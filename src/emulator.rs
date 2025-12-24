use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

mod debugger;

pub struct Emulator {
  regfile : [u32; 32],
  ram : HashMap<u32, u8>,
  pc : u32,
  flags : [bool; 4], // flags are: carry | zero | sign | overflow
  halted : bool,
  watchpoints: Vec<Watchpoint>,
  watchpoint_hit: Option<WatchpointHit>,
}

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where P: AsRef<Path>, {
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

// Label -> address list (labels can appear multiple times across sections).
type LabelMap = HashMap<String, Vec<u32>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WatchKind {
  Read,
  Write,
  ReadWrite,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WatchAccess {
  Read,
  Write,
}

// Single-byte watchpoints tracked by exact address.
#[derive(Clone, Copy, Debug)]
struct Watchpoint {
  addr: u32,
  kind: WatchKind,
}

#[derive(Clone, Copy, Debug)]
struct WatchpointHit {
  addr: u32,
  access: WatchAccess,
  value: u8,
}

fn parse_hex_u32(token: &str) -> Option<u32> {
  let s = token.trim();
  let s = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")).unwrap_or(s);
  if s.is_empty() {
    return None;
  }
  u32::from_str_radix(s, 16).ok()
}

fn add_label(labels: &mut LabelMap, name: &str, addr: u32) {
  let entry = labels.entry(name.to_string()).or_default();
  if !entry.contains(&addr) {
    entry.push(addr);
  }
}

// Parse assembler debug label lines: "#label <name> <addr>".
fn parse_label_line(line: &str, labels: &mut LabelMap) -> bool {
  let mut parts = line.split_whitespace();
  match parts.next() {
    Some("#label") => {
      if let (Some(name), Some(addr_str)) = (parts.next(), parts.next()) {
        if let Some(addr) = parse_hex_u32(addr_str) {
          add_label(labels, name, addr);
          return true;
        }
      }
    }
    _ => {}
  }
  false
}

// Load hex (or .debug) program and collect any embedded labels.
fn load_program(path: &str) -> (HashMap<u32, u8>, LabelMap) {
  let mut instructions = HashMap::new();
  let mut labels = LabelMap::new();

  let lines = read_lines(path).expect("Couldn't open input file");
  let mut pc: u32 = 0;
  for line in lines.map_while(Result::ok) {
    let line = line.trim();
    if line.is_empty() {
      continue;
    }

    if line.starts_with('#') {
      // Debug label lines are prefixed with '#'.
      parse_label_line(line, &mut labels);
      continue;
    }
    if line.starts_with(';') || line.starts_with("//") {
      continue;
    }

    if let Some(rest) = line.strip_prefix('@') {
      let addr_str = rest.trim();
      let addr = u32::from_str_radix(addr_str, 16).expect("Invalid address") * 4;
      pc = addr;
      continue;
    }

    let instruction = u32::from_str_radix(line, 16).expect("Error parsing hex file");

    instructions.insert(pc, instruction as u8);
    instructions.insert(pc + 1, (instruction >> 8) as u8);
    instructions.insert(pc + 2, (instruction >> 16) as u8);
    instructions.insert(pc + 3, (instruction >> 24) as u8);

    pc += 4;
  }

  (instructions, labels)
}

impl Emulator {
  pub fn new(path : String) -> Emulator {
    let (instructions, _labels) = load_program(&path);
    Emulator::from_instructions(instructions)
  }

  pub fn from_instructions(instructions: HashMap<u32, u8>) -> Emulator {
    Emulator {
      regfile: [0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0],
      ram: instructions,
      pc: 0,
      flags: [false, false, false, false],
      halted: false,
      watchpoints: Vec::new(),
      watchpoint_hit: None,
    }
  }

  // Record the first watchpoint hit so the debugger can stop after stepping.
  fn maybe_watch(&mut self, addr: u32, access: WatchAccess, value: u8) {
    if self.watchpoint_hit.is_some() || self.watchpoints.is_empty() {
      return;
    }
    for wp in &self.watchpoints {
      if wp.addr == addr {
        let matches = match (wp.kind, access) {
          (WatchKind::Read, WatchAccess::Read) => true,
          (WatchKind::Write, WatchAccess::Write) => true,
          (WatchKind::ReadWrite, _) => true,
          _ => false,
        };
        if matches {
          self.watchpoint_hit = Some(WatchpointHit { addr, access, value });
          break;
        }
      }
    }
  }

  // Debug reads bypass watchpoints so inspection doesn't change execution flow.
  fn read_debug8(&self, addr: u32) -> u8 {
    *self.ram.get(&addr).unwrap_or(&0)
  }

  fn read_debug16(&self, addr: u32) -> u16 {
    if (addr & 1) != 0 {
      println!("Warning: unaligned memory access at {:08x}", addr);
    }
    (u16::from(self.read_debug8((addr & 0xFFFFFFFE) + 1)) << 8) +
    u16::from(self.read_debug8(addr & 0xFFFFFFFE))
  }

  fn read_debug32(&self, addr: u32) -> u32 {
    if (addr & 3) != 0 {
      println!("Warning: unaligned memory access at {:08x}", addr);
    }
    (u32::from(self.read_debug16((addr & 0xFFFFFFFC) + 2)) << 16) +
    u32::from(self.read_debug16(addr & 0xFFFFFFFC))
  }

  // Instruction fetch uses debug reads to avoid triggering watchpoints.
  fn fetch32(&self, addr: u32) -> u32 {
    self.read_debug32(addr)
  }

  // memory operations must be aligned
  fn mem_write8(&mut self, addr : u32, data : u8) {
    self.maybe_watch(addr, WatchAccess::Write, data);
    self.ram.insert(addr, data);
  }

  fn mem_write16(&mut self, addr : u32, data : u16) {
    if (addr & 1) != 0 {
      // unaligned access
      println!("Warning: unaligned memory access at {:08x}", addr);
    }
    self.mem_write8(addr & 0xFFFFFFFE, data as u8);
    self.mem_write8((addr & 0xFFFFFFFE) + 1, (data >> 8) as u8);
  }

  fn mem_write32(&mut self, addr : u32, data : u32) {
    if (addr & 3) != 0 {
      // unaligned access
      println!("Warning: unaligned memory access at {:08x}", addr);
    }
    self.mem_write16(addr & 0xFFFFFFFC, data as u16);
    self.mem_write16((addr & 0xFFFFFFFC) + 2, (data >> 16) as u16);
  }

  fn mem_read8(&mut self, addr : u32) -> u8 {
    let value = if self.ram.contains_key(&addr) {
      self.ram[&addr]
    } else {
      0
    };
    self.maybe_watch(addr, WatchAccess::Read, value);
    value
  }

  fn mem_read16(&mut self, addr : u32) -> u16 {
    if (addr & 1) != 0 {
      // unaligned access
      println!("Warning: unaligned memory access at {:08x}", addr);
    }
    (u16::from(self.mem_read8((addr & 0xFFFFFFFE) + 1)) << 8) + 
    u16::from(self.mem_read8(addr & 0xFFFFFFFE))
  }

  fn mem_read32(&mut self, addr : u32) -> u32 {
    if (addr & 3) != 0 {
      // unaligned access
      println!("Warning: unaligned memory access at {:08x}", addr);
    }
    (u32::from(self.mem_read16((addr & 0xFFFFFFFC) + 2)) << 16) +
    u32::from(self.mem_read16(addr & 0xFFFFFFFC))
  }

  pub fn run(&mut self, max_iters: u32) -> Option<u32> {
    let mut cycles: u32 = 0;
    while !self.halted {
      assert!(self.pc % 4 == 0, "PC is not aligned");
      self.execute(self.fetch32(self.pc));
      cycles = cycles.wrapping_add(1);
      if max_iters != 0 && cycles > max_iters {
        return None;
      }
    }

    // return the value in r3
    Some(self.regfile[1])
  }

  fn execute(&mut self, instr : u32) {
    let opcode = instr >> 27; // opcode is top 5 bits of instruction

    match opcode {
      0 => self.alu_op(instr, false),
      1 => self.alu_op(instr, true),
      2 => self.load_upper_immediate(instr),

      // 32 bit mem instructions
      3 => self.mem_absolute(instr, 2),
      4 => self.mem_relative(instr, 2),
      5 => self.mem_imm(instr, 2),

      // 16 bit mem instructions
      6 => self.mem_absolute(instr, 1),
      7 => self.mem_relative(instr, 1),
      8 => self.mem_imm(instr, 1),

      // 8 bit mem instructions
      9 => self.mem_absolute(instr, 0),
      10 => self.mem_relative(instr, 0),
      11 => self.mem_imm(instr, 0),

      12 => self.branch_imm(instr),
      13 => self.branch_absolute(instr),
      14 => self.branch_relative(instr),
      15 => self.syscall(instr),
      
      // fadd
      16 => self.atomic_absolute(instr, 0),
      17 => self.atomic_relative(instr, 0),
      18 => self.atomic_imm(instr, 0),

      // swap
      19 => self.atomic_absolute(instr, 1),
      20 => self.atomic_relative(instr, 1),
      21 => self.atomic_imm(instr, 1),
      _ => panic!("Unrecognized opcode")
    }
  }

  fn get_reg(&self, regnum : u32) -> u32 {
    self.regfile[regnum as usize]
  }

  fn write_reg(&mut self, regnum : u32, value : u32) {
    // normal register access
    if regnum != 0 {
      // r0 is always zero
      self.regfile[regnum as usize] = value;
    }
  }

  fn decode_alu_imm(op : u32, imm : u32) -> u32 {
    match op {
      0..=6 => {
        // Bitwise op
        (imm & 0xFF) << (8 * ((imm >> 8) & 3)) // zero extend and shift
      },
      7..=13 => {
        // Shift op
        imm & 0x1F // zero extend
      },
      14..=18 => {
        // Arithmetic op
        imm | (0xFFFFF000 * ((imm >> 11) & 1)) // sign extend
      },
      _ => panic!("Unrecognized ALU operation")
    }
  }

  // 2nd operand is either register or immediate
  fn alu_op(&mut self, instr : u32, imm : bool) {
    // instruction format is
    // 00000aaaaabbbbbxxxxxxx?????ccccc
    // op (5 bits) | r_a (5 bits) | r_b (5 bits) | unused (7 bits) | op (5 bits) | r_c (5 bits)
    let r_a = (instr >> 22) & 0x1F;
    let r_b = (instr >> 17) & 0x1F;
    let op = if imm {
      (instr >> 12) & 0x1F
    } else {
      (instr >> 5) & 0x1F
    };

    // retrieve arguments
    let r_b = self.get_reg(r_b);

    let r_c = if imm {
      Self::decode_alu_imm(op, instr & 0xFFF)
    } else {
      let r_c = instr & 0x1F;
      self.get_reg(r_c)
    };

    let prev_carry = self.flags[0];

    self.flags[0] = false; // clear arithmetic flags

    // carry flag is set differently for each instruction,
    // so its handled here. The other flags are all handled together
    let result = match op {
      0 => {
        r_b & r_c // and
      }, 
      1 => {
        !(r_b & r_c)  // nand
      },
      2 => {
        r_b | r_c // or
      },
      3 => {
        !(r_b | r_c) // nor
      },
      4 => {
        r_b ^ r_c // xor
      },
      5 => {
        !(r_b ^ r_c) // xnor
      },
      6 => {
        !r_c // not
      },
      7 => {
        // set carry flag
        self.flags[0] = r_b >> if r_c > 0 {32 - r_c} else {0} != 0;
        r_b << r_c // lsl
      },
      8 => {
        // set carry flag
        self.flags[0] = r_b & ((1 << r_c) - 1) != 0;
        r_b >> r_c // lsr
      },
      9 => {
        // set carry flag
        let carry = r_b & 1;
        let sign = r_b >> 31;
        self.flags[0] = carry != 0;
        (r_b >> r_c) | (0xFFFFFFFF * sign << if r_c > 0 {32 - r_c} else {0}) // asr
      },
      10 => {
        // set carry flag
        let carry = r_b >> if r_c > 0 {32 - r_c} else {0};
        self.flags[0] = carry != 0;
        (r_b << r_c) | carry // rotl
      },
      11 => {
        // set carry flag
        let carry = r_b & ((1 << r_c) - 1);
        self.flags[0] = carry != 0;
        (r_b >> r_c) | (carry << if r_c > 0 {32 - r_c} else {0}) // rotr
      },
      12 => {
        // set carry flag
        let carry = if r_c > 0 {r_b >> (32 - r_c)} else {0};
        self.flags[0] = carry != 0;
        (r_b << r_c) | if r_c > 0 {(prev_carry as u32) << (r_c - 1)} else {0} // lslc
      },
      13 => {
        // set carry flag
        let carry = r_b & ((1 << r_c) - 1);
        self.flags[0] = carry != 0;
        (r_b >> r_c) | ((prev_carry as u32) << if r_c > 0 {32 - r_c} else {0}) // lsrc
      },
      14 => {
        // add
        let result = u64::from(r_b) + u64::from(r_c);

        // set the carry flag
        self.flags[0] = result >> 32 != 0;

        result as u32
      },
      15 => {
        // addc
        let result = u64::from(r_c) + u64::from(r_b) + u64::from(prev_carry);

        // set the carry flag
        self.flags[0] = result >> 32 != 0;

        result as u32
      },
      16 => {
        // sub

        // two's complement
        // sub with immediate does imm - reg
        let result = if imm {
          let r_b = (1 + u64::from(!r_b)) as u32;
          u64::from(r_c) + u64::from(r_b)
        } else {
          let r_c = (1 + u64::from(!r_c)) as u32;
          u64::from(r_c) + u64::from(r_b)
        };

        // set the carry flag
        self.flags[0] = result >> 32 != 0;

        result as u32
      },
      17 => {
        // subb

        // two's complement
        let result = if imm {
          let r_b = (1 + u64::from(
          !(u32::wrapping_add(
          u32::from(!prev_carry), r_b)))) as u32;
          u64::from(imm) + u64::from(r_b)
        } else {
          let r_c = (1 + u64::from(
          !(u32::wrapping_add(u32::from(!prev_carry), r_c)))
          ) as u32;
          u64::from(r_c) + u64::from(r_b)
        };

        // set the carry flag
        self.flags[0] = result >> 32 != 0;

        result as u32
      },
      _ => {
        panic!("Unrecognized ALU operation");
      }
    };

    // never update r0
    self.write_reg(r_a, result);
    
    self.update_flags(result, r_b, r_c, op);

    self.pc += 4;

  }

  fn load_upper_immediate(&mut self, instr : u32){
    // store imm << 10 in r_a
    let r_a = (instr >> 22) & 0x1F;
    let imm = (instr & 0x03FFFFF) << 10;

    self.write_reg(r_a, imm);

    self.pc += 4;
  }

  fn mem_absolute(&mut self, instr : u32, size : u8){
    // instruction format is
    // 00011aaaaabbbbb?yyzziiiiiiiiiiii
    // op (5 bits) | r_a (5 bits) | r_b (5 bits) | op (1 bit) | y (2 bits) | z (2 bits) | imm (12 bits)

    let r_a = (instr >> 22) & 0x1F;
    let r_b = (instr >> 17) & 0x1F;
    let is_load = ((instr >> 16) & 1) != 0; // is this a load? else is store
    let y = (instr >> 14) & 3; // offset type: 0 = signed offset, 1 = preinc, 2 = postinc, 3 = reserved
    let z = (instr >> 12) & 3; // shift amount
    let imm = instr & 0xFFF;

    // sign extend imm
    let imm = imm | (0xFFFFF000 * ((imm >> 11) & 1));
    // shift imm
    let imm = imm << z;

    if y >= 4 {
      panic!("Invalid memory addressing mode");
    };

    // get addr
    let r_b_out = self.get_reg(r_b);
    let addr = if y == 2 {r_b_out} else {u32::wrapping_add(r_b_out, imm)}; // check for postincrement

    if is_load {
      let data = match size {
        0 => {
          // byte
          u32::from(self.mem_read8(addr))
        },
        1 => {
          // halfword
          u32::from(self.mem_read16(addr))
        },
        2 => {
          // word
          self.mem_read32(addr)
        },
        _ => {
          panic!("invalid size for mem instruction");
        }
      };

      self.write_reg(r_a, data);
    } else {
      // is a store
      let data = self.get_reg(r_a);
      match size {
        0 => {
          // byte
          self.mem_write8(addr, data as u8)
        },
        1 => {
          // halfword
          self.mem_write16(addr, data as u16)
        },
        2 => {
          // word
          self.mem_write32(addr, data)
        },
        _ => {
          panic!("invalid size for mem instruction");
        }
      };
    }

    if y == 1 || y == 2 {
      // pre or post increment
      self.write_reg(r_b, u32::wrapping_add(r_b_out, imm));
    }

    self.pc += 4;
  }

  fn mem_relative(&mut self, instr : u32, size : u8){
    // instruction format is
    // 00100aaaaabbbbb?iiiiiiiiiiiiiiii
    // op (5 bits) | r_a (5 bits) | r_b (5 bits) | op (1 bit) | imm (16 bits)

    let r_a = (instr >> 22) & 0x1F;
    let r_b = (instr >> 17) & 0x1F;
    let is_load = ((instr >> 16) & 1) != 0; // is this a load? else is store
    let imm = instr & 0xFFFF;

    // sign extend imm
    let imm = imm | (0xFFFF0000 * ((imm >> 15) & 1));

    // get addr
    let r_b_out = self.get_reg(r_b);
    let addr = u32::wrapping_add(r_b_out, imm);

    // make addr pc-relative
    let addr = u32::wrapping_add(addr, self.pc);
    let addr = u32::wrapping_add(addr, 4);

    if is_load {
      let data = match size {
        0 => {
          // byte
          u32::from(self.mem_read8(addr))
        },
        1 => {
          // halfword
          u32::from(self.mem_read16(addr))
        },
        2 => {
          // word
          self.mem_read32(addr)
        },
        _ => {
          panic!("invalid size for mem instruction");
        }
      };

      self.write_reg(r_a, data);
    } else {
      // is a store
      let data = self.get_reg(r_a);

      match size {
        0 => {
          // byte
          self.mem_write8(addr, data as u8)
        },
        1 => {
          // halfword
          self.mem_write16(addr, data as u16)
        },
        2 => {
          // word
          self.mem_write32(addr, data)
        },
        _ => {
          panic!("invalid size for mem instruction");
        }
      };
    }

    self.pc += 4;
  }

  fn mem_imm(&mut self, instr : u32, size : u8){
    // instruction format is
    // 00101aaaaa?iiiiiiiiiiiiiiiiiiiii
    // op (5 bits) | r_a (5 bits) | op (1 bit) | imm (21 bits)

    let r_a = (instr >> 22) & 0x1F;
    let is_load = ((instr >> 21) & 1) != 0; // is this a load? else is store
    let imm = instr & 0x1FFFFF;

    // sign extend imm
    let imm = imm | (0xFFE00000 * ((imm >> 20) & 1));

    // get addr
    let addr = u32::wrapping_add(imm, self.pc);
    let addr = u32::wrapping_add(addr, 4);

    if is_load {
      let data = match size {
        0 => {
          // byte
          u32::from(self.mem_read8(addr))
        },
        1 => {
          // halfword
          u32::from(self.mem_read16(addr))
        },
        2 => {
          // word
          self.mem_read32(addr)
        },
        _ => {
          panic!("invalid size for mem instruction");
        }
      };

      self.write_reg(r_a, data);
    } else {
      // is a store
      let data = self.get_reg(r_a);

      match size {
        0 => {
          // byte
          self.mem_write8(addr, data as u8)
        },
        1 => {
          // halfword
          self.mem_write16(addr, data as u16)
        },
        2 => {
          // word
          self.mem_write32(addr, data)
        },
        _ => {
          panic!("invalid size for mem instruction");
        }
      };
    }

    self.pc += 4;
  }

  fn atomic_absolute(&mut self, instr : u32, type_ : u8){
    // instruction format is
    // 10000aaaaabbbbbccccciiiiiiiiiiii - fadd
    // opcode is 10011 for swap
    // op (5 bits) | r_a (5 bits) | r_c (5 bits) | r_b (5 bits) | imm (12 bits)

    let r_a = (instr >> 22) & 0x1F;
    let r_c = (instr >> 17) & 0x1F;
    let r_b = (instr >> 12) & 0x1F;
    let imm = instr & 0xFFF;

    // sign extend imm
    let imm = imm | (0xFFFFF000 * ((imm >> 11) & 1));

    // get addr
    let r_b_out = self.get_reg(r_b);
    let r_c_out = self.get_reg(r_c);
    let addr = u32::wrapping_add(r_b_out, imm);

    let data = self.mem_read32(addr);
    self.write_reg(r_a, data);

    match type_ {
      0 => {
        // fadd
        self.mem_write32(addr, u32::wrapping_add(r_c_out, data));
      }
      1 => {
        // swap
        self.mem_write32(addr, r_c_out);
      }
      _ => panic!("invalid atomic type"),
    };

    self.pc += 4;
  }

  fn atomic_relative(&mut self, instr : u32, type_ : u8){
    // instruction format is
    // 10001aaaaabbbbbccccciiiiiiiiiiii
    // or opcode is 10100
    // op (5 bits) | r_a (5 bits) | r_c (5 bits) | r_b (5 bits) | imm (12 bits)

    let r_a = (instr >> 22) & 0x1F;
    let r_c = (instr >> 17) & 0x1F;
    let r_b = (instr >> 12) & 0x1F;
    let imm = instr & 0xFFF;

    // sign extend imm
    let imm = imm | (0xFFFFF000 * ((imm >> 11) & 1));

    // get addr
    let r_b_out = self.get_reg(r_b);
    let r_c_out = self.get_reg(r_c);
    let addr = u32::wrapping_add(r_b_out, imm);

    // make addr pc-relative
    let addr = u32::wrapping_add(addr, self.pc);
    let addr = u32::wrapping_add(addr, 4);

    let data = self.mem_read32(addr);
    self.write_reg(r_a, data);

    match type_ {
      0 => {
        // fadd
        self.mem_write32(addr, u32::wrapping_add(r_c_out, data));
      }
      1 => {
        // swap
        self.mem_write32(addr, r_c_out);
      }
      _ => panic!("invalid atomic type"),
    };

    self.pc += 4;
  }

  fn atomic_imm(&mut self, instr : u32, type_ : u8){
    // instruction format is
    // 10010aaaaabbbbbiiiiiiiiiiiiiiiii
    // or opcode is 10101
    // op (5 bits) | r_a (5 bits) | r_b (5 bits) | imm (17 bits)

    let r_a = (instr >> 22) & 0x1F;
    let r_c = (instr >> 17) & 0x1F;
    let imm = instr & 0x1FFFF;

    // sign extend imm
    let imm = imm | (0xFFFE0000 * ((imm >> 16) & 1));

    // get addr
    let r_c_out = self.get_reg(r_c);

    // make addr pc-relative
    let addr = u32::wrapping_add(imm, self.pc);
    let addr = u32::wrapping_add(addr, 4);

    let data = self.mem_read32(addr);
    self.write_reg(r_a, data);

    match type_ {
      0 => {
        // fadd
        self.mem_write32(addr, u32::wrapping_add(r_c_out, data));
      }
      1 => {
        // swap
        self.mem_write32(addr, r_c_out);
      }
      _ => panic!("invalid atomic type"),
    };

    self.pc += 4;
  }

  fn get_branch_condition(&self, op: u32) -> bool {
    let carry = self.flags[0];
    let zero = self.flags[1];
    let sign = self.flags[2];
    let overflow = self.flags[3];

    match op {
      0 => true, // br
      1 => zero, // bz
      2 => !zero, // bnz
      3 => sign, // bs
      4 => !sign, // bns
      5 => carry, // bc
      6 => !carry, // bnc
      7 => overflow, // bo
      8 => !overflow, // bno
      9 => !zero && !sign, // bps
      10 => zero || sign, // bnps
      11 => sign == overflow && !zero, // bg
      12 => sign == overflow, // bge
      13 => sign != overflow && !zero, // bl
      14 => sign != overflow || zero, // ble
      15 => !zero && carry, // ba
      16 => carry || zero, // bae
      17 => !carry && !zero, // bb
      18 => !carry || zero, // bbe
      _ => {
        panic!("Unrecognized branch instruction");
      }
    }
  }

  fn branch_imm(&mut self, instr : u32){
    // instruction format is
    // 01100?????iiiiiiiiiiiiiiiiiiiiii
    // op (5 bits) | op (5 bits) | imm (22 bits)
    let op = (instr >> 22) & 0x1F;
    let imm = instr & 0x3FFFFF;

    // sign extend
    let imm = imm | (0xFFC00000 * ((imm >> 21) & 1));

    let branch = self.get_branch_condition(op);

    if branch {
      self.pc = u32::wrapping_add(self.pc, u32::wrapping_add(4 , imm));
    } else {
      self.pc += 4;
    }

  }

  fn branch_absolute(&mut self, instr : u32){
    // instruction format is
    // 01101?????xxxxxxxxxxxxaaaaabbbbb
    // op (5 bits) | op (5 bits) | unused (12 bits) | r_a (5 bits) | r_b (5 bits)
    let op = (instr >> 22) & 0x1F;
    let r_a = (instr >> 5) & 0x1F;
    let r_b = instr & 0x1F;

    // get address
    let r_b = self.get_reg(r_b);

    let branch = self.get_branch_condition(op);

    if branch {
      self.write_reg(r_a, self.pc + 4);
      self.pc = r_b;
    } else {
      self.pc += 4;
    }
  }

  fn branch_relative(&mut self, instr : u32){
    // instruction format is
    // 01110?????xxxxxxxxxxxxaaaaabbbbb
    // op (5 bits) | op (5 bits) | unused (12 bits) | r_a (5 bits) | r_b (5 bits)
    let op = (instr >> 22) & 0x1F;
    let r_a = (instr >> 5) & 0x1F;
    let r_b = instr & 0x1F;

    // get address
    let r_b = self.get_reg(r_b);

    let branch = self.get_branch_condition(op);

    if branch {
      self.write_reg(r_a, self.pc + 4);
      self.pc = u32::wrapping_add(self.pc, u32::wrapping_add(4, r_b));
    } else {
      self.pc += 4;
    }
  }

  fn syscall(&mut self, instr : u32){
    let imm = instr & 0xFF;

    match imm {
      1 => {
        // sys EXIT
        self.halted = true;
      }
      _ => panic!("Unrecognized syscall")
    }
  }

  // carry flag handled separately in each alu operation
  fn update_flags(&mut self, result : u32, lhs : u32, rhs : u32, op : u32) {
    let result_sign = result >> 31;
    let lhs_sign = lhs >> 31;
    let rhs_sign = rhs >> 31;

    let is_sub = op == 16 || op == 17;

    // set the zero flag
    self.flags[1] = result == 0;
    // set the sign flag
    self.flags[2] = result_sign != 0;
    // set the overflow flag
    self.flags[3] = if is_sub {
      (result_sign != lhs_sign) && (lhs_sign != rhs_sign)
    } else {
      (result_sign != lhs_sign) && (lhs_sign == rhs_sign)
    }
  }

}
