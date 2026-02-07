use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

mod debugger;

const STACK_SIZE: u32 = 0x10000;
const STACK_TOP: u32 = 0x8000_0000;
const STACK_BASE: u32 = STACK_TOP - STACK_SIZE;

pub struct Emulator {
  regfile : [u32; 32],
  ram : HashMap<u32, u8>,
  mem_regions: Vec<MemoryRegion>,
  default_perm: MemPerm,
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

#[derive(Clone, Debug)]
// Source line marker emitted by the assembler debug pipeline.
struct DebugLine {
  file: String,
  line: u32,
  addr: u32,
}

#[derive(Clone, Debug)]
// Stack local debug metadata anchored to a code address.
struct DebugLocal {
  name: String,
  offset: i32,
  size: u32,
}

#[derive(Clone, Debug)]
// Global data symbol debug metadata.
struct DebugGlobal {
  name: String,
  addr: u32,
}

#[derive(Clone, Debug, Default)]
// Aggregated C debug info parsed from a .debug file.
struct DebugInfo {
  lines: Vec<DebugLine>,
  locals_by_addr: HashMap<u32, Vec<DebugLocal>>,
  globals: Vec<DebugGlobal>,
  missing_line_addrs: bool,
  missing_local_addrs: bool,
  missing_local_sizes: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
// Memory permissions derived from ELF p_flags (R=4, W=2, X=1).
struct MemPerm {
  read: bool,
  write: bool,
  exec: bool,
}

impl MemPerm {
  fn from_elf_flags(flags: u32) -> MemPerm {
    MemPerm {
      read: (flags & 4) != 0,
      write: (flags & 2) != 0,
      exec: (flags & 1) != 0,
    }
  }
}

const PERM_RWX: MemPerm = MemPerm {
  read: true,
  write: true,
  exec: true,
};

const PERM_RW: MemPerm = MemPerm {
  read: true,
  write: true,
  exec: false,
};

const PERM_NONE: MemPerm = MemPerm {
  read: false,
  write: false,
  exec: false,
};

#[derive(Clone, Debug)]
struct MemoryRegion {
  base: u32,
  size: u32,
  perm: MemPerm,
}

impl MemoryRegion {
  fn contains(&self, addr: u32) -> bool {
    let start = self.base as u64;
    let end = start + self.size as u64;
    let addr = addr as u64;
    addr >= start && addr < end
  }
}

#[derive(Clone)]
// Loader output: bytes + labels + entrypoint + region permissions.
struct ProgramImage {
  ram: HashMap<u32, u8>,
  labels: LabelMap,
  entry: u32,
  regions: Vec<MemoryRegion>,
  default_perm: MemPerm,
  debug: DebugInfo,
}

#[derive(Clone, Copy, Debug)]
enum MemAccess {
  Read,
  Write,
  Exec,
}

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

fn read_u16_le(bytes: &[u8], offset: usize) -> Option<u16> {
  if offset + 1 >= bytes.len() {
    return None;
  }
  Some(u16::from(bytes[offset]) | (u16::from(bytes[offset + 1]) << 8))
}

fn read_u32_le(bytes: &[u8], offset: usize) -> Option<u32> {
  if offset + 3 >= bytes.len() {
    return None;
  }
  Some(
    u32::from(bytes[offset])
      | (u32::from(bytes[offset + 1]) << 8)
      | (u32::from(bytes[offset + 2]) << 16)
      | (u32::from(bytes[offset + 3]) << 24),
  )
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

// Parse C debug metadata lines emitted by the assembler.
fn parse_debug_line(line: &str, debug: &mut DebugInfo) -> bool {
  const DEFAULT_LOCAL_SIZE_BYTES: u32 = 4;
  let mut parts = line.split_whitespace();
  match parts.next() {
    Some("#line") => {
      let Some(file) = parts.next() else {
        return true;
      };
      let Some(line_str) = parts.next() else {
        return true;
      };
      let line_num = match line_str.parse::<u32>() {
        Ok(value) => value,
        Err(_) => {
          debug.missing_line_addrs = true;
          return true;
        }
      };
      let addr = match parts.next().and_then(parse_hex_u32) {
        Some(value) => value,
        None => {
          debug.missing_line_addrs = true;
          return true;
        }
      };
      debug.lines.push(DebugLine {
        file: file.to_string(),
        line: line_num,
        addr,
      });
      true
    }
    Some("#local") => {
      let Some(name) = parts.next() else {
        return true;
      };
      let Some(offset_str) = parts.next() else {
        return true;
      };
      let offset = match offset_str.parse::<i32>() {
        Ok(value) => value,
        Err(_) => {
          debug.missing_local_addrs = true;
          return true;
        }
      };
      let remaining: Vec<&str> = parts.collect();
      let (size, addr_str) = match remaining.as_slice() {
        [] => {
          debug.missing_local_sizes = true;
          debug.missing_local_addrs = true;
          return true;
        }
        [addr_only] => {
          debug.missing_local_sizes = true;
          (DEFAULT_LOCAL_SIZE_BYTES, *addr_only)
        }
        [size_str, addr_str, ..] => {
          let mut size = match size_str.parse::<u32>() {
            Ok(value) if value > 0 => value,
            _ => {
              debug.missing_local_sizes = true;
              DEFAULT_LOCAL_SIZE_BYTES
            }
          };
          if size == 0 {
            debug.missing_local_sizes = true;
            size = DEFAULT_LOCAL_SIZE_BYTES;
          }
          (size, *addr_str)
        }
      };
      let addr = match parse_hex_u32(addr_str) {
        Some(value) => value,
        None => {
          debug.missing_local_addrs = true;
          return true;
        }
      };
      debug.locals_by_addr.entry(addr).or_default().push(DebugLocal {
        name: name.to_string(),
        offset,
        size,
      });
      true
    }
    Some("#data") => {
      let Some(name) = parts.next() else {
        return true;
      };
      let Some(addr_str) = parts.next() else {
        return true;
      };
      if let Some(addr) = parse_hex_u32(addr_str) {
        if !debug.globals.iter().any(|g| g.name == name && g.addr == addr) {
          debug.globals.push(DebugGlobal {
            name: name.to_string(),
            addr,
          });
        }
      }
      true
    }
    _ => false,
  }
}

// Load raw hex (with optional @ origins) or ELF text and collect labels.
fn load_program(path: &str) -> ProgramImage {
  let mut labels = LabelMap::new();
  let mut debug = DebugInfo::default();
  let lines = read_lines(path).expect("Couldn't open input file");
  let mut raw_lines = Vec::new();

  for line in lines.map_while(Result::ok) {
    if line.trim_start().starts_with('#') {
      let trimmed = line.trim();
      parse_label_line(trimmed, &mut labels);
      parse_debug_line(trimmed, &mut debug);
    }
    raw_lines.push(line);
  }

  let mut has_origin = false;
  for line in &raw_lines {
    let line = line.trim();
    if line.starts_with('@') {
      has_origin = true;
      break;
    }
  }

  if has_origin {
    let mut instructions = HashMap::new();
    let mut pc: u32 = 0;
    let mut entry: Option<u32> = None;

    for line in &raw_lines {
      let line = line.trim();
      if line.is_empty() {
        continue;
      }
      if line.starts_with('#') || line.starts_with(';') || line.starts_with("//") {
        continue;
      }
      if let Some(rest) = line.strip_prefix('@') {
        let addr_str = rest.trim();
        let addr = u32::from_str_radix(addr_str, 16).expect("Invalid address") * 4;
        pc = addr;
        continue;
      }

      let instruction = u32::from_str_radix(line, 16).expect("Error parsing hex file");
      if entry.is_none() {
        entry = Some(pc);
      }
      instructions.insert(pc, instruction as u8);
      instructions.insert(pc + 1, (instruction >> 8) as u8);
      instructions.insert(pc + 2, (instruction >> 16) as u8);
      instructions.insert(pc + 3, (instruction >> 24) as u8);

      pc += 4;
    }

    return ProgramImage {
      ram: instructions,
      labels,
      entry: entry.unwrap_or(0),
      regions: Vec::new(),
      default_perm: PERM_RWX,
      debug: debug.clone(),
    };
  }

  let mut words = Vec::new();
  for line in &raw_lines {
    let line = line.trim();
    if line.is_empty() {
      continue;
    }
    if line.starts_with('#') || line.starts_with(';') || line.starts_with("//") {
      continue;
    }
    if line.starts_with('@') {
      continue;
    }
    let word = u32::from_str_radix(line, 16).expect("Error parsing hex file");
    words.push(word);
  }

  if words.is_empty() {
    return ProgramImage {
      ram: HashMap::new(),
      labels,
      entry: 0,
      regions: Vec::new(),
      default_perm: PERM_NONE,
      debug: debug.clone(),
    };
  }

  if words[0] != 0x464C457F {
    // not an ELF file; load as raw hex file
    let mut instructions = HashMap::new();
    let mut pc: u32 = 0;
    for instruction in words {
      instructions.insert(pc, instruction as u8);
      instructions.insert(pc + 1, (instruction >> 8) as u8);
      instructions.insert(pc + 2, (instruction >> 16) as u8);
      instructions.insert(pc + 3, (instruction >> 24) as u8);
      pc += 4;
    }
    return ProgramImage {
      ram: instructions,
      labels,
      entry: 0,
      regions: Vec::new(),
      default_perm: PERM_RWX,
      debug: debug.clone(),
    };
  }

  // it is an ELF file; parse headers
  let mut bytes = Vec::with_capacity(words.len() * 4);
  for word in words {
    bytes.extend_from_slice(&word.to_le_bytes());
  }

  let entry = read_u32_le(&bytes, 24).expect("ELF header truncated");
  let phoff = read_u32_le(&bytes, 28).expect("ELF header truncated") as usize;
  let phentsize = read_u16_le(&bytes, 42).expect("ELF header truncated") as usize;
  let phnum = read_u16_le(&bytes, 44).expect("ELF header truncated") as usize;

  if phentsize < 32 {
    panic!("Unsupported ELF program header size {}", phentsize);
  }
  let pht_end = phoff + (phentsize * phnum);
  if pht_end > bytes.len() {
    panic!("ELF program header table is out of bounds");
  }

  let mut instructions = HashMap::new();
  let mut regions = Vec::new();
  for idx in 0..phnum {
    let base = phoff + (idx * phentsize);
    let p_type = read_u32_le(&bytes, base).expect("ELF program header truncated");
    if p_type != 1 {
      continue;
    }
    let p_offset = read_u32_le(&bytes, base + 4).expect("ELF program header truncated") as usize;
    let p_vaddr = read_u32_le(&bytes, base + 8).expect("ELF program header truncated");
    let p_filesz = read_u32_le(&bytes, base + 16).expect("ELF program header truncated");
    let p_memsz = read_u32_le(&bytes, base + 20).expect("ELF program header truncated");
    let p_flags = read_u32_le(&bytes, base + 24).expect("ELF program header truncated");

    if p_memsz < p_filesz {
      panic!("ELF program header has memsz < filesz");
    }
    let p_filesz_usize = p_filesz as usize;
    if p_offset + p_filesz_usize > bytes.len() {
      panic!("ELF segment is out of bounds");
    }
    for i in 0..p_filesz_usize {
      let addr = p_vaddr.wrapping_add(i as u32);
      instructions.insert(addr, bytes[p_offset + i]);
    }

    if p_memsz != 0 {
      regions.push(MemoryRegion {
        base: p_vaddr,
        size: p_memsz,
        perm: MemPerm::from_elf_flags(p_flags),
      });
    }
  }

  ProgramImage {
    ram: instructions,
    labels,
    entry,
    regions,
    default_perm: PERM_NONE,
    debug,
  }
}

impl Emulator {
  pub fn new(path : String) -> Emulator {
    let image = load_program(&path);
    Emulator::from_image(&image)
  }

  pub fn from_instructions(instructions: HashMap<u32, u8>) -> Emulator {
    Emulator::from_parts(instructions, 0, Vec::new(), PERM_RWX)
  }

  fn from_image(image: &ProgramImage) -> Emulator {
    Emulator::from_parts(
      image.ram.clone(),
      image.entry,
      image.regions.clone(),
      image.default_perm,
    )
  }

  fn from_parts(
    instructions: HashMap<u32, u8>,
    entry: u32,
    mut regions: Vec<MemoryRegion>,
    default_perm: MemPerm,
  ) -> Emulator {
    // Reserve a simple RW stack below the default user text base.
    regions.push(MemoryRegion {
      base: STACK_BASE,
      size: STACK_SIZE,
      perm: PERM_RW,
    });
    let mut regfile = [0u32; 32];
    regfile[31] = STACK_TOP;
    Emulator {
      regfile,
      ram: instructions,
      mem_regions: regions,
      default_perm,
      pc: entry,
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

  fn perm_for_addr(&self, addr: u32) -> MemPerm {
    for region in &self.mem_regions {
      if region.contains(addr) {
        return region.perm;
      }
    }
    self.default_perm
  }

  fn check_access(&self, addr: u32, access: MemAccess) {
    let perm = self.perm_for_addr(addr);
    let allowed = match access {
      MemAccess::Read => perm.read,
      MemAccess::Write => perm.write,
      MemAccess::Exec => perm.exec,
    };
    if !allowed {
      panic!("Memory {:?} access violation at {:08X}", access, addr);
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
    // Exec permission is checked per byte.
    for offset in 0..4 {
      self.check_access(addr.wrapping_add(offset), MemAccess::Exec);
    }
    self.read_debug32(addr)
  }

  // memory operations must be aligned
  fn mem_write8(&mut self, addr : u32, data : u8) {
    self.check_access(addr, MemAccess::Write);
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
    self.check_access(addr, MemAccess::Read);
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

  // Fetch/decode/execute loop; returns r1 when halted.
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

  // Dispatch instruction families by top-level opcode.
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
      22 => self.adpc(instr),
      
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

  fn adpc(&mut self, instr: u32) {
    // adpc rA, i
    // rA <- pc + 4 + sign-extended 22-bit immediate (pc-relative to next instruction).
    let r_a = (instr >> 22) & 0x1F;
    let imm = (instr & 0x3FFFFF) as i32;
    let imm = (imm << 10) >> 10; // sign-extend 22 bits
    let pc = self.pc as i32;
    let value = pc.wrapping_add(4).wrapping_add(imm) as u32;
    self.write_reg(r_a, value);
    self.pc += 4;
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

  // ALU operations share flag updates; 2nd operand is register or immediate.
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
          let r_b = 1 + u64::from(!r_b);
          u64::from(r_c) + r_b
        } else {
          let r_c = 1 + u64::from(!r_c);
          r_c+ u64::from(r_b)
        };

        // set the carry flag
        self.flags[0] = result >> 32 != 0;

        result as u32
      },
      17 => {
        // subb

        // two's complement
        let result = if imm {
          let r_b = 1 + u64::from(
          !(u32::wrapping_add(
          u32::from(!prev_carry), r_b)));
          u64::from(imm) + r_b
        } else {
          let r_c = 1 + u64::from(
          !(u32::wrapping_add(u32::from(!prev_carry), r_c)));
          r_c + u64::from(r_b)
        };

        // set the carry flag
        self.flags[0] = result >> 32 != 0;

        result as u32
      },
      18 => {
        // sxtb (sign extend byte)
        let byte = r_c & 0xFF;
        if (byte & 0x80) != 0 {
          byte | 0xFFFFFF00
        } else {
          byte
        }
      }
      19 => {
        // sxtd (sign extend double)
        let half = r_c & 0xFFFF;
        if (half & 0x8000) != 0 {
          half | 0xFFFF0000
        } else {
          half
        }
      }
      20 => {
        // tncb (truncate to byte)
        r_c & 0xFF
      }
      21 => {
        // tncd (truncate to double)
        r_c & 0xFFFF
      }
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

  // Memory addressing modes are split by absolute/relative/immediate forms.
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

  // Branch helpers: immediate PC-relative, absolute register, or relative register.
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
      self.pc = u32::wrapping_add(self.pc, u32::wrapping_add(4 , u32::wrapping_mul(imm, 4)));
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
