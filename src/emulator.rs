use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

pub struct Emulator {
  regfile : [u32; 32],
  ram : HashMap<u32, u8>,
  pc : u32,
  flags : [bool; 4], // flags are: carry | zero | sign | overflow
  halted : bool
}

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where P: AsRef<Path>, {
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

impl Emulator {
  pub fn new(path : String) -> Emulator {

    let mut instructions = HashMap::new();
    
    // read in binary file
    let lines = read_lines(path).expect("Couldn't open input file");
    // Consumes the iterator, returns an (Optional) String
    let mut pc : u32 = 0;
    for line in lines.map_while(Result::ok) {
      // read one instruction
      let instruction = u32::from_str_radix(&line, 16).expect("Error parsing hex file");

      // write one instruction
      instructions.insert(pc, instruction as u8);
      instructions.insert(pc + 1, (instruction >> 8) as u8);
      instructions.insert(pc + 2, (instruction >> 16) as u8);
      instructions.insert(pc + 3, (instruction >> 24) as u8);

      pc += 4;
    }
    

    Emulator {
      regfile: [0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0],
      ram: instructions,
      pc: 0,
      flags: [false, false, false, false],
      halted: false
    }
  }

  fn mem_write8(&mut self, addr : u32, data : u8) {
    self.ram.insert(addr, data);
  }

  fn mem_write16(&mut self, addr : u32, data : u16) {
    self.mem_write8(addr, data as u8);
    self.mem_write8(addr + 1, (data >> 8) as u8);
  }

  fn mem_write32(&mut self, addr : u32, data : u32) {
    self.mem_write16(addr, data as u16);
    self.mem_write16(addr + 2, (data >> 16) as u16);
  }

  fn mem_read8(&self, addr : u32) -> u8 {
    if self.ram.contains_key(&addr) {
      self.ram[&addr]
    } else {
      0
    }
  }

  fn mem_read16(&self, addr : u32) -> u16 {
    (u16::from(self.mem_read8(addr + 1)) << 8) + 
    u16::from(self.mem_read8(addr))
  }

  fn mem_read32(&self, addr : u32) -> u32 {
    (u32::from(self.mem_read16(addr + 2)) << 16) + 
    u32::from(self.mem_read16(addr))
  }

  pub fn run(&mut self) -> u32 {
    while !self.halted {
      self.execute(self.mem_read32(self.pc));
    }

    // return the value in r3
    self.regfile[3]
  }

  fn execute(&mut self, instr : u32) {
    let opcode = instr >> 27; // opcode is top 5 bits of instruction

    //match opcode {
    //  0 => self.alu_op(args),
    //  1 => self.add_immediate(args),
    //  2 => panic!("Invalid opcode"),
    //  3 => self.load_upper_immediate(args),
    //  4 => self.store_word(args),
    //  5 => self.load_word(args),
    //  6 => self.branch(args),
    //  7 => self.jalr_or_exc(args),
    //  _ => panic!("instr >> 13 should always be < 8")
    //}
  }
//
  //fn alu_op(&mut self, args : u32) {
  //  // instruction format is
  //  // r_a (3 bits) | r_b (3 bits) | op (4 bits) | r_c (3 bits)
  //  let r_a = args >> 10;
  //  let r_b = (args >> 7) & 0b111;
  //  let op = (args >> 3) & 0b1111;
  //  let r_c = args & 0b111;
//
  //  // retrieve arguments
  //  let mut r_b = self.regfile[usize::from(r_b)];
  //  let r_c = self.regfile[usize::from(r_c)];
//
  //  // carry flag is set differently for each instruction,
  //  // so its handled here. The other flags are all handled together
  //  let result = match op {
  //    0 => {
  //      self.flags[0] = false;
  //      !(r_b & r_c)  // nand
  //    },
  //    1 => {
  //      // add
  //      let result = u32::from(r_b) + u32::from(r_c);
//
  //      // set the carry flag
  //      self.flags[0] = if result >> 16 != 0 {true} else {false};
//
  //      result as u16
  //    },
  //    2 => {
  //      // addc
  //      let result = u32::from(r_c) + u32::from(r_b) + u32::from(self.flags[0]);
//
  //      // set the carry flag
  //      self.flags[0] = if result >> 16 != 0 {true} else {false};
//
  //      result as u16
  //    },
  //    3 => {
  //      self.flags[0] = false;
  //      r_b | r_c // or
  //    },
  //    4 => {
  //      // subc
//
  //      // two's complement
  //      r_b = (1 + u32::from(
  //        !(u16::wrapping_add(
  //        u16::from(!self.flags[0]), r_b)))) as u16;
  //      let result = u32::from(r_c) + u32::from(r_b);
//
  //      // set the carry flag
  //      self.flags[0] = if result >> 16 != 0 {true} else {false};
//
  //      result as u16
  //    },
  //    5 => {
  //      self.flags[0] = false;
  //      r_b & r_c // and
  //    }, 
  //    6 => {
  //      // sub, cmp
//
  //      // two's complement
  //      r_b = (1 + u32::from(!r_b)) as u16;
  //      let result = u32::from(r_c) + u32::from(r_b);
//
  //      // set the carry flag
  //      self.flags[0] = if result >> 16 != 0 {true} else {false};
//
  //      result as u16
  //    },
  //    7 => {
  //      self.flags[0] = false;
  //      r_b ^ r_c // xor
  //    },
  //    8 => {
  //      self.flags[0] = false;
  //      !r_c // not
  //    },
  //    9 => {
  //      // set carry flag
  //      self.flags[0] = if r_c >> 15 != 0 {true} else {false};
  //      r_c << 1 // shl
  //    },
  //    10 => {
  //      // set carry flag
  //      self.flags[0] = if r_c & 1 != 0 {true} else {false};
  //      r_c >> 1 // shr
  //    },
  //    11 => {
  //      // set carry flag
  //      let carry = r_c >> 15;
  //      self.flags[0] = if carry != 0 {true} else {false};
  //      (r_c << 1) + carry // rotl
  //    },
  //    12 => {
  //      // set carry flag
  //      let carry = r_c & 1;
  //      self.flags[0] = if carry != 0 {true} else {false};
  //      (r_c >> 1) + (carry << 15) // rotr
  //    },
  //    13 => {
  //      // set carry flag
  //      let carry = r_c & 1;
  //      let sign = r_c >> 15;
  //      self.flags[0] = if carry != 0 {true} else {false};
  //      (r_c >> 1) + (sign << 15) // sshr
  //    },
  //    14 => {
  //      // set carry flag
  //      let carry = r_c & 15;
  //      let old_carry = u16::from(self.flags[0]);
  //      self.flags[0] = if carry != 0 {true} else {false};
  //      (r_c >> 1) + (old_carry << 15) // shrc
  //    },
  //    15 => {
  //      // set carry flag
  //      let carry = r_c >> 15;
  //      let old_carry = u16::from(self.flags[0]);
  //      self.flags[0] = if carry != 0 {true} else {false};
  //      (r_c << 1) + old_carry // shlc
  //    },
  //    _ => panic!("args & 15 should always be < 16")
  //  };
//
  //  // never update r0
  //  if r_a != 0 {
  //    self.regfile[usize::from(r_a)] = result as u16;
  //  }
  //  
  //  self.update_flags(result, r_b, r_c);
//
  //  self.pc += 1;
  //}
//
  //fn add_immediate(&mut self, args : u32) {
  //  // add the value in r_b to imm, store result in r_b
  //  let r_a = args >> 10;
  //  let r_b = (args >> 7) & 0b111;
  //  let imm = Self::sign_ext_7(args & 0x7F);
  //  let r_b = self.regfile[usize::from(r_b)];
//
  //  // convert to u32 so we can update the carry flag
  //  let result = u32::from(r_b) + u32::from(imm);
//
  //  if r_a != 0 {
  //    self.regfile[usize::from(r_a)] = result as u16;
  //  }
//
  //  // set the carry flag
  //  self.flags[0] = if result >> 16 != 0 {true} else {false};
//
  //  // update the other flags
  //  self.update_flags(result as u16, r_b, imm);
//
  //  self.pc += 1;
//
  //}
//
  //fn load_upper_immediate(&mut self, args : u32){
  //  // store imm << 6 in r_a
  //  let r_a = args >> 10;
  //  let imm = (args & 0x03FF) << 6;
//
  //  if r_a != 0 {
  //    self.regfile[usize::from(r_a)] = imm;
  //  }
//
  //  self.pc += 1;
  //}
//
  //fn store_word(&mut self, args : u32) {
  //  // store the value in r_a at address r_b + imm
  //  let r_a = args >> 10;
  //  let r_b = (args >> 7) & 0b111;
  //  let imm = Self::sign_ext_7(args & 0x7F);
//
  //  let address = u16::wrapping_add(self.regfile[usize::from(r_b)], imm);
  //  self.ram[usize::from(address)] = self.regfile[usize::from(r_a)];
//
  //  self.pc += 1;
  //}
//
  //fn load_word(&mut self, args : u32) {
  //  // load the value at address r_b + imm into r_a
  //  let r_a = args >> 10;
  //  let r_b = (args >> 7) & 0b111;
  //  let imm = Self::sign_ext_7(args & 0x7F);
//
  //  let address = u16::wrapping_add(self.regfile[usize::from(r_b)], imm);
//
  //  if r_a != 0 {
  //    self.regfile[usize::from(r_a)] = self.ram[usize::from(address)];
  //  }
//
  //  self.pc += 1;
  //}
//
  //fn branch(&mut self, args : u32) {
  //  let condition = args >> 7;
  //  let imm = Self::sign_ext_7(args & 0x7F);
//
  //  let branch = match condition {
  //    0 => self.flags[1], // bz / beq
  //    1 => !self.flags[1] && !self.flags[2], // bp
  //    2 => self.flags[2], // bn
  //    3 => self.flags[0], // bc
  //    4 => self.flags[3], // bo
  //    5 => !self.flags[1], // bnz / bne
  //    6 => true, // jmp
  //    7 => !self.flags[0], // bnc
  //    8 => self.flags[2] == self.flags[3] && !self.flags[1], // bg
  //    9 => self.flags[2] == self.flags[3], // bge
  //    10 => self.flags[2] != self.flags[3] && !self.flags[1], // bl
  //    11 => self.flags[2] != self.flags[3] || self.flags[1], // ble
//
  //    // TODO: figure out why these don't match the ROM
  //    12 => !self.flags[1] && self.flags[0], // ba
  //    13 => self.flags[0] || self.flags[1], // bae
  //    14 => !self.flags[0] && !self.flags[1], // bb
  //    15 => !self.flags[0] || self.flags[1], // bbe
  //    _ => false
  //  };
//
  //  if branch {
  //    self.pc = u16::wrapping_add(self.pc, u16::wrapping_add(1 , imm));
  //  } else {
  //    self.pc += 1;
  //  }
  //}
//
  //fn jalr_or_exc(&mut self, args : u32) {
  //  let exc_code = args & 0x007F;
  //  if exc_code != 0 {
  //    // this is an exception
  //    match exc_code {
  //      0x70 => {
  //        // this is a sys EXIT
  //        self.halted = true;
  //      },
  //      0x71 => {
  //        // this is a sys PUTCHAR
  //        // print the character in r3
  //        let character = char::from_u32(u32::from(self.regfile[3])).unwrap();
  //        print!("{}", character);
  //        self.pc += 1;
  //      },
  //      _ => panic!("Invalid Exception code")
  //    }
  //  } else {
  //    // this is a jalr
  //    // branch to address in r_b, store pc + 1 in r_a
  //    let r_a = args >> 10;
  //    let r_b = (args >> 7) & 0b111;
//
  //    let tmp = self.pc + 1;
//
  //    self.pc = self.regfile[usize::from(r_b)];
//
  //    if r_a != 0 {
  //      self.regfile[usize::from(r_a)] = tmp;
  //    }
  //  }
  //}

  //fn update_flags(&mut self, result : u16, lhs : u16, rhs : u16) {
  //  let result_sign = result >> 15;
  //  let lhs_sign = lhs >> 15;
  //  let rhs_sign = rhs >> 15;
//
  //  // set the zero flag
  //  self.flags[1] = if result == 0 {true} else {false};
  //  // set the sign flag
  //  self.flags[2] = if result_sign != 0 {true} else {false};
  //  // set the overflow flag
  //  let ovrflw_condition = (result_sign != lhs_sign) && (lhs_sign == rhs_sign);
  //  self.flags[3] = if ovrflw_condition {true} else {false};
  //}
//
  //fn sign_ext_7 (x : u16) -> u16 {
  //  let sign = x >> 6;
  //  if sign != 0{
  //    // this is a negative number
  //    // we need to sign extend
  //    x + 0xFF80
  //  } else {
  //    // this is a positive number
  //    // we can zero extend
  //    x
  //  }
  //}
}