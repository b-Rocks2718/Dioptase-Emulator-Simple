// User-mode Dioptase emulator: registers, flags, a sparse permission-checked
// memory, and instruction execution (docs/ISA.md "User Instructions").
//
// There is no kernel mode here. Conditions that would raise an exception on
// real hardware (invalid instructions, misaligned PC, permission violations)
// stop the emulator with a panic that names the instruction and address.
// `trap` is a host-side exit: it halts and run() reports r1.

use std::collections::HashMap;

mod alu;
mod debugger;
mod program;

use program::{
  DebugInfo, DebugLine, DebugLocal, LabelMap, MemPerm, MemoryRegion, PERM_RW, PERM_RWX, ProgramImage,
  load_program,
};

// A 64 KiB read/write stack ends just below 0x80000000; r31 starts at the top.
const STACK_SIZE: u32 = 0x10000;
const STACK_TOP: u32 = 0x8000_0000;
const STACK_BASE: u32 = STACK_TOP - STACK_SIZE;
// Stack pointer register (docs/abi.md).
const SP_REG: u32 = 31;
// trap encodings with any of these bits set are reserved.
const TRAP_RESERVED_MASK: u32 = 0x07FF_FFFF;
// Trap code (in r1) for the exit trap; r2 carries the exit status.
const TRAP_EXIT_CODE: u32 = 0;

// Condition flags (docs/ISA.md "ALU flags and edge cases").
#[derive(Clone, Copy, Debug, Default)]
struct Flags {
  carry: bool,
  zero: bool,
  sign: bool,
  overflow: bool,
}

// Kind of memory access, for permission checks.
#[derive(Clone, Copy, Debug)]
enum MemAccess {
  Read,
  Write,
  Exec,
}

// Access width of a load or store.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Width {
  Byte,
  Half,
  Word,
}

impl Width {
  fn bytes(self) -> u32 {
    match self {
      Width::Byte => 1,
      Width::Half => 2,
      Width::Word => 4,
    }
  }
}

// Address formation shared by the memory and atomic instruction groups.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AddrMode {
  // rB + imm (memory forms also support pre/post-increment)
  Absolute,
  // rB + imm + PC + 4
  Relative,
  // imm + PC + 4
  Immediate,
}

// Read-modify-write operation performed by an atomic instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AtomicOp {
  FetchAdd,
  Swap,
}

// Selects which kinds of access cause a watchpoint to fire.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WatchKind {
  Read,
  Write,
  ReadWrite,
}

// Records whether a watchpoint was triggered by a read or write.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WatchAccess {
  Read,
  Write,
}

// Single-byte watchpoint tracked by exact address.
#[derive(Clone, Copy, Debug)]
struct Watchpoint {
  addr: u32,
  kind: WatchKind,
}

// Describes the memory access that triggered a watchpoint.
#[derive(Clone, Copy, Debug)]
struct WatchpointHit {
  addr: u32,
  access: WatchAccess,
  value: u8,
}

// Field extractors shared by most instruction formats.
fn field_a(instr: u32) -> u32 {
  (instr >> 22) & 0x1F
}
fn field_b(instr: u32) -> u32 {
  (instr >> 17) & 0x1F
}

// Owns the CPU state, guest memory, and execution metadata for one program.
pub struct Emulator {
  regfile: [u32; 32],
  ram: HashMap<u32, u8>,
  mem_regions: Vec<MemoryRegion>,
  default_perm: MemPerm,
  pc: u32,
  flags: Flags,
  halted: bool,
  watchpoints: Vec<Watchpoint>,
  watchpoint_hit: Option<WatchpointHit>,
}

impl Emulator {
  // Load a program image and reset the CPU at its entry point.
  pub fn new(path: &str) -> Result<Emulator, String> {
    Ok(Emulator::from_image(&load_program(path)?))
  }

  // Build an emulator from a loaded image, adding the RW stack region.
  fn from_image(image: &ProgramImage) -> Emulator {
    let mut regions = image.regions.clone();
    regions.push(MemoryRegion { base: STACK_BASE, size: STACK_SIZE, perm: PERM_RW });
    let mut regfile = [0u32; 32];
    regfile[SP_REG as usize] = STACK_TOP;
    Emulator {
      regfile,
      ram: image.bytes.clone(),
      mem_regions: regions,
      default_perm: image.default_perm,
      pc: image.entry,
      flags: Flags::default(),
      halted: false,
      watchpoints: Vec::new(),
      watchpoint_hit: None,
    }
  }

  // Build an emulator from raw bytes at address 0 with full permissions.
  pub fn from_instructions(bytes: HashMap<u32, u8>) -> Emulator {
    Emulator::from_image(&ProgramImage {
      bytes,
      labels: LabelMap::new(),
      entry: 0,
      regions: Vec::new(),
      default_perm: PERM_RWX,
      debug: DebugInfo::default(),
    })
  }

  // Run until a halting trap; returns r1, or None if `max_iters` (when
  // nonzero) instructions run first.
  pub fn run(&mut self, max_iters: u32) -> Option<u32> {
    let mut cycles: u32 = 0;
    while !self.halted {
      self.step();
      cycles = cycles.wrapping_add(1);
      if max_iters != 0 && cycles > max_iters {
        return None;
      }
    }
    Some(self.regfile[1])
  }

  // Fetch and execute one instruction; returns its PC and encoding.
  fn step(&mut self) -> (u32, u32) {
    let pc = self.pc;
    assert!(pc.is_multiple_of(4), "Emulator: PC 0x{:08X} is not word aligned", pc);
    let instr = self.fetch32(pc);
    self.execute(instr);
    (pc, instr)
  }

  // Stop on an instruction this emulator cannot execute.
  fn invalid_instruction(&self, instr: u32, reason: &str) -> ! {
    panic!("Emulator: invalid instruction 0x{:08X} at pc 0x{:08X}: {}", instr, self.pc, reason);
  }

  // ---- Registers -------------------------------------------------------

  fn get_reg(&self, regnum: u32) -> u32 {
    self.regfile[regnum as usize]
  }

  // Write a register; r0 is hardwired to zero.
  fn write_reg(&mut self, regnum: u32, value: u32) {
    if regnum != 0 {
      self.regfile[regnum as usize] = value;
    }
  }

  fn advance(&mut self) {
    self.pc = self.pc.wrapping_add(4);
  }

  // ---- Memory ------------------------------------------------------------

  // Permissions for an address: its region's, else the image default.
  fn perm_for_addr(&self, addr: u32) -> MemPerm {
    self
      .mem_regions
      .iter()
      .find(|region| region.contains(addr))
      .map_or(self.default_perm, |region| region.perm)
  }

  // Stop if `addr` does not allow `access`.
  fn check_access(&self, addr: u32, access: MemAccess) {
    let perm = self.perm_for_addr(addr);
    let allowed = match access {
      MemAccess::Read => perm.read,
      MemAccess::Write => perm.write,
      MemAccess::Exec => perm.exec,
    };
    if !allowed {
      panic!("Memory {:?} access violation at {:08X} (pc 0x{:08X})", access, addr, self.pc);
    }
  }

  // Record the first watchpoint hit so the debugger can stop after stepping.
  fn watch(&mut self, addr: u32, access: WatchAccess, value: u8) {
    if self.watchpoint_hit.is_some() {
      return;
    }
    let hit = self.watchpoints.iter().any(|wp| {
      wp.addr == addr
        && matches!(
          (wp.kind, access),
          (WatchKind::ReadWrite, _) | (WatchKind::Read, WatchAccess::Read) | (WatchKind::Write, WatchAccess::Write)
        )
    });
    if hit {
      self.watchpoint_hit = Some(WatchpointHit { addr, access, value });
    }
  }

  // Byte at `addr`; unwritten memory reads as 0. No checks or watchpoints.
  fn read_debug8(&self, addr: u32) -> u8 {
    self.ram.get(&addr).copied().unwrap_or(0)
  }

  // Little-endian word at `addr` without checks or watchpoints.
  fn read_debug32(&self, addr: u32) -> u32 {
    u32::from_le_bytes(std::array::from_fn(|i| self.read_debug8(addr.wrapping_add(i as u32))))
  }

  // Warn about and clear the low address bits of a sized access (accesses
  // are naturally aligned, per docs/ISA.md).
  fn align(addr: u32, width: Width) -> u32 {
    let size = width.bytes();
    if size > 1 && addr & (size - 1) != 0 {
      println!("Warning: unaligned memory access at {:08x}", addr);
    }
    addr & !(size - 1)
  }

  // Fetch an instruction word; every byte must be executable.
  fn fetch32(&self, addr: u32) -> u32 {
    for offset in 0..4 {
      self.check_access(addr.wrapping_add(offset), MemAccess::Exec);
    }
    self.read_debug32(addr)
  }

  // Load `width` bytes (zero-extended), checking each byte's permission.
  fn load(&mut self, addr: u32, width: Width) -> u32 {
    let addr = Self::align(addr, width);
    let mut value = 0;
    for i in 0..width.bytes() {
      let byte_addr = addr.wrapping_add(i);
      self.check_access(byte_addr, MemAccess::Read);
      let byte = self.read_debug8(byte_addr);
      self.watch(byte_addr, WatchAccess::Read, byte);
      value |= u32::from(byte) << (8 * i);
    }
    value
  }

  // Store the low `width` bytes of `value`, checking each byte's permission.
  fn store(&mut self, addr: u32, width: Width, value: u32) {
    let addr = Self::align(addr, width);
    for i in 0..width.bytes() {
      let byte_addr = addr.wrapping_add(i);
      let byte = (value >> (8 * i)) as u8;
      self.check_access(byte_addr, MemAccess::Write);
      self.watch(byte_addr, WatchAccess::Write, byte);
      self.ram.insert(byte_addr, byte);
    }
  }

  // ---- Execution -----------------------------------------------------------

  // Decode the opcode (top 5 bits) and execute one instruction.
  fn execute(&mut self, instr: u32) {
    const WIDTHS: [Width; 3] = [Width::Word, Width::Half, Width::Byte];
    const MODES: [AddrMode; 3] = [AddrMode::Absolute, AddrMode::Relative, AddrMode::Immediate];
    let opcode = instr >> 27;
    match opcode {
      0 => self.alu_instr(instr, false),
      1 => self.alu_instr(instr, true),
      2 => {
        // lui: rA <- imm22 << 10
        self.write_reg(field_a(instr), (instr & 0x3F_FFFF) << 10);
        self.advance();
      }
      3..=11 => {
        let group = (opcode - 3) as usize;
        self.mem_instr(instr, WIDTHS[group / 3], MODES[group % 3]);
      }
      12 => self.branch_imm(instr),
      13 => self.branch_reg(instr, false),
      14 => self.branch_reg(instr, true),
      15 => self.trap_instr(instr),
      16..=18 => self.atomic_instr(instr, AtomicOp::FetchAdd, MODES[(opcode - 16) as usize]),
      19..=21 => self.atomic_instr(instr, AtomicOp::Swap, MODES[(opcode - 19) as usize]),
      22 => {
        // adpc: rA <- PC + 4 + sext(imm22)
        let imm = alu::sign_extend(instr & 0x3F_FFFF, 22);
        self.write_reg(field_a(instr), self.pc.wrapping_add(4).wrapping_add(imm));
        self.advance();
      }
      31 => self.invalid_instruction(instr, "privileged instructions are not supported in user mode"),
      _ => self.invalid_instruction(instr, "undefined opcode"),
    }
  }

  // ALU instruction; the second operand is rC or a decoded immediate.
  fn alu_instr(&mut self, instr: u32, imm_form: bool) {
    let lhs = self.get_reg(field_b(instr));
    let (op, rhs) = if imm_form {
      let op = (instr >> 12) & 0x1F;
      match alu::decode_imm(op, instr & 0xFFF) {
        Some(imm) => (op, imm),
        None => self.invalid_instruction(instr, "ALU op has no immediate form"),
      }
    } else {
      ((instr >> 5) & 0x1F, self.get_reg(instr & 0x1F))
    };
    let Some(out) = alu::evaluate(op, lhs, rhs, self.flags.carry, imm_form) else {
      self.invalid_instruction(instr, "undefined ALU op");
    };
    // Immediate subtractions compute imm - rB, so V uses that order.
    let reversed = imm_form && (op == alu::OP_SUB || op == alu::OP_SUBB);
    let (a, b) = if reversed { (rhs, lhs) } else { (lhs, rhs) };
    self.flags = Flags {
      carry: out.carry,
      zero: out.value == 0,
      sign: out.value >> 31 != 0,
      overflow: alu::overflow(op, a, b, out.value),
    };
    self.write_reg(field_a(instr), out.value);
    self.advance();
  }

  // Load/store with absolute, PC-relative, or immediate addressing.
  fn mem_instr(&mut self, instr: u32, width: Width, mode: AddrMode) {
    let r_a = field_a(instr);
    let (addr, is_load, writeback) = match mode {
      AddrMode::Absolute => {
        // op | rA | rB | load | y(2) | z(2) | imm12; imm is shifted by z.
        // y: 0 = offset, 1 = pre-increment, 2 = post-increment. y = 3 is
        // not specified by docs/ISA.md and behaves like y = 0.
        let r_b = field_b(instr);
        let y = (instr >> 14) & 3;
        let imm = alu::sign_extend(instr & 0xFFF, 12) << ((instr >> 12) & 3);
        let base = self.get_reg(r_b);
        let offset_addr = base.wrapping_add(imm);
        let addr = if y == 2 { base } else { offset_addr };
        (addr, (instr >> 16) & 1 != 0, matches!(y, 1 | 2).then_some((r_b, offset_addr)))
      }
      AddrMode::Relative => {
        let imm = alu::sign_extend(instr & 0xFFFF, 16);
        let addr = self.get_reg(field_b(instr)).wrapping_add(imm).wrapping_add(self.pc).wrapping_add(4);
        (addr, (instr >> 16) & 1 != 0, None)
      }
      AddrMode::Immediate => {
        let imm = alu::sign_extend(instr & 0x1F_FFFF, 21);
        (imm.wrapping_add(self.pc).wrapping_add(4), (instr >> 21) & 1 != 0, None)
      }
    };
    if is_load {
      let value = self.load(addr, width);
      self.write_reg(r_a, value);
    } else {
      self.store(addr, width, self.get_reg(r_a));
    }
    if let Some((r_b, value)) = writeback {
      self.write_reg(r_b, value);
    }
    self.advance();
  }

  // Atomic fetch-add or swap: rA <- old [addr], [addr] <- f(old, rC).
  fn atomic_instr(&mut self, instr: u32, op: AtomicOp, mode: AddrMode) {
    // op | rA | rC | rB | imm12, or op | rA | rC | imm17 for Immediate.
    let operand = self.get_reg(field_b(instr));
    let addr = match mode {
      AddrMode::Immediate => alu::sign_extend(instr & 0x1_FFFF, 17).wrapping_add(self.pc).wrapping_add(4),
      _ => {
        let base = self.get_reg((instr >> 12) & 0x1F).wrapping_add(alu::sign_extend(instr & 0xFFF, 12));
        if mode == AddrMode::Relative { base.wrapping_add(self.pc).wrapping_add(4) } else { base }
      }
    };
    let prev = self.load(addr, Width::Word);
    self.write_reg(field_a(instr), prev);
    let next = match op {
      AtomicOp::FetchAdd => prev.wrapping_add(operand),
      AtomicOp::Swap => operand,
    };
    self.store(addr, Width::Word, next);
    self.advance();
  }

  // Evaluate a branch condition code; None for undefined codes.
  fn branch_condition(&self, cond: u32) -> Option<bool> {
    let Flags { carry, zero, sign, overflow } = self.flags;
    Some(match cond {
      0 => true,                       // br
      1 => zero,                       // bz
      2 => !zero,                      // bnz
      3 => sign,                       // bs
      4 => !sign,                      // bns
      5 => carry,                      // bc
      6 => !carry,                     // bnc
      7 => overflow,                   // bo
      8 => !overflow,                  // bno
      9 => !zero && !sign,             // bps
      10 => zero || sign,              // bnps
      11 => sign == overflow && !zero, // bg
      12 => sign == overflow,          // bge
      13 => sign != overflow && !zero, // bl
      14 => sign != overflow || zero,  // ble
      15 => !zero && carry,            // ba
      16 => carry || zero,             // bae
      17 => !carry && !zero,           // bb
      18 => !carry || zero,            // bbe
      _ => return None,
    })
  }

  // PC-relative branch: target = PC + 4 + sext(imm22) * 4.
  fn branch_imm(&mut self, instr: u32) {
    let Some(taken) = self.branch_condition(field_a(instr)) else {
      self.invalid_instruction(instr, "undefined branch condition");
    };
    if taken {
      let offset = alu::sign_extend(instr & 0x3F_FFFF, 22).wrapping_mul(4);
      self.pc = self.pc.wrapping_add(4).wrapping_add(offset);
    } else {
      self.advance();
    }
  }

  // Register branch with link: rA <- PC + 4, then PC <- rB (absolute) or
  // PC + 4 + rB (relative). rB is read before rA is written.
  fn branch_reg(&mut self, instr: u32, relative: bool) {
    let target = self.get_reg(instr & 0x1F);
    let Some(taken) = self.branch_condition(field_a(instr)) else {
      self.invalid_instruction(instr, "undefined branch condition");
    };
    if !taken {
      return self.advance();
    }
    let link = self.pc.wrapping_add(4);
    self.write_reg((instr >> 5) & 0x1F, link);
    self.pc = if relative { link.wrapping_add(target) } else { target };
  }

  // trap: host-side program exit. With the exit trap ABI (r1 = 0), r2 holds
  // the exit status and is copied into r1 so run() reports it; a bare trap
  // halts and reports the current r1.
  fn trap_instr(&mut self, instr: u32) {
    if instr & TRAP_RESERVED_MASK != 0 {
      self.invalid_instruction(instr, "reserved trap encoding");
    }
    if self.get_reg(1) == TRAP_EXIT_CODE {
      self.write_reg(1, self.get_reg(2));
    }
    self.halted = true;
  }
}
