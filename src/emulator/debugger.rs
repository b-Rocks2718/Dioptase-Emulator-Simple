// Interactive debuggers: `--debug` (instruction level, labels from `#label`)
// and `--debugc` (C source level, from `#line`/`#local`/`#data`). `r`
// reloads the program from scratch.

use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io::{self, BufRead, Write};
use std::path::Path;

use crate::disassembler::disassemble;

use super::{
  DebugInfo, DebugLine, DebugLocal, Emulator, LabelMap, ProgramImage, WatchAccess, WatchKind, Watchpoint,
  WatchpointHit, load_program,
};

// Upper bound on instructions per source-level step, so a step on a line
// that never ends (e.g. a spin loop) returns control to the user.
const MAX_STEP_INSTRUCTIONS: u32 = 1_000_000;
// ABI base pointer register (docs/abi.md); C locals are addressed from it.
const BP_REG: u32 = 30;
// General-purpose register aliases from docs/abi.md.
const GPR_ALIASES: [(&str, u32); 3] = [("sp", 31), ("bp", 30), ("ra", 29)];

const ASM_HELP: &str = "\
  r                 reset and run until break/watchpoint/halt
  c                 continue execution
  n                 step one instruction
  break <label|addr> set breakpoint
  breaks            list breakpoints
  delete <label|addr> remove breakpoint
  watch [r|w|rw] <addr> stop on memory access
  watchs            list watchpoints
  unwatch <addr>    remove watchpoint
  info regs         print all registers/flags
  info <reg>        print a single register
  info <addr>       print word at address
  x <addr> <len>    dump memory range
  set reg <reg> <value> write a register
  q                 quit";

const C_HELP: &str = "\
  r                   reset and run until break/halt
  c                   continue execution
  step                step to the next source line
  next                step over calls to the next source line
  break <line>         set breakpoint on current file line
  break <file>:<line>  set breakpoint on file line
  break <label>        set breakpoint on label
  break *<addr>        set breakpoint on address
  breaks              list breakpoints
  delete <target>     remove breakpoint
  info locals         print locals for current frame
  info globals        print global data symbols
  q                   quit";

// Parse a debugger number: 0x-prefixed hex, decimal, or bare hex digits.
fn parse_addr(token: &str) -> Option<u32> {
  let s = token.trim();
  if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
    return u32::from_str_radix(hex, 16).ok();
  }
  s.parse::<u32>().ok().or_else(|| u32::from_str_radix(s, 16).ok())
}

// Print the prompt and read one non-empty command; None on EOF or error.
fn read_command() -> Option<String> {
  loop {
    print!("dbg> ");
    io::stdout().flush().unwrap();
    let mut line = String::new();
    match io::stdin().read_line(&mut line) {
      Ok(0) | Err(_) => return None,
      Ok(_) => {
        let line = line.trim();
        if !line.is_empty() {
          return Some(line.to_string());
        }
      }
    }
  }
}

// Read one source line (1-based) for display.
fn read_source_line(file: &str, line: u32) -> Result<String, String> {
  if line == 0 {
    return Err("Line numbers start at 1".to_string());
  }
  let path = Path::new(file);
  let path = if path.is_absolute() {
    path.to_path_buf()
  } else {
    env::current_dir().map_err(|err| format!("Failed to resolve cwd: {}", err))?.join(file)
  };
  let file = File::open(&path).map_err(|err| format!("Failed to open {}: {}", path.display(), err))?;
  match io::BufReader::new(file).lines().nth(line as usize - 1) {
    Some(Ok(text)) => Ok(text),
    Some(Err(err)) => Err(format!("Failed to read {}: {}", path.display(), err)),
    None => Err(format!("File {} has no line {}", path.display(), line)),
  }
}

// Invert the label map so every address lists all symbols defined there.
fn build_labels_by_addr(labels: &LabelMap) -> HashMap<u32, Vec<String>> {
  let mut by_addr: HashMap<u32, Vec<String>> = HashMap::new();
  for (name, addrs) in labels {
    for addr in addrs {
      by_addr.entry(*addr).or_default().push(name.clone());
    }
  }
  by_addr
}

// Format addresses as a comma-separated list of eight-digit hex values.
fn format_addr_list(addrs: &[u32]) -> String {
  addrs.iter().map(|addr| format!("{:08X}", addr)).collect::<Vec<_>>().join(", ")
}

// Print breakpoints in address order, each described by `describe`.
fn list_breakpoints(breakpoints: &HashSet<u32>, describe: impl Fn(u32) -> String) {
  if breakpoints.is_empty() {
    println!("No breakpoints set.");
    return;
  }
  let mut list: Vec<u32> = breakpoints.iter().copied().collect();
  list.sort_unstable();
  for addr in list {
    println!("{}", describe(addr));
  }
}

// Why debugger execution returned control to the user.
enum RunOutcome {
  Breakpoint(u32),
  Halted,
  Watchpoint(WatchpointHit),
}

// Run until halt, a watchpoint, or a breakpoint. When `resume` is set, the
// breakpoint at the starting PC is ignored until execution leaves that PC,
// so `c` from a breakpoint makes progress.
fn run_until_breakpoint(cpu: &mut Emulator, breakpoints: &HashSet<u32>, resume: bool) -> RunOutcome {
  let start_pc = cpu.pc;
  let mut skip_start = resume;
  loop {
    if cpu.halted {
      return RunOutcome::Halted;
    }
    if cpu.pc != start_pc {
      skip_start = false;
    }
    if breakpoints.contains(&cpu.pc) && !skip_start {
      return RunOutcome::Breakpoint(cpu.pc);
    }
    cpu.step();
    if let Some(hit) = cpu.watchpoint_hit.take() {
      return RunOutcome::Watchpoint(hit);
    }
  }
}

// Report how a run ended, using `show_stop` to describe a breakpoint stop.
fn report_run(outcome: RunOutcome, cpu: &mut Emulator, show_stop: impl FnOnce(&mut Emulator, u32)) {
  match outcome {
    RunOutcome::Breakpoint(addr) => show_stop(cpu, addr),
    RunOutcome::Halted => println!("Program halted. r1 = {:08X}", cpu.regfile[1]),
    RunOutcome::Watchpoint(hit) => println!(
      "Watchpoint hit ({} at {:08X} = {:02X}) pc {:08X}",
      if hit.access == WatchAccess::Read { "read" } else { "write" },
      hit.addr,
      hit.value,
      cpu.pc
    ),
  }
}

// ---- Instruction-level debugger helpers -----------------------------------

// Display label for a watchpoint access kind.
fn watch_kind_label(kind: WatchKind) -> &'static str {
  match kind {
    WatchKind::Read => "r",
    WatchKind::Write => "w",
    WatchKind::ReadWrite => "rw",
  }
}

// Parse the read/write/read-write watchpoint selector.
fn parse_watch_kind(token: &str) -> Option<WatchKind> {
  match token {
    "r" => Some(WatchKind::Read),
    "w" => Some(WatchKind::Write),
    "rw" | "wr" => Some(WatchKind::ReadWrite),
    _ => None,
  }
}

// Insert a watchpoint, widening an existing one at the same address to
// read/write if the kinds differ. Returns the resulting kind.
fn add_watchpoint(list: &mut Vec<Watchpoint>, addr: u32, kind: WatchKind) -> WatchKind {
  if let Some(wp) = list.iter_mut().find(|wp| wp.addr == addr) {
    if wp.kind != kind {
      wp.kind = WatchKind::ReadWrite;
    }
    return wp.kind;
  }
  list.push(Watchpoint { addr, kind });
  kind
}

// Resolve a target that must name exactly one address (number or label).
fn resolve_single(target: &str, labels: &LabelMap) -> Result<u32, String> {
  if let Some(addr) = parse_addr(target) {
    return Ok(addr);
  }
  let addrs = labels.get(target).ok_or_else(|| format!("Unknown label {}", target))?;
  match addrs.as_slice() {
    [addr] => Ok(*addr),
    _ => Err(format!("Ambiguous label {} -> {}", target, format_addr_list(addrs))),
  }
}

// Print an executed or stopped-at instruction with its labels.
fn print_step(pc: u32, instr: u32, labels_by_addr: &HashMap<u32, Vec<String>>) {
  match labels_by_addr.get(&pc) {
    Some(names) => println!("{:08X}: {:08X}  {} ({})", pc, instr, disassemble(instr), names.join(", ")),
    None => println!("{:08X}: {:08X}  {}", pc, instr, disassemble(instr)),
  }
}

// Hex-dump `len` bytes starting at `base`, 16 per row.
fn dump_bytes(base: u32, len: u32, read_byte: impl Fn(u32) -> u8) {
  if len == 0 {
    println!("(empty range)");
    return;
  }
  for offset in 0..len {
    let addr = base.wrapping_add(offset);
    if offset % 16 == 0 {
      print!("{:08X}: ", addr);
    }
    print!("{:02X} ", read_byte(addr));
    if offset % 16 == 15 || offset + 1 == len {
      println!();
    }
  }
}

// ---- C-level debugger helpers ---------------------------------------------

// Debug addresses indexed by source file and line (sorted, deduplicated).
type LineIndex = HashMap<String, HashMap<u32, Vec<u32>>>;

// Build the file -> line -> addresses index.
fn build_line_index(lines: &[DebugLine]) -> LineIndex {
  let mut index: LineIndex = HashMap::new();
  for line in lines {
    index.entry(line.file.clone()).or_default().entry(line.line).or_default().push(line.addr);
  }
  for addrs in index.values_mut().flat_map(|file| file.values_mut()) {
    addrs.sort_unstable();
    addrs.dedup();
  }
  index
}

// Last line marker at or below `pc`. Requires `lines` sorted by address.
fn line_for_pc(lines: &[DebugLine], pc: u32) -> Option<&DebugLine> {
  let idx = lines.partition_point(|line| line.addr <= pc);
  idx.checked_sub(1).map(|i| &lines[i])
}

// Whether two debug locations refer to the same source line.
fn same_source_line(a: Option<&DebugLine>, b: Option<&DebugLine>) -> bool {
  match (a, b) {
    (Some(a), Some(b)) => a.line == b.line && a.file == b.file,
    (None, None) => true,
    _ => false,
  }
}

// Print the source line for `pc`, with lookup failures shown inline.
fn print_c_location(pc: u32, line: Option<&DebugLine>) {
  let Some(line) = line else {
    println!("{:08X}: <no line info>", pc);
    return;
  };
  match read_source_line(&line.file, line.line) {
    Ok(text) => println!("{:08X}: {}:{}: {}", pc, line.file, line.line, text),
    Err(err) => println!("{:08X}: {}:{}: <{}>", pc, line.file, line.line, err),
  }
}

// Locals sorted by their anchor address, each list sorted by bp offset.
fn build_locals_by_addr(debug: &DebugInfo) -> Vec<(u32, Vec<DebugLocal>)> {
  let mut locals: Vec<(u32, Vec<DebugLocal>)> = debug
    .locals_by_addr
    .iter()
    .map(|(addr, locals)| {
      let mut locals = locals.clone();
      locals.sort_by_key(|local| local.offset);
      (*addr, locals)
    })
    .collect();
  locals.sort_by_key(|(addr, _)| *addr);
  locals
}

// Heuristic function entries: the compiler emits a duplicate #line at each
// function label, so a line with several addresses whose first address
// carries a non-local (no '.') label marks a function start.
fn build_function_entries(line_index: &LineIndex, labels_by_addr: &HashMap<u32, Vec<String>>) -> Vec<u32> {
  let mut entries: Vec<u32> = line_index
    .values()
    .flat_map(|file| file.values())
    .filter(|addrs| addrs.len() >= 2)
    .map(|addrs| addrs[0])
    .filter(|addr| labels_by_addr.get(addr).is_some_and(|names| names.iter().any(|name| !name.contains('.'))))
    .collect();
  entries.sort_unstable();
  entries.dedup();
  entries
}

// [start, end) of the function containing `pc`. Requires sorted `entries`.
fn function_range_for_pc(entries: &[u32], pc: u32) -> Option<(u32, Option<u32>)> {
  let idx = entries.partition_point(|&entry| entry <= pc);
  let start = *entries.get(idx.checked_sub(1)?)?;
  Some((start, entries.get(idx).copied()))
}

// Locals in scope at `pc`: the nearest anchor at or below `pc`, provided it
// lies inside the current function. Requires sorted inputs.
fn locals_for_pc<'a>(locals: &'a [(u32, Vec<DebugLocal>)], func_entries: &[u32], pc: u32) -> Option<&'a Vec<DebugLocal>> {
  let idx = locals.partition_point(|(addr, _)| *addr <= pc);
  let (anchor, list) = &locals[idx.checked_sub(1)?];
  match function_range_for_pc(func_entries, pc) {
    Some((func_start, _)) if *anchor < func_start => None,
    _ => Some(list),
  }
}

// First local anchor inside [start, end), used to explain "not yet in scope".
fn first_locals_addr_in_range(locals: &[(u32, Vec<DebugLocal>)], start: u32, end: Option<u32>) -> Option<u32> {
  let idx = locals.partition_point(|(addr, _)| *addr < start);
  let addr = locals.get(idx)?.0;
  match end {
    Some(end) if addr >= end => None,
    _ => Some(addr),
  }
}

// Strip the compiler's numeric suffix (".N") from local names for display.
fn display_local_name(name: &str) -> &str {
  match name.rsplit_once('.') {
    Some((base, suffix)) if !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit()) => base,
    _ => name,
  }
}

// Resolve `line`, `file:line`, `*addr`, `0xaddr`, or a label to addresses.
fn resolve_break_targets_c(
  token: &str,
  labels: &LabelMap,
  line_index: &LineIndex,
  default_file: Option<&str>,
) -> Result<Vec<u32>, String> {
  let lookup_line = |file: &str, line_str: &str| -> Result<Vec<u32>, String> {
    let line = line_str.parse::<u32>().map_err(|_| format!("Invalid line number {}", line_str))?;
    line_index
      .get(file)
      .ok_or_else(|| format!("Unknown source file {}", file))?
      .get(&line)
      .cloned()
      .ok_or_else(|| format!("No debug line {} in {}", line, file))
  };
  if let Some(rest) = token.strip_prefix('*') {
    return parse_addr(rest).map(|addr| vec![addr]).ok_or_else(|| format!("Invalid address {}", rest));
  }
  if token.starts_with("0x") || token.starts_with("0X") {
    return parse_addr(token).map(|addr| vec![addr]).ok_or_else(|| format!("Invalid address {}", token));
  }
  if let Some((file, line_str)) = token.rsplit_once(':') {
    return lookup_line(file, line_str);
  }
  if token.chars().all(|c| c.is_ascii_digit()) {
    let file = default_file.ok_or_else(|| "No default source file; use break <file>:<line> instead".to_string())?;
    return lookup_line(file, token);
  }
  labels.get(token).cloned().ok_or_else(|| format!("Unknown label {}", token))
}

// Show values of up to 4 bytes as little-endian hex, larger ones as bytes.
fn format_bytes(bytes: &[u8]) -> String {
  if bytes.is_empty() {
    return "<empty>".to_string();
  }
  if bytes.len() <= 4 {
    let value = bytes.iter().rev().fold(0u32, |acc, byte| (acc << 8) | u32::from(*byte));
    return format!("0x{:0width$X}", value, width = bytes.len() * 2);
  }
  let parts: Vec<String> = bytes.iter().map(|byte| format!("{:02X}", byte)).collect();
  format!("[{}]", parts.join(" "))
}

// Register selected by a debugger register token.
#[derive(Clone, Copy)]
enum DebugReg {
  Pc,
  Gpr(u32),
}

impl Emulator {
  // A freshly reset core for `image`, carrying the current watchpoints.
  fn reset_from(image: &ProgramImage, watchpoints: &[Watchpoint]) -> Emulator {
    let mut cpu = Emulator::from_image(image);
    cpu.watchpoints = watchpoints.to_vec();
    cpu
  }

  // Print all registers and flags.
  fn print_regs(&self) {
    println!("pc: {:08X}", self.pc);
    for row in 0..8u32 {
      let cells: Vec<String> = (row * 4..row * 4 + 4).map(|r| format!("r{:02}: {:08X}", r, self.get_reg(r))).collect();
      println!("{}", cells.join(" "));
    }
    let f = self.flags;
    println!("flags: C={} Z={} S={} O={}", f.carry as u8, f.zero as u8, f.sign as u8, f.overflow as u8);
  }

  // Resolve "pc", rN, or a docs/abi.md alias to (display label, register).
  fn parse_register(token: &str) -> Option<(String, DebugReg)> {
    let token = token.to_ascii_lowercase();
    if token == "pc" {
      return Some(("pc".to_string(), DebugReg::Pc));
    }
    if let Some(&(name, reg)) = GPR_ALIASES.iter().find(|(name, _)| *name == token) {
      return Some((format!("{} (r{})", name, reg), DebugReg::Gpr(reg)));
    }
    let idx = token.strip_prefix('r')?.parse::<u32>().ok()?;
    (idx < 32).then(|| (token.clone(), DebugReg::Gpr(idx)))
  }

  // Run the instruction-level debugger command loop.
  pub fn debug(path: &str) -> Result<(), String> {
    let image = load_program(path)?;
    let labels = &image.labels;
    let labels_by_addr = build_labels_by_addr(labels);
    let mut breakpoints: HashSet<u32> = HashSet::new();
    let mut watchpoints: Vec<Watchpoint> = Vec::new();
    let mut cpu = Emulator::from_image(&image);
    let show_breakpoint = |cpu: &mut Emulator, addr: u32| print_step(addr, cpu.read_debug32(addr), &labels_by_addr);

    println!("Debug mode:\n{}", ASM_HELP);
    while let Some(line) = read_command() {
      let mut parts = line.split_whitespace();
      let cmd = parts.next().unwrap();
      let usage = |text: &str| println!("Usage: {}", text);
      match cmd {
        "q" | "quit" => break,
        "h" | "help" => println!("Commands:\n{}", ASM_HELP),
        "r" | "c" => {
          if cmd == "r" {
            cpu = Emulator::reset_from(&image, &watchpoints);
          }
          let outcome = run_until_breakpoint(&mut cpu, &breakpoints, cmd == "c");
          report_run(outcome, &mut cpu, show_breakpoint);
        }
        "n" => {
          if cpu.halted {
            println!("Program already halted.");
            continue;
          }
          let (pc, instr) = cpu.step();
          print_step(pc, instr, &labels_by_addr);
          if let Some(hit) = cpu.watchpoint_hit.take() {
            report_run(RunOutcome::Watchpoint(hit), &mut cpu, show_breakpoint);
          }
          if cpu.halted {
            println!("Program halted. r1 = {:08X}", cpu.regfile[1]);
          }
        }
        "break" | "b" => match parts.next().map(|t| resolve_single(t, labels)) {
          None => usage("break <label|addr>"),
          Some(Ok(addr)) => {
            breakpoints.insert(addr);
            println!("Breakpoint set at {:08X}", addr);
          }
          Some(Err(msg)) => println!("{}", msg),
        },
        "breaks" => list_breakpoints(&breakpoints, |addr| match labels_by_addr.get(&addr) {
          Some(names) => format!("{:08X} ({})", addr, names.join(", ")),
          None => format!("{:08X}", addr),
        }),
        "delete" | "del" => match parts.next().map(|t| resolve_single(t, labels)) {
          None => usage("delete <label|addr>"),
          Some(Ok(addr)) if breakpoints.remove(&addr) => println!("Breakpoint removed at {:08X}", addr),
          Some(Ok(addr)) => println!("No breakpoint set at {:08X}", addr),
          Some(Err(msg)) => println!("{}", msg),
        },
        "watch" => {
          let mut token = parts.next();
          let kind = token.and_then(parse_watch_kind);
          if kind.is_some() {
            token = parts.next();
          }
          let Some(addr_str) = token else {
            usage("watch [r|w|rw] <addr>");
            continue;
          };
          let Some(addr) = parse_addr(addr_str) else {
            println!("Invalid address {}", addr_str);
            continue;
          };
          let kind = add_watchpoint(&mut watchpoints, addr, kind.unwrap_or(WatchKind::ReadWrite));
          cpu.watchpoints = watchpoints.clone();
          println!("Watchpoint set at {:08X} ({})", addr, watch_kind_label(kind));
        }
        "watchs" | "watchpoints" => {
          if watchpoints.is_empty() {
            println!("No watchpoints set.");
          }
          let mut sorted = watchpoints.clone();
          sorted.sort_by_key(|wp| wp.addr);
          for wp in sorted {
            println!("{:08X} ({})", wp.addr, watch_kind_label(wp.kind));
          }
        }
        "unwatch" => {
          let Some(addr_str) = parts.next() else {
            usage("unwatch <addr>");
            continue;
          };
          let Some(addr) = parse_addr(addr_str) else {
            println!("Invalid address {}", addr_str);
            continue;
          };
          let before = watchpoints.len();
          watchpoints.retain(|wp| wp.addr != addr);
          if watchpoints.len() != before {
            cpu.watchpoints = watchpoints.clone();
            println!("Watchpoint removed at {:08X}", addr);
          } else {
            println!("No watchpoint set at {:08X}", addr);
          }
        }
        "x" => {
          let (Some(addr_str), Some(len_str)) = (parts.next(), parts.next()) else {
            usage("x <addr> <len>");
            continue;
          };
          let (Some(addr), Some(len)) = (parse_addr(addr_str), parse_addr(len_str)) else {
            println!("Invalid address or length: {} {}", addr_str, len_str);
            continue;
          };
          dump_bytes(addr, len, |a| cpu.read_debug8(a));
        }
        "set" => {
          let (Some("reg"), Some(reg), Some(value_str)) = (parts.next(), parts.next(), parts.next()) else {
            usage("set reg <reg> <value>");
            continue;
          };
          match (Emulator::parse_register(reg), parse_addr(value_str)) {
            (_, None) => println!("Invalid value {}", value_str),
            (None, _) => println!("Unknown register {}", reg),
            (Some((_, DebugReg::Pc)), Some(value)) => cpu.pc = value,
            (Some((_, DebugReg::Gpr(r))), Some(value)) => cpu.write_reg(r, value),
          }
        }
        "info" => match parts.next() {
          Some("regs") => cpu.print_regs(),
          Some(token) => {
            // Register names win over bare-hex addresses (e.g. "bp").
            if let Some((label, reg)) = Emulator::parse_register(token) {
              let value = match reg {
                DebugReg::Pc => cpu.pc,
                DebugReg::Gpr(r) => cpu.get_reg(r),
              };
              println!("{} = {:08X}", label, value);
            } else if let Some(addr) = parse_addr(token) {
              println!("addr {:08X} = {:08X}", addr, cpu.read_debug32(addr));
            } else {
              println!("Unknown info target {}", token);
            }
          }
          None => usage("info <regs|reg|addr>"),
        },
        _ => println!("Unknown command: {}", cmd),
      }
    }
    Ok(())
  }

  // Run the C-source-level debugger command loop.
  pub fn debug_c(path: &str) -> Result<(), String> {
    let image = load_program(path)?;
    let debug = &image.debug;
    let labels = &image.labels;
    let mut lines = debug.lines.clone();
    lines.sort_by_key(|line| line.addr);
    let line_index = build_line_index(&lines);
    let labels_by_addr = build_labels_by_addr(labels);
    let function_entries = build_function_entries(&line_index, &labels_by_addr);
    let locals_by_addr = build_locals_by_addr(debug);
    let mut globals = debug.globals.clone();
    globals.sort_by(|a, b| a.name.cmp(&b.name).then(a.addr.cmp(&b.addr)));
    globals.dedup_by(|a, b| a.name == b.name && a.addr == b.addr);

    let warnings = [
      (lines.is_empty(), "no C debug line info found; break/next/step will be limited."),
      (debug.missing_line_addrs, "some #line entries lack addresses; rebuild with the updated assembler."),
      (locals_by_addr.is_empty(), "no C local debug info found; info locals will be empty."),
      (debug.missing_local_addrs, "some #local entries lack addresses; rebuild with the updated assembler."),
      (debug.missing_local_sizes, "some #local entries lack sizes; defaulting to 4-byte reads."),
    ];
    for (present, text) in warnings {
      if present {
        println!("Warning: {}", text);
      }
    }

    let mut breakpoints: HashSet<u32> = HashSet::new();
    let mut cpu = Emulator::from_image(&image);
    let show_location = |_: &mut Emulator, addr: u32| print_c_location(addr, line_for_pc(&lines, addr));
    // Breakpoint line numbers without a file refer to the current file, or
    // to the only file when there is exactly one.
    let default_file = |pc: u32| {
      line_for_pc(&lines, pc)
        .map(|line| line.file.clone())
        .or_else(|| (line_index.len() == 1).then(|| line_index.keys().next().unwrap().clone()))
    };

    println!("C debug mode:\n{}", C_HELP);
    while let Some(line) = read_command() {
      let mut parts = line.split_whitespace();
      let cmd = parts.next().unwrap();
      match cmd {
        "q" | "quit" => break,
        "h" | "help" => println!("Commands:\n{}", C_HELP),
        "r" | "c" => {
          if cmd == "r" {
            cpu = Emulator::from_image(&image);
          }
          let outcome = run_until_breakpoint(&mut cpu, &breakpoints, cmd == "c");
          report_run(outcome, &mut cpu, show_location);
        }
        "step" | "s" | "next" | "n" => {
          if cpu.halted {
            println!("Program already halted.");
            continue;
          }
          step_source_line(&mut cpu, &lines, &breakpoints, matches!(cmd, "next" | "n"));
          if cpu.halted {
            println!("Program halted. r1 = {:08X}", cpu.regfile[1]);
          } else {
            print_c_location(cpu.pc, line_for_pc(&lines, cpu.pc));
          }
        }
        "break" | "b" | "delete" | "del" => {
          let adding = matches!(cmd, "break" | "b");
          let Some(token) = parts.next() else {
            println!("Usage: {} <line|file:line|label|*addr>", if adding { "break" } else { "delete" });
            continue;
          };
          let file = default_file(cpu.pc);
          match resolve_break_targets_c(token, labels, &line_index, file.as_deref()) {
            Ok(addrs) => {
              let changed = addrs
                .into_iter()
                .filter(|addr| if adding { breakpoints.insert(*addr) } else { breakpoints.remove(addr) })
                .count();
              match (adding, changed) {
                (true, 0) => println!("No new breakpoints set."),
                (true, n) => println!("Breakpoints set: {}", n),
                (false, 0) => println!("No matching breakpoints."),
                (false, n) => println!("Breakpoints removed: {}", n),
              }
            }
            Err(msg) => println!("{}", msg),
          }
        }
        "breaks" => list_breakpoints(&breakpoints, |addr| match line_for_pc(&lines, addr) {
          Some(line) => format!("{:08X} ({}:{})", addr, line.file, line.line),
          None => format!("{:08X}", addr),
        }),
        "info" => match parts.next() {
          Some("locals") => print_locals(&cpu, &locals_by_addr, &function_entries),
          Some("globals") => {
            if globals.is_empty() {
              println!("No global debug symbols found.");
            }
            for global in &globals {
              println!("{} @ {:08X} = {:08X}", global.name, global.addr, cpu.read_debug32(global.addr));
            }
          }
          _ => println!("Usage: info <locals|globals>"),
        },
        _ => println!("Unknown command: {}", cmd),
      }
    }
    Ok(())
  }
}

// Step until the source line changes or a breakpoint or halt is reached.
// With `step_over`, instructions executed in a deeper frame (bp differs from
// the starting bp) never end the step.
fn step_source_line(cpu: &mut Emulator, lines: &[DebugLine], breakpoints: &HashSet<u32>, step_over: bool) {
  let start_line = line_for_pc(lines, cpu.pc);
  let start_bp = cpu.get_reg(BP_REG);
  for _ in 0..MAX_STEP_INSTRUCTIONS {
    cpu.step();
    if breakpoints.contains(&cpu.pc) {
      return;
    }
    if step_over && cpu.get_reg(BP_REG) != start_bp {
      continue;
    }
    if start_line.is_none() || !same_source_line(start_line, line_for_pc(lines, cpu.pc)) || cpu.halted {
      return;
    }
  }
  println!("Warning: step limit reached without leaving the current line.");
}

// Print the C locals in scope at the current PC, read relative to bp.
fn print_locals(cpu: &Emulator, locals_by_addr: &[(u32, Vec<DebugLocal>)], function_entries: &[u32]) {
  let Some(locals) = locals_for_pc(locals_by_addr, function_entries, cpu.pc) else {
    let first = function_range_for_pc(function_entries, cpu.pc)
      .and_then(|(start, end)| first_locals_addr_in_range(locals_by_addr, start, end));
    match first {
      Some(first_addr) if cpu.pc < first_addr => println!(
        "Locals are not available yet; enter the function body (after prologue at {:08X}).",
        first_addr
      ),
      _ => println!("No local variables found for current location."),
    }
    return;
  };
  let bp = i64::from(cpu.get_reg(BP_REG));
  for local in locals {
    let name = display_local_name(&local.name);
    let Ok(addr) = u32::try_from(bp + i64::from(local.offset)) else {
      println!("{} @ <invalid> (offset {:+}, size {})", name, local.offset, local.size);
      continue;
    };
    let bytes: Vec<u8> = (0..local.size).map(|i| cpu.read_debug8(addr.wrapping_add(i))).collect();
    println!(
      "{} @ {:08X} (offset {:+}, size {}) = {}",
      name,
      addr,
      local.offset,
      local.size,
      format_bytes(&bytes)
    );
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  // Accept explicit hex, implicit hex with letters, and decimal addresses.
  #[test]
  fn parse_addr_accepts_hex_and_dec() {
    assert_eq!(parse_addr("0x10"), Some(0x10));
    assert_eq!(parse_addr("0X20"), Some(0x20));
    assert_eq!(parse_addr("10"), Some(10));
    assert_eq!(parse_addr("FF"), Some(0xFF));
    assert_eq!(parse_addr("not-a-number"), None);
  }

  // Merge read and write watchpoints at one address into a single read/write entry.
  #[test]
  fn watchpoint_merge_upgrades_kind() {
    let mut list = Vec::new();
    add_watchpoint(&mut list, 0x10, WatchKind::Read);
    let merged = add_watchpoint(&mut list, 0x10, WatchKind::Write);
    assert_eq!(merged, WatchKind::ReadWrite);
    assert_eq!(list.len(), 1);
  }

  // Accept every documented watchpoint selector and reject unknown ones.
  #[test]
  fn parse_watch_kind_variants() {
    assert_eq!(parse_watch_kind("r"), Some(WatchKind::Read));
    assert_eq!(parse_watch_kind("w"), Some(WatchKind::Write));
    assert_eq!(parse_watch_kind("rw"), Some(WatchKind::ReadWrite));
    assert_eq!(parse_watch_kind("wr"), Some(WatchKind::ReadWrite));
    assert_eq!(parse_watch_kind("x"), None);
  }

  // Register names and aliases resolve before `info` falls back to addresses.
  #[test]
  fn register_tokens_resolve_before_addresses() {
    assert!(matches!(Emulator::parse_register("bp"), Some((_, DebugReg::Gpr(30)))));
    assert!(matches!(Emulator::parse_register("R7"), Some((_, DebugReg::Gpr(7)))));
    assert!(Emulator::parse_register("r32").is_none());
  }

  // Binary-search helpers find the nearest entry at or below a PC.
  #[test]
  fn function_range_brackets_pc() {
    let entries = [0x100, 0x200, 0x300];
    assert_eq!(function_range_for_pc(&entries, 0x0FF), None);
    assert_eq!(function_range_for_pc(&entries, 0x100), Some((0x100, Some(0x200))));
    assert_eq!(function_range_for_pc(&entries, 0x3FF), Some((0x300, None)));
  }
}
