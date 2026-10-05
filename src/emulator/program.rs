// Loader for assembler output and the debug metadata embedded in it.
//
// Accepted text formats (one little-endian 32-bit hex word per line):
// - `@<word address>` origin lines present: words load at the cursor and every
//   address is readable, writable, and executable; the entry is the first word.
// - plain words beginning with the ELF magic: a pseudo-ELF image whose PT_LOAD
//   segments define the only accessible memory, with ELF p_flags permissions.
// - other plain words: loaded from address 0 with full permissions.
// `;`/`//` lines are comments; `#`-prefixed lines carry `-g`/`--debug`
// metadata:
//   #label <name> <addr>
//   #line  <file> <line> <addr>
//   #local <name> <bp offset> [<size>] <addr>
//   #data  <name> <addr>

use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead};

// "\x7FELF" read as a little-endian word.
const ELF_MAGIC: u32 = 0x464C_457F;
// ELF32 header field offsets.
const ELF_ENTRY_OFFSET: usize = 24;
const ELF_PHOFF_OFFSET: usize = 28;
const ELF_PHENTSIZE_OFFSET: usize = 42;
const ELF_PHNUM_OFFSET: usize = 44;
// Smallest valid ELF32 program header.
const ELF_MIN_PHENTSIZE: usize = 32;
const ELF_PT_LOAD: u32 = 1;

// Label -> address list (labels can appear multiple times across sections).
pub(super) type LabelMap = HashMap<String, Vec<u32>>;

// Source line marker emitted by the assembler debug pipeline.
#[derive(Clone, Debug)]
pub(super) struct DebugLine {
  pub file: String,
  pub line: u32,
  pub addr: u32,
}

// Stack local debug metadata anchored to a code address.
#[derive(Clone, Debug)]
pub(super) struct DebugLocal {
  pub name: String,
  pub offset: i32,
  pub size: u32,
}

// Global data symbol debug metadata.
#[derive(Clone, Debug)]
pub(super) struct DebugGlobal {
  pub name: String,
  pub addr: u32,
}

// Aggregated C debug info. The `missing_*` flags record metadata from older
// assemblers that omitted fields, so the C debugger can warn about it.
#[derive(Clone, Debug, Default)]
pub(super) struct DebugInfo {
  pub lines: Vec<DebugLine>,
  pub locals_by_addr: HashMap<u32, Vec<DebugLocal>>,
  pub globals: Vec<DebugGlobal>,
  pub missing_line_addrs: bool,
  pub missing_local_addrs: bool,
  pub missing_local_sizes: bool,
}

// Memory permissions (ELF p_flags: R=4, W=2, X=1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct MemPerm {
  pub read: bool,
  pub write: bool,
  pub exec: bool,
}

impl MemPerm {
  // Convert ELF p_flags bits to permissions.
  fn from_elf_flags(flags: u32) -> MemPerm {
    MemPerm {
      read: flags & 4 != 0,
      write: flags & 2 != 0,
      exec: flags & 1 != 0,
    }
  }
}

pub(super) const PERM_RWX: MemPerm = MemPerm { read: true, write: true, exec: true };
pub(super) const PERM_RW: MemPerm = MemPerm { read: true, write: true, exec: false };
const PERM_NONE: MemPerm = MemPerm { read: false, write: false, exec: false };

// A contiguous loaded memory range and its permissions.
#[derive(Clone, Debug)]
pub(super) struct MemoryRegion {
  pub base: u32,
  pub size: u32,
  pub perm: MemPerm,
}

impl MemoryRegion {
  // Whether `addr` falls inside the region (computed in 64 bits so a region
  // ending at the top of the address space works).
  pub fn contains(&self, addr: u32) -> bool {
    let start = u64::from(self.base);
    (start..start + u64::from(self.size)).contains(&u64::from(addr))
  }
}

// Loader output: initial bytes, labels, entry point, and memory permissions.
// Addresses outside every region get `default_perm`.
#[derive(Clone)]
pub(super) struct ProgramImage {
  pub bytes: HashMap<u32, u8>,
  pub labels: LabelMap,
  pub entry: u32,
  pub regions: Vec<MemoryRegion>,
  pub default_perm: MemPerm,
  pub debug: DebugInfo,
}

// Parse a hexadecimal 32-bit word, with or without a 0x prefix.
fn parse_hex_u32(token: &str) -> Option<u32> {
  let s = token.trim();
  let s = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")).unwrap_or(s);
  if s.is_empty() {
    return None;
  }
  u32::from_str_radix(s, 16).ok()
}

// Parse a "#label <name> <addr>" line into `labels`; returns whether it was one.
fn parse_label_line(line: &str, labels: &mut LabelMap) -> bool {
  let mut parts = line.split_whitespace();
  if parts.next() != Some("#label") {
    return false;
  }
  let (Some(name), Some(addr)) = (parts.next(), parts.next().and_then(parse_hex_u32)) else {
    return false;
  };
  let entry = labels.entry(name.to_string()).or_default();
  if !entry.contains(&addr) {
    entry.push(addr);
  }
  true
}

// Parse a `#line`, `#local`, or `#data` line into `debug`; returns whether the
// line used one of those tags (malformed entries are recorded as missing data).
fn parse_debug_line(line: &str, debug: &mut DebugInfo) -> bool {
  const DEFAULT_LOCAL_SIZE_BYTES: u32 = 4;
  let mut parts = line.split_whitespace();
  match parts.next() {
    Some("#line") => {
      let (Some(file), Some(line_str)) = (parts.next(), parts.next()) else {
        return true;
      };
      match (line_str.parse::<u32>(), parts.next().and_then(parse_hex_u32)) {
        (Ok(line), Some(addr)) => debug.lines.push(DebugLine { file: file.to_string(), line, addr }),
        _ => debug.missing_line_addrs = true,
      }
      true
    }
    Some("#local") => {
      let (Some(name), Some(offset_str)) = (parts.next(), parts.next()) else {
        return true;
      };
      let Ok(offset) = offset_str.parse::<i32>() else {
        debug.missing_local_addrs = true;
        return true;
      };
      // Older assemblers emitted "#local <name> <offset> <addr>" with no size.
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
        [size_str, addr_str, ..] => match size_str.parse::<u32>() {
          Ok(size) if size > 0 => (size, *addr_str),
          _ => {
            debug.missing_local_sizes = true;
            (DEFAULT_LOCAL_SIZE_BYTES, *addr_str)
          }
        },
      };
      let Some(addr) = parse_hex_u32(addr_str) else {
        debug.missing_local_addrs = true;
        return true;
      };
      debug.locals_by_addr.entry(addr).or_default().push(DebugLocal { name: name.to_string(), offset, size });
      true
    }
    Some("#data") => {
      let (Some(name), Some(addr)) = (parts.next(), parts.next().and_then(parse_hex_u32)) else {
        return true;
      };
      if !debug.globals.iter().any(|g| g.name == name && g.addr == addr) {
        debug.globals.push(DebugGlobal { name: name.to_string(), addr });
      }
      true
    }
    _ => false,
  }
}

// One non-metadata line of the image.
enum ImageLine {
  Origin(u32),
  Word(u32),
}

// Little-endian u16/u32 readers over the ELF byte image.
fn elf_u16(bytes: &[u8], offset: usize, path: &str) -> Result<u16, String> {
  bytes
    .get(offset..offset + 2)
    .map(|b| u16::from_le_bytes([b[0], b[1]]))
    .ok_or_else(|| format!("Loader: ELF image {} is truncated at byte {}", path, offset))
}
fn elf_u32(bytes: &[u8], offset: usize, path: &str) -> Result<u32, String> {
  bytes
    .get(offset..offset + 4)
    .map(|b| u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    .ok_or_else(|| format!("Loader: ELF image {} is truncated at byte {}", path, offset))
}

// Store a little-endian word at `addr`.
fn insert_word(bytes: &mut HashMap<u32, u8>, addr: u32, word: u32) {
  for (offset, byte) in word.to_le_bytes().into_iter().enumerate() {
    bytes.insert(addr.wrapping_add(offset as u32), byte);
  }
}

// Load PT_LOAD segments from a pseudo-ELF byte image.
fn load_elf(bytes: &[u8], path: &str, image: &mut ProgramImage) -> Result<(), String> {
  image.entry = elf_u32(bytes, ELF_ENTRY_OFFSET, path)?;
  image.default_perm = PERM_NONE;
  let phoff = elf_u32(bytes, ELF_PHOFF_OFFSET, path)? as usize;
  let phentsize = elf_u16(bytes, ELF_PHENTSIZE_OFFSET, path)? as usize;
  let phnum = elf_u16(bytes, ELF_PHNUM_OFFSET, path)? as usize;
  if phentsize < ELF_MIN_PHENTSIZE {
    return Err(format!(
      "Loader: ELF image {} has program header size {}, expected at least {}",
      path, phentsize, ELF_MIN_PHENTSIZE
    ));
  }
  for index in 0..phnum {
    let header = phoff + index * phentsize;
    if elf_u32(bytes, header, path)? != ELF_PT_LOAD {
      continue;
    }
    let offset = elf_u32(bytes, header + 4, path)? as usize;
    let vaddr = elf_u32(bytes, header + 8, path)?;
    let filesz = elf_u32(bytes, header + 16, path)?;
    let memsz = elf_u32(bytes, header + 20, path)?;
    let flags = elf_u32(bytes, header + 24, path)?;
    if memsz < filesz {
      return Err(format!(
        "Loader: ELF image {} segment {} has memsz 0x{:X} < filesz 0x{:X}",
        path, index, memsz, filesz
      ));
    }
    let data = bytes.get(offset..offset + filesz as usize).ok_or_else(|| {
      format!("Loader: ELF image {} segment {} data lies outside the file", path, index)
    })?;
    for (i, byte) in data.iter().enumerate() {
      image.bytes.insert(vaddr.wrapping_add(i as u32), *byte);
    }
    if memsz != 0 {
      image.regions.push(MemoryRegion { base: vaddr, size: memsz, perm: MemPerm::from_elf_flags(flags) });
    }
  }
  Ok(())
}

// Load an image in any of the formats described at the top of this file.
pub(super) fn load_program(path: &str) -> Result<ProgramImage, String> {
  let file = File::open(path).map_err(|err| format!("Loader: failed to open program image {}: {}", path, err))?;
  let mut image = ProgramImage {
    bytes: HashMap::new(),
    labels: LabelMap::new(),
    entry: 0,
    regions: Vec::new(),
    default_perm: PERM_RWX,
    debug: DebugInfo::default(),
  };
  let mut lines = Vec::new();
  for (index, line) in io::BufReader::new(file).lines().enumerate() {
    let line_no = index + 1;
    let line = line.map_err(|err| format!("Loader: failed to read {} line {}: {}", path, line_no, err))?;
    let line = line.trim();
    if line.is_empty() || line.starts_with(';') || line.starts_with("//") {
      continue;
    }
    if line.starts_with('#') {
      parse_label_line(line, &mut image.labels);
      parse_debug_line(line, &mut image.debug);
      continue;
    }
    let (text, is_origin) = match line.strip_prefix('@') {
      Some(rest) => (rest.trim(), true),
      None => (line, false),
    };
    let value = u32::from_str_radix(text, 16).map_err(|_| {
      format!("Loader: expected a 32-bit hex {} at {}:{}, found '{}'",
        if is_origin { "word address after '@'" } else { "word" }, path, line_no, line)
    })?;
    lines.push(if is_origin { ImageLine::Origin(value) } else { ImageLine::Word(value) });
  }

  if lines.iter().any(|line| matches!(line, ImageLine::Origin(_))) {
    let mut addr: u32 = 0;
    let mut entry = None;
    for line in lines {
      match line {
        ImageLine::Origin(word_addr) => addr = word_addr.wrapping_mul(4),
        ImageLine::Word(word) => {
          entry.get_or_insert(addr);
          insert_word(&mut image.bytes, addr, word);
          addr = addr.wrapping_add(4);
        }
      }
    }
    image.entry = entry.unwrap_or(0);
    return Ok(image);
  }

  let words: Vec<u32> = lines
    .into_iter()
    .map(|line| match line {
      ImageLine::Word(word) => word,
      ImageLine::Origin(_) => unreachable!("origin images were handled above"),
    })
    .collect();
  match words.first() {
    // An empty image has no accessible memory at all.
    None => image.default_perm = PERM_NONE,
    Some(&ELF_MAGIC) => {
      let bytes: Vec<u8> = words.iter().flat_map(|word| word.to_le_bytes()).collect();
      load_elf(&bytes, path, &mut image)?;
    }
    Some(_) => {
      for (index, word) in words.iter().enumerate() {
        insert_word(&mut image.bytes, index as u32 * 4, *word);
      }
    }
  }
  Ok(image)
}
