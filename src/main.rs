use std::env;
use std::process;

pub mod disassembler;
pub mod emulator;
#[cfg(test)]
mod tests;

use emulator::Emulator;

const USAGE: &str = "Usage: cargo run -- <file>.hex [--debug|--debugc] [--max-cycles N]";

// Print an error and exit with status 1.
fn fail(message: impl std::fmt::Display) -> ! {
  println!("{}", message);
  process::exit(1);
}

// Parse command-line options, load a program image, and run the emulator.
fn main() {
  let args = env::args().collect::<Vec<_>>();
  let (mut debug, mut debugc) = (false, false);
  let mut max_cycles: u32 = 0;
  let mut path: Option<String> = None;

  let mut iter = args.iter().skip(1);
  while let Some(arg) = iter.next() {
    let (flag, inline_value) = match arg.split_once('=') {
      Some((flag, value)) if arg.starts_with("--") => (flag, Some(value.to_string())),
      _ => (arg.as_str(), None),
    };
    match flag {
      "--debug" => debug = true,
      "--debugc" => debugc = true,
      "--max-cycles" => {
        let value = inline_value
          .or_else(|| iter.next().cloned())
          .unwrap_or_else(|| fail("Missing value for --max-cycles"));
        max_cycles = value
          .parse()
          .unwrap_or_else(|_| fail(format!("Invalid max cycle count: {}", value)));
      }
      _ if flag.starts_with('-') => fail(format!("Unknown flag: {}", arg)),
      _ if path.is_none() => path = Some(arg.clone()),
      _ => fail(USAGE),
    }
  }

  let path = path.unwrap_or_else(|| fail(USAGE));
  if debug && debugc {
    fail("Error: --debug and --debugc are mutually exclusive");
  }
  if debug || debugc {
    let mode = if debugc { "debugc" } else { "debug" };
    if max_cycles != 0 {
      println!("Warning: --max-cycles is ignored in {} mode", mode);
    }
    let debugger = if debugc { Emulator::debug_c } else { Emulator::debug };
    debugger(&path).unwrap_or_else(|err| fail(err));
    return;
  }
  let mut cpu = Emulator::new(&path).unwrap_or_else(|err| fail(err));
  // Programs return a value in r1; a missing result means the cycle budget ran out.
  let result = cpu.run(max_cycles).expect("did not terminate");
  println!("{:08x}", result);
}
