use std::env;
use std::process;

pub mod emulator;
pub mod tests;
pub mod disassembler;

use emulator::Emulator;

fn main() {
  let args = env::args().collect::<Vec<_>>();

  let mut debug = false;
  let mut max_cycles: u32 = 0;
  let mut path: Option<String> = None;

  let mut iter = args.iter().skip(1).peekable();
  while let Some(arg) = iter.next() {
    match arg.as_str() {
      "--debug" => debug = true,
      "--max-cycles" => {
        let value = iter.next().unwrap_or_else(|| {
          println!("Missing value for --max-cycles");
          process::exit(1);
        });
        max_cycles = value.parse::<u32>().unwrap_or_else(|_| {
          println!("Invalid max cycle count: {}", value);
          process::exit(1);
        });
      }
      _ if arg.starts_with("--max-cycles=") => {
        let value = &arg["--max-cycles=".len()..];
        max_cycles = value.parse::<u32>().unwrap_or_else(|_| {
          println!("Invalid max cycle count: {}", value);
          process::exit(1);
        });
      }
      _ if arg.starts_with('-') => {
        println!("Unknown flag: {}", arg);
        process::exit(1);
      }
      _ => {
        if path.is_none() {
          path = Some(arg.clone());
        } else {
          println!("Usage: cargo run -- <file>.hex [--debug] [--max-cycles N]");
          process::exit(1);
        }
      }
    }
  }

  if let Some(path) = path {
    if debug {
      if max_cycles != 0 {
        println!("Warning: --max-cycles is ignored in debug mode");
      }
      Emulator::debug(path);
    } else {
      let mut cpu = Emulator::new(path);
      let result = cpu.run(max_cycles).expect("did not terminate"); // programs should return a value in r3
      println!("{:08x}", result);
    }
  } else {
    println!("Usage: cargo run -- <file>.hex [--debug] [--max-cycles N]");
    process::exit(1);
  }
}
