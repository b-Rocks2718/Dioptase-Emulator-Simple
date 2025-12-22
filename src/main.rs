use std::env;
use std::process;

pub mod emulator;
pub mod tests;
pub mod disassembler;

use emulator::Emulator;

fn main() {
  let args = env::args().collect::<Vec<_>>();

  let mut debug = false;
  let mut path: Option<String> = None;

  for arg in args.iter().skip(1) {
    match arg.as_str() {
      "--debug" => debug = true,
      _ if arg.starts_with('-') => {
        println!("Unknown flag: {}", arg);
        process::exit(1);
      }
      _ => {
        if path.is_none() {
          path = Some(arg.clone());
        } else {
          println!("Usage: cargo run -- <file>.hex [--debug]");
          process::exit(1);
        }
      }
    }
  }

  if let Some(path) = path {
    if debug {
      Emulator::debug(path);
    } else {
      let mut cpu = Emulator::new(path);
      let result = cpu.run(); // programs should return a value in r3
      println!("{:08x}", result);
    }
  } else {
    println!("Usage: cargo run -- <file>.hex [--debug]");
    process::exit(1);
  }
}
