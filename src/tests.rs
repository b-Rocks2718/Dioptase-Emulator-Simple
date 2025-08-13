
#[cfg(test)]
use std::process::Command;

#[cfg(test)]
use std::path::{Path, PathBuf};

#[cfg(test)]
use super::*;

#[cfg(test)]
fn run_test(asm_file : &'static str, expected : u32){

  // Build hex file path by replacing asm path prefix/suffix
  let hex_file = {
    let asm_path = Path::new(asm_file);
    let stem = asm_path.file_stem().unwrap(); // e.g., "add"
    PathBuf::from("tests/hex").join(format!("{}.hex", stem.to_string_lossy()))
  };

  // assemble test case
  let status = Command::new("../../Dioptase-Assembler/build/assembler")
    .args([asm_file, "-o", hex_file.to_str().unwrap()])
    .status()
    .expect("failed to run assembler");
  assert!(status.success(), "assembler failed");

  // execute hex file
  let mut cpu = Emulator::new(hex_file.to_string_lossy().to_string());
  let result = cpu.run();

  // check result
  assert_eq!(result, expected);
}

#[test]
fn add() {
  run_test("tests/asm/add.s", 42);
}

#[test]
fn addc() {
  run_test("tests/asm/addc.s", 0xAAAAAAAC);
}

#[test]
fn sub() {
  run_test("tests/asm/sub.s", 0xFFFFFFF9);
}

#[test]
fn subb() {
  run_test("tests/asm/subb.s", 0xFFFFFFFF);
}

#[test]
fn and() {
  run_test("tests/asm/and.s", 2);
}

#[test]
fn nand() {
  run_test("tests/asm/nand.s", 0xFFFFFFFD);
}

#[test]
fn not() {
  run_test("tests/asm/not.s", 2);
}

#[test]
fn or() {
  run_test("tests/asm/or.s", 14);
}

#[test]
fn xor() {
  run_test("tests/asm/xor.s", 29);
}

#[test]
fn lsl() {
  run_test("tests/asm/lsl.s", 0x55550);
}

#[test]
fn lui() {
  run_test("tests/asm/lui.s", 0xAA000000);
}

#[test]
fn movi() {
  run_test("tests/asm/movi.s", 0xABABABAB);
}


