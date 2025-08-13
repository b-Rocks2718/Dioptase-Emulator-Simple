use std::process::Command;

#[cfg(test)]

use super::*;

#[test]
fn add_two_numbers() {
  let asm_file = "tests/asm/test.s";
  let hex_file = "tests/hex/test.hex";

  // 1. Assemble
  let status = Command::new("../../Dioptase-Assembler/build/assembler")
    .args([asm_file, "-o", hex_file])
    .status()
    .expect("failed to run assembler");
  assert!(status.success(), "assembler failed");

  let mut cpu = Emulator::new(String::from(hex_file));
  let result = cpu.run();
  assert_eq!(result, 14);
}
