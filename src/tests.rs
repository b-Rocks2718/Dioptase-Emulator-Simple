use std::process::Command;

#[cfg(test)]

use super::*;

#[test]
fn test() {
  let asm_file = "tests/asm/test.s";
  let hex_file = "tests/hex/test.hex";
  let expected = 14;

  // assemble test case
  let status = Command::new("../../Dioptase-Assembler/build/assembler")
    .args([asm_file, "-o", hex_file])
    .status()
    .expect("failed to run assembler");
  assert!(status.success(), "assembler failed");

  // execute hex file
  let mut cpu = Emulator::new(String::from(hex_file));
  let result = cpu.run();

  // check result
  assert_eq!(result, expected);
}
