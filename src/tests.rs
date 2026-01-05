
#[cfg(test)]
use std::fs;

#[cfg(test)]
use std::path::{Path, PathBuf};

#[cfg(test)]
use std::process::Command;

#[cfg(test)]
use std::sync::Once;

#[cfg(test)]
use super::*;

#[cfg(test)]
fn assembler_profile() -> &'static str {
  // Match the assembler build to the test binary profile.
  if cfg!(debug_assertions) {
    "debug"
  } else {
    "release"
  }
}

#[cfg(test)]
fn build_assembler() {
  static BUILD: Once = Once::new();
  BUILD.call_once(|| {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let asm_dir = manifest.join("../../Dioptase-Assembler");
    // Build the assembler once so tests can run in clean environments.
    let status = Command::new("make")
      .arg(assembler_profile())
      .current_dir(asm_dir)
      .status()
      .expect("failed to run make for assembler");
    assert!(status.success(), "assembler build failed");
  });
}

#[cfg(test)]
fn assembler_path() -> PathBuf {
  let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
  let path = manifest
    .join("../../Dioptase-Assembler")
    .join("build")
    .join(assembler_profile())
    .join("basm");
  if path.exists() {
    return path;
  }
  // Build on-demand if the binary isn't present yet.
  build_assembler();
  assert!(path.exists(), "assembler not found at {}", path.display());
  path
}

#[cfg(test)]
fn ensure_hex_dir() {
  let hex_dir = Path::new("tests/hex");
  fs::create_dir_all(hex_dir).expect("failed to create tests/hex dir");
}

#[cfg(test)]
fn run_test(asm_file : &'static str, expected : u32){
  ensure_hex_dir();

  // Build hex file path by replacing asm path prefix/suffix
  let hex_file = {
    let asm_path = Path::new(asm_file);
    let stem = asm_path.file_stem().unwrap(); // e.g., "add"
    PathBuf::from("tests/hex").join(format!("{}.hex", stem.to_string_lossy()))
  };

  // assemble test case
  let assembler = assembler_path();
  let status = Command::new(&assembler)
    .args([asm_file, "-o", hex_file.to_str().unwrap()])
    .status()
    .expect("failed to run assembler");
  assert!(status.success(), "assembler failed");

  // execute hex/ELF file emitted by the assembler
  let mut cpu = Emulator::new(hex_file.to_string_lossy().to_string());
  let result = cpu.run(0);

  // check result
  assert_eq!(result, Some(expected));
}

#[cfg(test)]
fn run_test_expect_panic(asm_file: &'static str) {
  ensure_hex_dir();

  let hex_file = {
    let asm_path = Path::new(asm_file);
    let stem = asm_path.file_stem().unwrap();
    PathBuf::from("tests/hex").join(format!("{}.hex", stem.to_string_lossy()))
  };

  let assembler = assembler_path();
  let status = Command::new(&assembler)
    .args([asm_file, "-o", hex_file.to_str().unwrap()])
    .status()
    .expect("failed to run assembler");
  assert!(status.success(), "assembler failed");

  let result = std::panic::catch_unwind(|| {
    let mut cpu = Emulator::new(hex_file.to_string_lossy().to_string());
    let _ = cpu.run(0);
  });

  assert!(result.is_err(), "expected emulator to panic");
}

#[test]
fn and() {
  run_test("tests/asm/and.s", 2);
}

#[test]
fn nand() {
  run_test("tests/asm/nand.s", 0xFFFFFFFA);
}

#[test]
fn or() {
  run_test("tests/asm/or.s", 0xF000000F);
}

#[test]
fn nor() {
  run_test("tests/asm/nor.s", 6);
}

#[test]
fn xor() {
  run_test("tests/asm/xor.s", 25);
}

#[test]
fn xnor() {
  run_test("tests/asm/xnor.s", 13);
}

#[test]
fn not() {
  run_test("tests/asm/not.s", 1);
}

#[test]
fn lsl() {
  run_test("tests/asm/lsl.s", 0x55550);
}

#[test]
fn lsr() {
  run_test("tests/asm/lsr.s", 0xAAA);
}

#[test]
fn asr() {
  run_test("tests/asm/asr.s", 0xF5555555);
}

#[test]
fn lslc() {
  run_test("tests/asm/lslc.s", 0x143);
}

#[test]
fn lsrc() {
  run_test("tests/asm/lsrc.s", 0xC0000028);
}

#[test]
fn add() {
  run_test("tests/asm/add.s", 38);
}

#[test]
fn addc() {
  run_test("tests/asm/addc.s", 0xAAAAAAAD);
}

#[test]
fn sub() {
  run_test("tests/asm/sub.s", 8);
}

#[test]
fn subb() {
  run_test("tests/asm/subb.s", 0xFFFFFFFF);
}

#[test]
fn sub_overflow_sets_flag() {
  run_test("tests/asm/sub_overflow.s", 1);
}

#[test]
fn sxtb() {
  run_test("tests/asm/sxtb.s", 0x000000FF);
}

#[test]
fn sxtd() {
  run_test("tests/asm/sxtd.s", 0x0000FFFF);
}

#[test]
fn tncb() {
  run_test("tests/asm/tncb.s", 0x00000081);
}

#[test]
fn tncd() {
  run_test("tests/asm/tncd.s", 0x00008001);
}

#[test]
fn lui() {
  run_test("tests/asm/lui.s", 0xAA000000);
}

#[test]
fn movi() {
  run_test("tests/asm/movi.s", 0xABABABAB);
}

#[test]
fn mem_wa() {
  run_test("tests/asm/mem_wa.s", 0x42424242);
}

#[test]
fn mem_wr() {
  run_test("tests/asm/mem_wr.s", 0x25);
}

#[test]
fn mem_da() {
  run_test("tests/asm/mem_da.s", 0x4242);
}

#[test]
fn mem_dr() {
  run_test("tests/asm/mem_dr.s", 0x11114444);
}

#[test]
fn mem_ba() {
  run_test("tests/asm/mem_ba.s", 0x42);
}

#[test]
fn mem_br() {
  run_test("tests/asm/mem_br.s", 0x11111144);
}

#[test]
fn atomic_fadd() {
  run_test("tests/asm/atomic_fadd.s", 0x6D);
}

#[test]
fn atomic_swap() {
  run_test("tests/asm/atomic_swap.s", 0x164);
}

#[test]
fn r0_load_invariant() {
  run_test("tests/asm/r0_load_invariant.s", 0);
}

#[test]
fn inc() {
  run_test("tests/asm/inc.s", 0xFFFF);
}

#[test]
fn stack() {
  run_test("tests/asm/stack.s", 0x123456);
}

#[test]
fn ba() {
  run_test("tests/asm/ba.s", 1);
}

#[test]
fn bae() {
  run_test("tests/asm/bae.s", 1);
}

#[test]
fn bb() {
  run_test("tests/asm/bb.s", 1);
}

#[test]
fn bbe() {
  run_test("tests/asm/bbe.s", 1);
}

#[test]
fn bc() {
  run_test("tests/asm/bc.s", 1);
}

#[test]
fn bz() {
  run_test("tests/asm/bz.s", 1);
}


#[test]
fn bg() {
  run_test("tests/asm/bg.s", 1);
}

#[test]
fn bge() {
  run_test("tests/asm/bge.s", 1);
}

#[test]
fn bl() {
  run_test("tests/asm/bl.s", 2);
}

#[test]
fn ble() {
  run_test("tests/asm/ble.s", 3);
}

#[test]
fn bs() {
  run_test("tests/asm/bs.s", 2);
}

#[test]
fn bnc() {
  run_test("tests/asm/bnc.s", 0);
}

#[test]
fn bnz() {
  run_test("tests/asm/bnz.s", 0);
}

#[test]
fn bo() {
  run_test("tests/asm/bo.s", 0);
}

#[test]
fn bps() {
  run_test("tests/asm/bps.s", 0);
}

#[test]
fn jmp() {
  run_test("tests/asm/jmp.s", 0);
}

#[test]
fn call() {
  run_test("tests/asm/call.s", 42);
}

#[test]
fn origin() {
  run_test("tests/asm/origin.s", 21);
}

#[test]
fn bad_write_rodata_panics() {
  run_test_expect_panic("tests/asm/bad_rodata_write.s");
}

#[test]
fn bad_exec_data_panics() {
  run_test_expect_panic("tests/asm/bad_exec_data.s");
}
