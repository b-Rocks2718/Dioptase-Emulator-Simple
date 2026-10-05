// Instruction-level regression tests: each fixture in tests/asm is assembled
// with the sibling Dioptase-Assembler checkout into a user-mode image and run
// until its exit trap; the test checks the r1 value the program returns.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Once;

use crate::emulator::Emulator;

// Assembler build profile matching the test binary profile.
fn assembler_profile() -> &'static str {
  if cfg!(debug_assertions) { "debug" } else { "release" }
}

// Path to the assembler, building it once if it is missing.
fn assembler_path() -> PathBuf {
  static BUILD: Once = Once::new();
  let asm_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../Dioptase-Assembler");
  let path = asm_dir.join("build").join(assembler_profile()).join("basm");
  if !path.exists() {
    BUILD.call_once(|| {
      let status = Command::new("make")
        .arg(assembler_profile())
        .current_dir(&asm_dir)
        .status()
        .expect("failed to run make for assembler");
      assert!(status.success(), "assembler build failed");
    });
  }
  assert!(path.exists(), "assembler not found at {}", path.display());
  path
}

// Assemble a fixture into tests/hex/<stem>.hex and return the image path.
fn assemble(asm_file: &str) -> String {
  fs::create_dir_all("tests/hex").expect("failed to create tests/hex dir");
  let stem = Path::new(asm_file).file_stem().unwrap().to_string_lossy();
  let hex_file = format!("tests/hex/{}.hex", stem);
  let status = Command::new(assembler_path())
    .args([asm_file, "-o", &hex_file])
    .status()
    .expect("failed to run assembler");
  assert!(status.success(), "assembler failed on {}", asm_file);
  hex_file
}

// Load an assembled image, panicking with the loader's message on failure.
fn load(hex_file: &str) -> Emulator {
  Emulator::new(hex_file).unwrap_or_else(|err| panic!("{}", err))
}

// Assemble and run one fixture, expecting `expected` in r1.
fn run_test(asm_file: &'static str, expected: u32) {
  let mut cpu = load(&assemble(asm_file));
  assert_eq!(cpu.run(0), Some(expected), "{} returned the wrong r1", asm_file);
}

// Assemble a fixture and verify that executing it stops the emulator.
fn run_test_expect_panic(asm_file: &'static str) {
  let hex = assemble(asm_file);
  let result = std::panic::catch_unwind(|| load(&hex).run(0));
  assert!(result.is_err(), "{} should stop the emulator with a panic", asm_file);
}

// Check register AND produces the expected bit mask.
#[test]
fn and() {
  run_test("tests/asm/and.s", 2);
}

// Check NAND complements the register AND result.
#[test]
fn nand() {
  run_test("tests/asm/nand.s", 0xFFFFFFFA);
}

// Check register OR combines every set input bit.
#[test]
fn or() {
  run_test("tests/asm/or.s", 0xF000000F);
}

// Check NOR complements the register OR result.
#[test]
fn nor() {
  run_test("tests/asm/nor.s", 6);
}

// Check register XOR preserves bits set in exactly one operand.
#[test]
fn xor() {
  run_test("tests/asm/xor.s", 25);
}

// Check XNOR complements the register XOR result.
#[test]
fn xnor() {
  run_test("tests/asm/xnor.s", 13);
}

// Check NOT complements every bit in its operand.
#[test]
fn not() {
  run_test("tests/asm/not.s", 1);
}

// Check logical left shift inserts zeros at the low end.
#[test]
fn lsl() {
  run_test("tests/asm/lsl.s", 0x55550);
}

// Check logical right shift inserts zeros at the high end.
#[test]
fn lsr() {
  run_test("tests/asm/lsr.s", 0xAAA);
}

// Check arithmetic right shift preserves the sign bit.
#[test]
fn asr() {
  run_test("tests/asm/asr.s", 0xF5555555);
}

// Check left shift through carry consumes and updates the carry bit.
#[test]
fn lslc() {
  run_test("tests/asm/lslc.s", 0x143);
}

// Check right shift through carry consumes and updates the carry bit.
#[test]
fn lsrc() {
  run_test("tests/asm/lsrc.s", 0xC0000028);
}

// Check register addition produces the expected sum.
#[test]
fn add() {
  run_test("tests/asm/add.s", 38);
}

// Check add-with-carry includes the incoming carry bit.
#[test]
fn addc() {
  run_test("tests/asm/addc.s", 0xAAAAAAAD);
}

// Check register subtraction produces the expected difference.
#[test]
fn sub() {
  run_test("tests/asm/sub.s", 8);
}

// Check subtract-with-borrow includes the incoming borrow state.
#[test]
fn subb() {
  run_test("tests/asm/subb.s", 0xFFFFFFFF);
}

// Verify subtraction reports signed overflow through the architectural flag.
#[test]
fn sub_overflow_sets_flag() {
  run_test("tests/asm/sub_overflow.s", 1);
}

// Check byte sign extension preserves the encoded signed value.
#[test]
fn sxtb() {
  run_test("tests/asm/sxtb.s", 0x000000FF);
}

// Check halfword sign extension preserves the encoded signed value.
#[test]
fn sxtd() {
  run_test("tests/asm/sxtd.s", 0x0000FFFF);
}

// Check byte truncation discards only the upper bits.
#[test]
fn tncb() {
  run_test("tests/asm/tncb.s", 0x00000081);
}

// Check halfword truncation discards only the upper bits.
#[test]
fn tncd() {
  run_test("tests/asm/tncd.s", 0x00008001);
}

// Check load-upper-immediate places its payload in the high bits.
#[test]
fn lui() {
  run_test("tests/asm/lui.s", 0xAA000000);
}

// Check the movi pseudo-instruction constructs a full-width constant.
#[test]
fn movi() {
  run_test("tests/asm/movi.s", 0xABABABAB);
}

// Check add-PC forms the expected PC-relative address.
#[test]
fn adpc() {
  run_test("tests/asm/adpc.s", 0);
}

// Verify the swa/lwa register-relative word round trip.
#[test]
fn mem_wa() {
  run_test("tests/asm/mem_wa.s", 0x42424242);
}

// Verify relocated lw/sw accesses preserve neighboring words.
#[test]
fn mem_wr() {
  run_test("tests/asm/mem_wr.s", 0x25);
}

// Verify the sda/lda register-relative halfword round trip.
#[test]
fn mem_da() {
  run_test("tests/asm/mem_da.s", 0x4242);
}

// Verify relocated ld/sd accesses update only the selected halfword.
#[test]
fn mem_dr() {
  run_test("tests/asm/mem_dr.s", 0x11114444);
}

// Verify the sba/lba register-relative byte round trip.
#[test]
fn mem_ba() {
  run_test("tests/asm/mem_ba.s", 0x42);
}

// Verify relocated lb/sb accesses update only the selected byte.
#[test]
fn mem_br() {
  run_test("tests/asm/mem_br.s", 0x11111144);
}

// Verify atomic fetch-add returns the old word and stores the sum.
#[test]
fn atomic_fadd() {
  run_test("tests/asm/atomic_fadd.s", 0x6D);
}

// Verify atomic swap returns the old word and installs the replacement.
#[test]
fn atomic_swap() {
  run_test("tests/asm/atomic_swap.s", 0x164);
}

// Verify memory loads cannot change the architecturally constant r0.
#[test]
fn r0_load_invariant() {
  run_test("tests/asm/r0_load_invariant.s", 0);
}

// Check increment updates the operand by exactly one.
#[test]
fn inc() {
  run_test("tests/asm/inc.s", 0xFFFF);
}

// Check stack pseudo-operations preserve pushed values and stack position.
#[test]
fn stack() {
  run_test("tests/asm/stack.s", 0x123456);
}

// Check unsigned-above branches only when carry and zero permit it.
#[test]
fn ba() {
  run_test("tests/asm/ba.s", 1);
}

// Check unsigned-above-or-equal follows the carry condition.
#[test]
fn bae() {
  run_test("tests/asm/bae.s", 1);
}

// Check unsigned-below follows the inverse carry condition.
#[test]
fn bb() {
  run_test("tests/asm/bb.s", 1);
}

// Check unsigned-below-or-equal includes equality.
#[test]
fn bbe() {
  run_test("tests/asm/bbe.s", 1);
}

// Check branch-on-carry observes the carry flag.
#[test]
fn bc() {
  run_test("tests/asm/bc.s", 1);
}

// Check branch-on-zero observes the zero flag.
#[test]
fn bz() {
  run_test("tests/asm/bz.s", 1);
}


// Check signed-greater branches from the sign/overflow/zero flags.
#[test]
fn bg() {
  run_test("tests/asm/bg.s", 1);
}

// Check signed-greater-or-equal includes equality.
#[test]
fn bge() {
  run_test("tests/asm/bge.s", 1);
}

// Check signed-less branches from differing sign and overflow flags.
#[test]
fn bl() {
  run_test("tests/asm/bl.s", 2);
}

// Check signed-less-or-equal includes equality.
#[test]
fn ble() {
  run_test("tests/asm/ble.s", 3);
}

// Check branch-on-sign observes the sign flag.
#[test]
fn bs() {
  run_test("tests/asm/bs.s", 2);
}

// Check branch-on-no-carry rejects a set carry flag.
#[test]
fn bnc() {
  run_test("tests/asm/bnc.s", 0);
}

// Check branch-on-nonzero rejects a set zero flag.
#[test]
fn bnz() {
  run_test("tests/asm/bnz.s", 0);
}

// Check branch-on-overflow observes the overflow flag.
#[test]
fn bo() {
  run_test("tests/asm/bo.s", 0);
}

// Check branch-on-positive-sign rejects a set sign flag.
#[test]
fn bps() {
  run_test("tests/asm/bps.s", 0);
}

// Check an unconditional jump resumes at its target.
#[test]
fn jmp() {
  run_test("tests/asm/jmp.s", 0);
}

// Check call transfers control and preserves a usable return address.
#[test]
fn call() {
  run_test("tests/asm/call.s", 42);
}

// Check code assembled at a nonzero origin executes with correct addresses.
#[test]
fn origin() {
  run_test("tests/asm/origin.s", 21);
}

// Verify a store to a read-only loaded region is rejected.
#[test]
fn bad_write_rodata_panics() {
  run_test_expect_panic("tests/asm/bad_rodata_write.s");
}

// Verify instruction fetch from a non-executable loaded region is rejected.
#[test]
fn bad_exec_data_panics() {
  run_test_expect_panic("tests/asm/bad_exec_data.s");
}

// Check arithmetic carry propagates through the tested instruction sequence.
#[test]
fn carry() {
  run_test("tests/asm/carry.s", 42);
}

// asr by 0 must not sign-fill the result.
#[test]
fn asr_zero() {
  run_test("tests/asm/asr_zero.s", 0x8000_0010);
}

// Immediate subb must use its immediate as the minuend.
#[test]
fn subb_imm() {
  run_test("tests/asm/subb_imm.s", 42);
}

// Shift amounts above 31 saturate; rotates wrap modulo 32.
#[test]
fn shift_large() {
  run_test("tests/asm/shift_large.s", 2);
}

// ALU-immediate op 18 has no immediate encoding; it used to execute sxtb.
#[test]
fn alu_imm_invalid_panics() {
  run_test_expect_panic("tests/asm/alu_imm_invalid.s");
}
