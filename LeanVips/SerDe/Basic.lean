import LeanVips.Asm.Basic
import Std.Tactic.BVDecide

namespace LeanVips.Instr

-- Deserialization from bit vector to instruction
def fromBv32 (bv: Bv32) : Instr :=
  let op : Op := (bv >>> 26).setWidth _
  let funct : Funct := bv.setWidth _
  let rs : Reg := (bv >>> 21).setWidth _
  let rt : Reg := (bv >>> 16).setWidth _
  let rd : Reg := (bv >>> 11).setWidth _
  let imm16 : Bv16 := bv.setWidth _
  let imm26 : Bv26 := bv.setWidth _

  match op with
  | 0 => match funct with
    | 0x24 => and rd rs rt
    | 0x25 => or  rd rs rt
    | 0x20 => add rd rs rt
    | 0x22 => sub rd rs rt
    | 0x2a => slt rd rs rt
    | _    => panic!("non supported R instruction")
  | 0x0c => andi rt rs imm16
  | 0x0d => ori  rt rs imm16
  | 0x08 => addi rt rs imm16
  | 0x0a => slti rt rs imm16
  | 0x23 => lw   rt imm16 rs
  | 0x2b => sw   rt imm16 rs
  | 0x04 => beq  rt rs imm16
  | 0x05 => bne  rt rs imm16
  | 0x02 => j    imm26
  | _    => panic!("non supported instruction")

-- Serialization of instruction to bit vector

def toBv32 (instr: Instr) : Bv32 :=
  match instr with
  | and  rd rs rt    => (0: Op) ++ rs ++ rt ++ rd ++ (0: Shamt) ++ (0x24: Funct)
  | or   rd rs rt    => (0: Op) ++ rs ++ rt ++ rd ++ (0: Shamt) ++ (0x25: Funct)
  | add  rd rs rt    => (0: Op) ++ rs ++ rt ++ rd ++ (0: Shamt) ++ (0x20: Funct)
  | sub  rd rs rt    => (0: Op) ++ rs ++ rt ++ rd ++ (0: Shamt) ++ (0x22: Funct)
  | slt  rd rs rt    => (0: Op) ++ rs ++ rt ++ rd ++ (0: Shamt) ++ (0x2a: Funct)
  | andi rt rs imm16 => (0x0c: Op) ++ rs ++ rt ++ imm16
  | ori  rt rs imm16 => (0x0d: Op) ++ rs ++ rt ++ imm16
  | addi rt rs imm16 => (0x08: Op) ++ rs ++ rt ++ imm16
  | slti rt rs imm16 => (0x0a: Op) ++ rs ++ rt ++ imm16
  | lw   rt imm16 rs => (0x23: Op) ++ rs ++ rt ++ imm16
  | sw   rt imm16 rs => (0x2b: Op) ++ rs ++ rt ++ imm16
  | beq  rt rs imm16 => (0x04: Op) ++ rs ++ rt ++ imm16
  | bne  rt rs imm16 => (0x05: Op) ++ rs ++ rt ++ imm16
  | j    imm26       => (0x02: Op) ++ imm26

section TestToFromBv

open Reg

def bv_addi := toBv32 (addi t0 t0 1)
#eval bv_addi.toHex
def i_bv_addi := fromBv32 bv_addi
#eval toString i_bv_addi

end TestToFromBv

-- theorem helpers
theorem i_op : ∀ (op : Op) (rs rt : Reg) (imm: Bv16),
  BitVec.setWidth 6 ((op ++ rs ++ rt ++ imm) >>> 26) = op := by
  bv_decide
theorem i_rs : ∀ (op : Op) (rs rt : Reg) (imm: Bv16),
  BitVec.setWidth 5 ((op ++ rs ++ rt ++ imm) >>> 21) = rs := by
  bv_decide
theorem i_rt : ∀ (op : Op) (rs rt : Reg) (imm: Bv16),
  BitVec.setWidth 5 ((op ++ rs ++ rt ++ imm) >>> 16) = rt := by
  bv_decide
theorem i_imm : ∀ (op : Op) (rs rt : Reg) (imm: Bv16),
  BitVec.setWidth 16 ((op ++ rs ++ rt ++ imm)) = imm := by
  bv_decide
theorem r_op : ∀ (op : Op) (rs rt rd: Reg) (shamt: Shamt) (funct: Funct),
  BitVec.setWidth 6 ((op ++ rs ++ rt ++ rd ++ shamt ++ funct) >>> 26) = op := by
  bv_decide
theorem r_rs : ∀ (op : Op) (rs rt rd: Reg) (shamt: Shamt) (funct: Funct),
  BitVec.setWidth 5 ((op ++ rs ++ rt ++ rd ++ shamt ++ funct) >>> 21) = rs := by
  bv_decide
theorem r_rt : ∀ (op : Op) (rs rt rd: Reg) (shamt: Shamt) (funct: Funct),
  BitVec.setWidth 5 ((op ++ rs ++ rt ++ rd ++ shamt ++ funct) >>> 16) = rt := by
  bv_decide
theorem r_rd : ∀ (op : Op) (rs rt rd: Reg) (shamt: Shamt) (funct: Funct),
  BitVec.setWidth 5 ((op ++ rs ++ rt ++ rd ++ shamt ++ funct) >>> 11) = rd := by
  bv_decide
theorem r_funct : ∀ (op : Op) (rs rt rd: Reg) (shamt: Shamt) (funct: Funct),
  BitVec.setWidth 6 (op ++ rs ++ rt ++ rd ++ shamt ++ funct) = funct := by
  bv_decide

theorem tofrom (i: Instr) : fromBv32 (toBv32 i) = i := by
  simp [toBv32]
  cases i
  . split -- i type instruction
    . rename_i heq -- not a r type instruction
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i rt rs imm16 heq
      rw [heq]
      unfold fromBv32
      simp
      rw [i_op]
      simp
      rw [i_rt, i_rs, i_imm]
      rfl
    . rename_i rt rs imm16 heq
      rw [heq]
      unfold fromBv32
      simp
      rw [i_op]
      simp
      rw [i_rt, i_rs, i_imm]
      rfl
    . rename_i rt rs imm16 heq
      rw [heq]
      unfold fromBv32
      simp
      rw [i_op]
      simp
      rw [i_rt, i_rs, i_imm]
      rfl
    . rename_i rt rs imm16 heq
      rw [heq]
      unfold fromBv32
      simp
      rw [i_op]
      simp
      rw [i_rt, i_rs, i_imm]
      rfl
    . rename_i rt rs imm16 heq
      rw [heq]
      unfold fromBv32
      simp
      rw [i_op]
      simp
      rw [i_rt, i_rs, i_imm]
      rfl
    . rename_i rt rs imm16 heq
      rw [heq]
      unfold fromBv32
      simp
      rw [i_op]
      simp
      rw [i_rt, i_rs, i_imm]
      rfl
    . rename_i rt rs imm16 heq
      rw [heq]
      unfold fromBv32
      simp
      rw [i_op]
      simp
      rw [i_rt, i_rs, i_imm]
      rfl
    . rename_i rt rs imm16 heq
      rw [heq]
      unfold fromBv32
      simp
      rw [i_op]
      simp
      rw [i_rt, i_rs, i_imm]
      rfl
    . -- not a j type instruction
      rename_i heq
      simp at heq
  . split -- r type instruction
    . rename_i heq
      rw [heq]
      unfold fromBv32
      rename_i rd rs rt
      simp
      rw [r_op]
      simp
      rw [r_funct]
      simp
      rw [r_rd, r_rt, r_rs]
      rfl
    . rename_i heq
      rw [heq]
      unfold fromBv32
      rename_i rd rs rt
      simp
      rw [r_op]
      simp
      rw [r_funct]
      simp
      rw [r_rd, r_rt, r_rs]
      rfl
    . rename_i heq
      rw [heq]
      unfold fromBv32
      rename_i rd rs rt
      simp
      rw [r_op]
      simp
      rw [r_funct]
      simp
      rw [r_rd, r_rt, r_rs]
      rfl
    . rename_i heq
      rw [heq]
      unfold fromBv32
      rename_i rd rs rt
      simp
      rw [r_op]
      simp
      rw [r_funct]
      simp
      rw [r_rd, r_rt, r_rs]
      rfl
    . rename_i heq
      rw [heq]
      unfold fromBv32
      rename_i rd rs rt
      simp
      rw [r_op]
      simp
      rw [r_funct]
      simp
      rw [r_rd, r_rt, r_rs]
      rfl
    . rename_i heq -- not a i/j type
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i heq
      simp at heq
    . rename_i heq
      simp at heq

  . rename_i imm -- j type instruction
    simp [toBv32]
    unfold fromBv32
    have jt : ∀ (x: BitVec 6), (BitVec.setWidth 6 ((x ++ imm) >>> 26) = x) := by
      bv_decide
    simp
    rw [jt]
    simp
    have jt2 : (BitVec.setWidth 26 (2#6 ++ imm) = imm) := by
      bv_decide
    rw [jt2]
