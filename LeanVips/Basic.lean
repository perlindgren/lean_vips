import LeanVips.Reg.Basic
import Std.Tactic.BVDecide

abbrev Op   : Type := BitVec 6
abbrev Funct: Type := BitVec 6
abbrev Shamt: Type := BitVec 5

inductive R where
  | and : R
  | or  : R
  | add : R
  | sub : R
  | slt : R
deriving Repr

inductive I where
  | andi : I
  | ori  : I
  | addi : I
  | slti : I
  | lw   : I
  | sw   : I
  | beq  : I
  | bne  : I
deriving Repr, BEq

inductive Instr where
  | i (instr: I) (rs rt: Reg) (imm: Bv16) : Instr
  | r (instr: R) (rs rt rd: Reg) : Instr
  | j (imm26: Bv26) : Instr
deriving Repr, Inhabited


namespace LeanVips

-- Instruction shorthands
@[match_pattern] def and  (rd rs rt: Reg) : Instr := .r .and rd rs rt
@[match_pattern] def or   (rd rs rt: Reg) : Instr := .r .or  rd rs rt
@[match_pattern] def add  (rd rs rt: Reg) : Instr := .r .add rd rs rt
@[match_pattern] def sub  (rd rs rt: Reg) : Instr := .r .sub rd rs rt
@[match_pattern] def slt  (rd rs rt: Reg) : Instr := .r .slt rd rs rt
@[match_pattern] def andi (rt rs: Reg) (imm16: Bv16): Instr := .i .andi rt rs imm16
@[match_pattern] def ori  (rt rs: Reg) (imm16: Bv16): Instr := .i .ori  rt rs imm16
@[match_pattern] def addi (rt rs: Reg) (imm16: Bv16): Instr := .i .addi rt rs imm16
@[match_pattern] def slti (rt rs: Reg) (imm16: Bv16): Instr := .i .slti rt rs imm16
@[match_pattern] def lw   (rt rs: Reg) (imm16: Bv16): Instr := .i .lw   rt rs imm16
@[match_pattern] def sw   (rt rs: Reg) (imm16: Bv16): Instr := .i .sw   rt rs imm16
@[match_pattern] def beq  (rt rs: Reg) (imm16: Bv16): Instr := .i .beq  rt rs imm16
@[match_pattern] def bne  (rt rs: Reg) (imm16: Bv16): Instr := .i .bne  rt rs imm16
@[match_pattern] def j                 (imm26: Bv26): Instr := .j             imm26


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
  | 0x23 => lw   rt rs imm16
  | 0x2b => sw   rt rs imm16
  | 0x04 => beq  rt rs imm16
  | 0x05 => bne  rt rs imm16
  | 0x02 => j    imm26
  | _    => panic!("non supported instruction")

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
  | lw   rt rs imm16 => (0x23: Op) ++ rs ++ rt ++ imm16
  | sw   rt rs imm16 => (0x2b: Op) ++ rs ++ rt ++ imm16
  | beq  rt rs imm16 => (0x04: Op) ++ rs ++ rt ++ imm16
  | bne  rt rs imm16 => (0x05: Op) ++ rs ++ rt ++ imm16
  | j    imm26       => (0x02: Op) ++ imm26


#eval (toBv32 (and t0 t1 t2))
#eval (toBv32 (or  t0 t1 t2))
#eval (toBv32 (add t0 t1 t2))
#eval (toBv32 (sub t0 t1 t2))
#eval (toBv32 (slt t0 t1 t2))

#eval (fromBv32 (toBv32 (and t0 t1 t2)))
#eval (fromBv32 (toBv32 (or  t0 t1 t2)))
#eval (fromBv32 (toBv32 (add t0 t1 t2)))
#eval (fromBv32 (toBv32 (sub t0 t1 t2)))
#eval (fromBv32 (toBv32 (slt t0 t1 t2)))

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
  . -- rename_i instr rs rt imm
    split
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
    . -- not a j instruction
      rename_i heq
      simp at heq
  . split
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
    . rename_i heq
      simp at heq

  . rename_i imm
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
    rfl

-- Instruction memory
abbrev IMem : Type := Array Instr
deriving instance Repr for IMem

def instr (im: IMem) (pc: Bv32) : Instr := im[(pc >>> 2).toNat]!

-- Data memory
abbrev DMem : Type := Array Bv32
deriving instance Repr for DMem

def DMem.w (dm: DMem) (addr: Bv32) (v: Bv32) : DMem :=
  dm.set! addr.toNat v

def DMem.r (dm: DMem) (addr: Bv32) : Bv32 :=
  dm[addr.toNat]!

def instr_eval (instr: Instr) (pc: Bv32) (rf:Regfile) (dm: DMem):Regfile × DMem × Bv32 :=
  match instr  with
  | .r op rd rs rt => -- R type instructions
     let a := rf.r rs
     let b := rf.r rt
     (match op with
     | .and => rf.w rd (a &&& b)
     | .or  => rf.w rd (a ||| b)
     | .add => rf.w rd (a + b)
     | .sub => rf.w rd (a - b)
     | .slt => rf.w rd (if a < b then 1 else 0), dm, pc)
  | .i .sw  rt rs imm16 => (rf, dm.w (rf.r rs + imm16.signExtend _) (rf.r rt), pc)
  | .i .beq rt rs imm16 => (rf, dm, if rf.r rs == rf.r rt then pc + (imm16.signExtend _ <<< 2) else pc)
  | .i .bne rt rs imm16 => (rf, dm, if rf.r rs != rf.r rt then pc + (imm16.signExtend _ <<< 2) else pc)
  | .i op rt rs imm16 => -- I type instructions
    let a := rf.r rs
    (match op with
    | .andi => rf.w rt (a &&& imm16.zeroExtend _)
    | .ori  => rf.w rt (a ||| imm16.zeroExtend _)
    | .addi => rf.w rt (a + imm16.signExtend _)
    | .slti => rf.w rt (if a < imm16.signExtend _ then 1 else 0)
    | .lw   => rf.w rt (dm.r (a + imm16.signExtend _))
    | _     => unreachable!
    , dm, pc)
  | .j imm26 => (rf, dm, (pc &&& 0xF000_0000: Bv32) ||| (imm26.zeroExtend _ <<< 2) - 4)

def eval (im: IMem) (fuel: Nat) (pc: Bv32) (rf:Regfile) (dm: DMem): Regfile × DMem × Bv32 :=
  match fuel with
  | 0 => (rf, dm, pc)
  | fu + 1 =>
    let (rf, dm, pc) := instr_eval (instr im pc) pc rf dm
    eval im fu (pc + 4) rf dm

def imem : IMem := #[
  bne  t1 zero 4,    --00 -- if t1 != 0 brach to 14
  addi t0 t0 0x20,   --04
  addi t1 t0 (-1),   --08
  slt  t2 t0 t1,     --0c
  j    0,            --10 -- jump to address 0
  slt  t3 t1 t0,     --14
  andi t4 t3 0xFFFF, --18
  ori  t5 t3 0xFFFF  --20
]

-- we define an initial state for our VM
def rf:  Regfile := Vector.mkVector 32 0
def dm : DMem := #[]

#eval (eval imem 9 0 rf dm) -- state after executing 9 instructions

-- lets try some simple proofs by (symbolic) execution
def imem_p1 :=
  #[
  addi t0 t0 0x20,   --00
  ]

-- prove that the pc is 0x04 after executing one clock cycle
theorem prog1 : ∀ (rf : Regfile) (dm: DMem),
    let (_rf', _dm', pc') := eval imem_p1 1 0x00 rf dm
    pc' = 0x04
  := by
    simp [eval, imem_p1, instr_eval, instr]

-- prove that reg t0 has increased by 0x20 (independent on initial value)
-- notice the value might have overflowed (we have wrapping arithmetics)
theorem prog1b : ∀ (rf : Regfile) (dm: DMem),
    let (rf', _dm', _pc') := eval imem_p1 1 0x00 rf dm
    rf'[t0.toNat] = (rf[t0.toNat] + 0x20)
  := by
    simp [eval, imem_p1, instr_eval, instr, Regfile.w, Regfile.r, t0, zero]

-- a bit more complex, here we first update t1 and based on that t2
def imem_p2 :=
  #[
  addi t1 t0 0x20,   --00
  addi t2 t1 0x20,   --04
  ]

-- prove the value of t1 after 2 clock cycles
theorem prog2 : ∀ (rf : Regfile) (dm: DMem),
    let (rf', _dm', _pc') := eval imem_p2 2 0x00 rf dm
    rf'[t1.toNat] = (rf[t0.toNat] + 0x20)
  := by
    simp [eval, imem_p2, instr_eval, instr, Regfile.w, Regfile.r, t0, t1, t2, zero]

-- prove the value of t2 after 2 clock cycles
-- this should now be initial t0 + 0x40
theorem prog2b : ∀ (rf : Regfile) (dm: DMem),
    let (rf', _dm', _pc') := eval imem_p2 2 0x00 rf dm
    rf'[t2.toNat] = (rf[t0.toNat] + 0x40)
  := by
    simp [eval, imem_p2, instr_eval, instr, Regfile.w, Regfile.r, t0, t1, t2, zero]
    bv_decide

-- now lets try to prove the implementation of arithmetic summation

-- specification arithmetic sum
def sum (n:Nat) : Nat :=
  match n with
  | 0     => 0
  | n + 1 => n + 1 + (sum n)

#eval (sum 3) -- 3 + 2 + 1 = 6

-- implementation arithmetic sum
-- let n = 3; // sum = 1 + 2 + 3 = 6
-- let mut sum = 0;
-- for i in 1..=n {
--  sum += i;
-- }

-- assembly version
-- m :   t0 (n + 1)
-- sum : t1
-- i :   t2
def imem_sum :=
  #[
  addi t0   zero 0x4  ,--00 m = n + 1
  addi t1   zero 0x0  ,--04 sum = 0
  addi t2   zero 0x0  ,--08 i = 0
  slt  at'  t2   t0   ,--0c i < m
  beq  at'  zero 3    ,--10 for: !(i < m) -> end
  add  t1   t1   t2   ,--14   sum = sum + i
  addi t2   t2   1    ,--18   i = i + 1
  j    3              ,--1c   j for:
  beq  zero zero (-1) ,--20 end: b end
  ]

#eval (eval imem_sum 25 0x00 rf dm).fst[t1.toNat]

theorem prog_sum : ∀ (rf : Regfile) (dm: DMem),
    let (rf', _dm', _pc') := eval imem_sum 25 0x00 rf dm
    rf'[t1.toNat] = 6
  := by
    simp [eval, imem_sum, instr_eval, instr, Regfile.w, Regfile.r, at', t0, t1, t2, zero]

-- We want to prove that for all n, the program computes the sum according to the specification
-- However we have to assume:
--   sum n = (sum n: Bv32), that is the result fits 32 bits
--   pc = 0x20, the program has run to end
theorem prog_sum_proof : ∀ (rf : Regfile) (dm: DMem) (n f: Nat),
    let (rf', dm', pc') := eval imem_sum f 0x00 rf dm
    sum n = (sum n: Bv32) -> (pc' = 0x20) -> (rf'[t1.toNat] = sum n)
  := by
    simp [eval, imem_sum, instr_eval, instr, Regfile.w, Regfile.r, at', t0, t1, t2, zero]
    sorry
