import LeanVips.Semantics.Basic
import Std.Tactic.BVDecide

namespace LeanVips

-- serialization examples
#eval (toBv32 (and  t0 t1 t2))
#eval (toBv32 (or   t0 t1 t2))
#eval (toBv32 (add  t0 t1 t2))
#eval (toBv32 (sub  t0 t1 t2))
#eval (toBv32 (andi t0 t1 0))
#eval (toBv32 (ori  t0 t1 0xffff))
#eval (toBv32 (addi t0 t1 (-1)))
#eval (toBv32 (slti t0 t1 5))
#eval (toBv32 (lw   t0 t1 16))
#eval (toBv32 (sw   t0 zero 0))
#eval (toBv32 (beq  t0 t1 2))
#eval (toBv32 (beq  t0 t1 (-1)))
#eval (toBv32 (j    0x123_4567))

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

#eval (eval imem 9 0x00 rf dm) -- state after executing 9 instructions

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
    simp [eval, imem_p1, instr_eval, IMem.r]

-- prove that reg t0 has increased by 0x20 (independent on initial value)
-- notice the value might have overflowed (we have wrapping arithmetics)
theorem prog1b : ∀ (rf : Regfile) (dm: DMem),
    let (rf', _dm', _pc') := eval imem_p1 1 0x00 rf dm
    rf'[t0.toNat] = (rf[t0.toNat] + 0x20)
  := by
    simp [eval, imem_p1, instr_eval, IMem.r, Regfile.w, Regfile.r, t0, zero]

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
    simp [eval, imem_p2, instr_eval, IMem.r, Regfile.w, Regfile.r, t0, t1, t2, zero]

-- prove the value of t2 after 2 clock cycles
-- this should now be initial t0 + 0x40
theorem prog2b : ∀ (rf : Regfile) (dm: DMem),
    let (rf', _dm', _pc') := eval imem_p2 2 0x00 rf dm
    rf'[t2.toNat] = (rf[t0.toNat] + 0x40)
  := by
    simp [eval, imem_p2, instr_eval, IMem.r, Regfile.w, Regfile.r, t0, t1, t2, zero]
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
    simp [eval, imem_sum, instr_eval, IMem.r, Regfile.w, Regfile.r, at', t0, t1, t2, zero]

-- We want to prove that for all n, the program computes the sum according to the specification
-- However we have to assume:
--   sum n = (sum n: Bv32), that is the result fits 32 bits
--   pc = 0x20, the program has run to end
theorem prog_sum_proof : ∀ (rf : Regfile) (dm: DMem) (n f: Nat),
    let (rf', dm', pc') := eval imem_sum f 0x00 rf dm
    sum n = (sum n: Bv32) -> (pc' = 0x20) -> (rf'[t1.toNat] = sum n)
  := by
    simp [eval, imem_sum, instr_eval, IMem.r, Regfile.w, Regfile.r, at', t0, t1, t2, zero]
    sorry
