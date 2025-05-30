import LeanVips.Semantics.Basic
import LeanVips.SerDe.Basic

namespace LeanVips.Instr

open Reg

-- serialization examples
#eval toBv32 (and  t0 t1 t2)     -- 0x012a4024#32
#eval toBv32 (or   t0 t1 t2)     -- 0x012a4025#32
#eval toBv32 (add  t0 t1 t2)     -- 0x012a4020#32
#eval toBv32 (sub  t0 t1 t2)     -- 0x012a4022#32
#eval toBv32 (andi t0 t1 0)      -- 0x31280000#32
#eval toBv32 (ori  t1 t1 0xfff0) -- 0x3529fff0#32
#eval toBv32 (addi t0 t1 (-1))   -- 0x2128ffff#32
#eval toBv32 (slti t0 t1 5)      -- 0x29280005#32
#eval toBv32 (lw   t0 16 t1)     -- 0x8d280010#32
#eval toBv32 (sw   t0 0 t1)      -- 0xad280000#32
#eval toBv32 (beq  t0 t1 2)      -- 0x11280002#32
#eval toBv32 (bne  t0 t1 (-1))   -- 0x1528ffff#32
#eval toBv32 (j    0x123_4567)   -- 0x09234567#32
-- de-serialization examples
#eval fromBv32 0x012a4024#32            -- corresponds to `and  t0 t1 t2`
#eval fromBv32 (toBv32 (and  t0 t1 t2)) -- 1-1 (bijection)

-- a simple program, (an array of instructions)
def imem : IMem := #[
  bne  t2 zero 4,    --00 -- if t2 != 0 brach to 14
  addi t0 t0 0x20,   --04 -- t0 <- 0x20
  addi t1 t0 (-1),   --08 -- t1 <- 0x1f
  slt  t2 t1 t0,     --0c -- t2 <- 0x1f < 0x20
  j    0,            --10 -- jump to address 0
  slt  t3 t0 t1,     --14 -- t3 <- 0x20 < 0x1f
  andi t4 t1 0xF00F, --18 -- t4 <- 0x0000_000f
  ori  t5 t1 0xF00F  --20 -- t5 <- 0x0000_f01f
                     --24 -- index out of bounds
]

-- we define an initial state for our VM
def rf:  Regfile := Vector.replicate 32 0
def dm : DMem := #[]

-- virtual machine execution of 9 cycles, starting from 0x00
#eval eval imem 9 0x00 rf dm -- [your cursor here]

#eval -- [place cursor here]
  let (rf, _, pc) := eval imem 9 0x00 rf dm -- state after executing 9 instructions
  (pc, rf[t0], rf[t1], rf[t2], rf[t3], rf[t4], rf[t5])

-- lets try some simple proofs by (symbolic) execution
def imem_p1 :=
  #[
  addi t0 t0 0x20, -- instruction at address 0x00
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
    rf'[t0] = rf[t0] + 0x20
  := by
    simp [eval, instr_eval, IMem.r, imem_p1, Regfile.w, Regfile.r, t0,zero, Vector.get]

-- a bit more complex, here we first update t1 and based on that t2
def imem_p2 :=
  #[
  addi t1 t0 0x20,   --00
  addi t2 t1 0x20,   --04
  ]

-- prove the value of t1 after 2 clock cycles
theorem prog2 : ∀ (rf : Regfile) (dm: DMem),
    let (rf', _dm', _pc') := eval imem_p2 2 0x00 rf dm
    rf'[t1] = (rf[t0] + 0x20)
  := by
    simp [eval, instr_eval, IMem.r, imem_p2, Regfile.w, Regfile.r, t0, t1, t2, zero]

-- prove the value of t2 after 2 clock cycles
-- this should now be initial t0 + 0x40
theorem prog2b : ∀ (rf : Regfile) (dm: DMem),
    let (rf', _dm', _pc') := eval imem_p2 2 0x00 rf dm
    rf'[t2.toNat] = (rf[t0.toNat] + 0x40)
  := by
    simp [eval, imem_p2, instr_eval, IMem.r, Regfile.w, Regfile.r, t0, t1, t2, zero]
    bv_decide

-- now lets try to prove the implementation of arithmetic summation

-- specification arithmetic sum in Lean
def sum (n:Nat) : Nat :=
  match n with
  | 0     => 0
  | n + 1 => n + 1 + (sum n)

#eval sum 3 -- 3 + 2 + 1 = 6

-- imperative implementation in Lean
def sum_imperative (n: Nat): IO Unit := do
  let mut sum : Nat := 0
  let mut x : Nat := 1
  while x < n + 1 do
    sum := sum + x
    IO.println s!"x = {x}, sum = {sum}"
    x := x + 1
  IO.println s!"sum = {sum}"

#eval sum_imperative 3

-- assembly version
-- n    : a0, argument
-- cond : t0, initiated to (n + 1)
-- sum  : t1
-- x    : t2, loop variable
def imem_sum :=
  #[
  addi t0   a0   0x1  ,--00 cond = n + 1
  addi t1   zero 0x0  ,--04 sum = 0
  addi t2   zero 0x1  ,--08 x = 1
  slt  at'  t2   t0   ,--0c while: x < cond
  beq  at'  zero 3    ,--10   if !(x < cond) -> end
  add  t1   t1   t2   ,--14   sum = sum + x
  addi t2   t2   1    ,--18   x = x + 1
  j    3              ,--1c   j while
  beq  zero zero (-1) ,--20 end: b end
  ]

-- run the virtual machine for 20 clock cycles
-- result is (0x00000006#32, 0x00000020#32)
-- i.e, the next instruction to execute is 0x20
-- thus, program has run to end
#eval -- [your cursor here]
  let rf := rf.w a0 3 -- set argument n = 3
  let (rf, _, pc) := (eval imem_sum 20 0x00 rf dm)
  (rf[t1.toNat], pc)

-- set_option maxHeartbeats 100_000

theorem prog_sum : ∀ (rf : Regfile) (dm: DMem),
    let (rf', _dm', _pc') := eval imem_sum 26 0x00 rf dm
    rf[a0] = 3 -> rf'[t1] = 1+2+3
  := by
    -- the indexing of Regfile seems to cause some problem with the verification
    -- in any case it is not super interesting to show for a concrete value
    -- what we want is a general proof
    -- simp [eval, imem_sum, instr_eval, IMem.r, Regfile.w, Regfile.r, at', t0, t1, t2, zero]
    sorry

-- We want to prove that for all n, the program computes the sum according to the specification
-- However we have to assume:
--   rf[a0] = n
--   sum n = (sum n: Bv32), that is the result fits 32 bits
--   pc = 0x20, the program has run to end
theorem prog_sum_proof : ∀ (rf : Regfile) (dm: DMem) (n f: Nat),
    let (rf', dm', pc') := eval imem_sum f 0x00 rf dm
    rf[a0] = n -> sum n = (sum n: Bv32) -> pc' = 0x20 -> (rf'[t1] = sum n)
  := by
    sorry

-- testing the data memory
-- notice,
--   we support only lw/sw
--   memory implementation is based on word indexes, so address is shifted right by 2
--   out of bounds reads/writes will cause panic

def dm_data : DMem := #[
  1, -- 00
  2, -- 04
  3, -- 08
  4, -- 0c
]

def imem_dm := #[
  lw t0   0x0 zero   ,-- lw t0 0x0(zero)
  lw t1   0x4 zero   ,--
  lw t2   0x8 zero   ,--
  lw t3   0xc zero   ,--

  sw t0   0xc zero   ,-- sw t0 0x0(zero)
  sw t1   0x8 zero   ,--
  sw t2   0x4 zero   ,--
  sw t3   0x0 zero   ,--

  beq zero zero (-1) ,-- loop:   b loop:
]

#eval
  let (rf, dm, pc) := eval imem_dm 25 0x00 rf dm_data
  (rf[t0], rf[t1], rf[t2], rf[t3], dm, pc)

-- The above example sets the initial data memory content to [1,2,3,4],
-- reads the first 4 words to registers t0, t1, t2, t3 respectively,
-- and writes the registers to memory in reversed order.
-- Registers t0, t1, t2, and t3, the dm and pc are shown as results of evaluation

def imem_dm2 := #[
  lw t0   0x0c zero  ,-- lw t0 0x0c(zero), value 4
  lw t1   (-0x04) t0 ,-- lw t1 -0x04(t0), address 0, value 1
  beq zero zero (-1) ,-- loop:   b loop:
]

#eval
  let (rf, _dm, _pc) := eval imem_dm2 5 0x00 rf dm_data
  (rf[t0.toNat], rf[t1.toNat])

-- The above example, reads the address 0x04 (value 4) from data memory into t0
-- Read, the address (-0x04) (t0), (address 0), with value 1 into t1
-- Registers t0 and t1 are shown as the result of evaluation
