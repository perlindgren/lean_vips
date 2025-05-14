-- BitVectors
abbrev Bv32:  Type := BitVec 32
abbrev Bv16:  Type := BitVec 16
abbrev Bv26:  Type := BitVec 26

-- Registers
abbrev Reg  : Type := BitVec 5

namespace Reg

@[match_pattern] def zero : Reg := 0
@[match_pattern] def at'  : Reg := 1
@[match_pattern] def v0   : Reg := 2
@[match_pattern] def v1   : Reg := 3
@[match_pattern] def a0   : Reg := 4
@[match_pattern] def a1   : Reg := 5
@[match_pattern] def a2   : Reg := 6
@[match_pattern] def a3   : Reg := 7
@[match_pattern] def t0   : Reg := 8
@[match_pattern] def t1   : Reg := 9
@[match_pattern] def t2   : Reg := 10
@[match_pattern] def t3   : Reg := 11
@[match_pattern] def t4   : Reg := 12
@[match_pattern] def t5   : Reg := 13
@[match_pattern] def t6   : Reg := 14
@[match_pattern] def t7   : Reg := 15
@[match_pattern] def s0   : Reg := 16
@[match_pattern] def s1   : Reg := 17
@[match_pattern] def s2   : Reg := 18
@[match_pattern] def s3   : Reg := 19
@[match_pattern] def s4   : Reg := 20
@[match_pattern] def s5   : Reg := 21
@[match_pattern] def s6   : Reg := 22
@[match_pattern] def s7   : Reg := 23
@[match_pattern] def t8   : Reg := 24
@[match_pattern] def t9   : Reg := 25
@[match_pattern] def k0   : Reg := 26
@[match_pattern] def k1   : Reg := 27
@[match_pattern] def gp   : Reg := 28
@[match_pattern] def sp   : Reg := 29
@[match_pattern] def fp   : Reg := 30
@[match_pattern] def ra   : Reg := 31

-- Register file

abbrev Regfile : Type := Vector Bv32 32

--instance : GetElem (Vector α n) Nat α fun _ i => i < n where
--   getElem xs i h := get xs ⟨i, h⟩

def Regfile.w (rf: Regfile) (r: Reg) (v: Bv32) : Regfile :=
  rf.set r.toFin v

-- def Regfile.r (rf: Regfile) (r: Reg) : Bv32 :=
--   match r with
--   | zero => 0 -- register zero always reads zero
--   | _    => rf[r.toNat]

-- for easier reasoning using bv_decide
def Regfile.r (rf: Regfile) (r: Reg) : Bv32 :=
  if r = zero then
    0
  else
    rf.get r.toFin

instance : GetElem Regfile Reg Bv32 (fun _ _ => True) where
   getElem rf r _ :=  rf.r r

@[simp] theorem get_elem : ∀ (rf : Regfile) (r:Reg), rf[r] = rf.r r := by
  simp [getElem]



def toString (r : Reg) : String :=
  match r with
  | zero => "zero"
  | at'  => "at"
  | v0   => "v0"
  | v1   => "v1"
  | a0   => "a0"
  | a1   => "a1"
  | a2   => "a2"
  | a3   => "a3"
  | t0   => "t0"
  | t1   => "t1"
  | t2   => "t2"
  | t3   => "t3"
  | t4   => "t4"
  | t5   => "t5"
  | t6   => "t6"
  | t7   => "t7"
  | s0   => "s0"
  | s1   => "s1"
  | s2   => "s2"
  | s3   => "s3"
  | s4   => "s4"
  | s5   => "s5"
  | s6   => "s6"
  | s7   => "s7"
  | t8   => "t8"
  | t9   => "t9"
  | k0   => "k0"
  | k1   => "k1"
  | gp   => "gp"
  | sp   => "sp"
  | fp   => "fp"
  | ra   => "ra"
  | _    => unreachable! -- can we get rid of this

#eval zero.toString

#eval s!"{t0.toString}"

#eval
  for r in [0:32] do
    let reg: Reg := r
    dbg_trace "{reg.toString}";
