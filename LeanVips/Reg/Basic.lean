-- BitVectors
abbrev Bv32:  Type := BitVec 32
abbrev Bv16:  Type := BitVec 16
abbrev Bv26:  Type := BitVec 26

-- Registers
abbrev Reg  : Type := BitVec 5

@[match_pattern]
def zero : Reg := 0
def at'  : Reg := 1
def v0   : Reg := 2
def v1   : Reg := 3
def a0   : Reg := 4
def a1   : Reg := 5
def a2   : Reg := 6
def a3   : Reg := 7
def t0   : Reg := 8
def t1   : Reg := 9
def t2   : Reg := 10
def t3   : Reg := 11
def t4   : Reg := 12
def t5   : Reg := 13
def t6   : Reg := 14
def t7   : Reg := 15
def s0   : Reg := 16
def s1   : Reg := 17
def s2   : Reg := 18
def s3   : Reg := 19
def s4   : Reg := 20
def s5   : Reg := 21
def s6   : Reg := 22
def s7   : Reg := 23
def t8   : Reg := 24
def t9   : Reg := 25
def k0   : Reg := 26
def k1   : Reg := 27
def gp   : Reg := 28
def sp   : Reg := 29
def fp   : Reg := 30
def ra   : Reg := 31

-- Register file

abbrev Regfile : Type := Vector Bv32 32

def Regfile.w (rf: Regfile) (r: Reg) (v: Bv32) : Regfile :=
  rf.set r.toNat v

-- def Regfile.r (rf: Regfile) (r: Reg) : Bv32 :=
--   match r with
--   | zero => 0 -- register zero always reads zero
--   | _    => rf[r.toNat]

-- for easier reasoning using bv_decide
def Regfile.r (rf: Regfile) (r: Reg) : Bv32 :=
  if r = zero then
    0
  else
    rf[r.toNat]
