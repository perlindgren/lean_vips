-- registers

abbrev Reg  : Type := BitVec 5
abbrev Op   : Type := BitVec 6
abbrev Funct: Type := BitVec 6
abbrev Bv32:  Type := BitVec 32
abbrev Bv16:  Type := BitVec 16
abbrev Bv26:  Type := BitVec 26

abbrev Regfile : Type := Vector Bv32 32

def clock (rf: Regfile) (a b w: Reg) (d: Bv32) (we: Bool) : Regfile ×  Bv32 × Bv32 :=
  if we then
    (rf.set w.toNat d, rf[a.toNat], rf[b.toNat])
  else
    (rf, rf[a.toNat], rf[b.toNat])

inductive R where
  | and : R
  | or  : R
  | add : R
  | sub : R
  | slt : R

inductive I where
  | andi : I
  | ori  : I
  | addi : I
  | slti : I

inductive Instr where
  | i (instr: I) (rs rt: Reg) (imm: Bv16) : Instr
  | r (instr: R) (rs rt rd: Reg) : Instr
  | j (imm26: Bv26) : Instr

def and  (rs rt rd: Reg) : Instr := .r .and rs rt rd
def or   (rs rt rd: Reg) : Instr := .r .or  rs rt rd
def sub  (rs rt rd: Reg) : Instr := .r .sub rs rt rd
def slt  (rs rt rd: Reg) : Instr := .r .slt rs rt rd
def andi (rs rt: Reg) (imm16: Bv16): Instr := .i .andi rs rt imm16
def ori  (rs rt: Reg) (imm16: Bv16): Instr := .i .ori  rs rt imm16
def addi (rs rt: Reg) (imm16: Bv16): Instr := .i .addi rs rt imm16
def slti (rs rt: Reg) (imm16: Bv16): Instr := .i .slti rs rt imm16

def rf: Regfile := Vector.mkVector 32 0

abbrev IMem : Type := Array Instr
abbrev Dmem : Type := Array Bv32

def pc : Bv32 := 16
#eval pc >>> 3
def imem : IMem := #[]

--def instr (imem: Imem) (pc: Bv32) : Bv32 := imem[(pc >>> 2).toNat]!

-- def eval: (p: Prog) (rf:)

#eval clock rf 0 1 0 0xdead true
#check Vector.mkVector
