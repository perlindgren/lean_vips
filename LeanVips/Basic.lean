-- BitVec type aliases

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
deriving Repr

inductive I where
  | andi : I
  | ori  : I
  | addi : I
  | slti : I
deriving Repr

inductive Instr where
  | i (instr: I) (rs rt: Reg) (imm: Bv16) : Instr
  | r (instr: R) (rs rt rd: Reg) : Instr
  | j (imm26: Bv26) : Instr
deriving Repr

-- register definitions
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

-- instruction shorthands
def and  (rd rs rt: Reg) : Instr := .r .and rd rs rt
def or   (rd rs rt: Reg) : Instr := .r .or  rd rs rt
def sub  (rd rs rt: Reg) : Instr := .r .sub rd rs rt
def slt  (rd rs rt: Reg) : Instr := .r .slt rd rs rt
def andi (rt rs: Reg) (imm16: Bv16): Instr := .i .andi rt rs imm16
def ori  (rt rs: Reg) (imm16: Bv16): Instr := .i .ori  rt rs imm16
def addi (rt rs: Reg) (imm16: Bv16): Instr := .i .addi rt rs imm16
def slti (rt rs: Reg) (imm16: Bv16): Instr := .i .slti rt rs imm16

-- register file
def rf: Regfile := Vector.mkVector 32 0
def w (rf: Regfile) (r: Reg) (v: Bv32) : Regfile :=
  rf.set r.toNat v
def r (rf: Regfile) (r: Reg) : Bv32 :=
  match r with
  | zero => 0 -- register zero always reads zero
  | _    => rf[r.toNat]

-- instruction memory
abbrev IMem : Type := Array Instr
deriving instance Repr for IMem

def instr (im: IMem) (pc: Bv32) : Instr := im[(pc >>> 2).toNat]

-- data memory
abbrev DMem : Type := Array Bv32
deriving instance Repr for DMem

def data (dm: DMem) (addr: Bv32) : Bv32 := dm[(addr >>> 2).toNat]!


def eval (im: IMem) (fuel: Nat) (pc: Bv32) (rf:Regfile) : Regfile :=
  match fuel with
  | 0 => rf
  | fu + 1 =>
    let rf := match instr im pc with
      | .r op rd rs rt =>
           let a := rf[rs.toNat]
         let b := rf[rt.toNat]
         let rd := rd.toNat
         match op with
         | .and => rf.set rd (a &&& b)
         | .or  => rf.set rd (a ||| b)
         | .add => rf.set rd (a + b)
         | .sub => rf.set rd (a - b)
         | .slt => rf.set rd (
           if a.toInt < b.toInt then
             1
           else
             0
         )
      |  .i op rt rs imm16 =>
        let a := rf[rs.toNat]
        let rt := rt.toNat
        match op with
        | .andi => rf.set rt (a &&& imm16.zeroExtend 32)
        | .ori  => rf.set rt (a ||| imm16.zeroExtend 32)
        | .addi => rf.set rt (a + imm16.signExtend 32)
        | .slti => rf.set rt (
          if a.toInt < (imm16.signExtend 32).toInt then
            1
          else
            0
         )
      | .j imm26 => rf
     -- | _ => rf
    eval im fu (pc + 4) rf

def pc : Bv32 := 4
def imem : IMem := #[
  addi t0 t0 0x20,
  addi t1 t0 (-1),
  slt  t2 t0 t1,
  slt  t3 t1 t0
]

#eval! ((eval imem 4 0 rf)[t0.toNat])
#eval! ((eval imem 4 0 rf)[t1.toNat])
#eval! ((eval imem 4 0 rf)[t2.toNat])
#eval! ((eval imem 4 0 rf)[t3.toNat])

#eval clock rf 0 1 0 0xdead true
#check Vector.mkVector
