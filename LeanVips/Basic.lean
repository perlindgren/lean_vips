import LeanVips.Reg.Basic

abbrev Op   : Type := BitVec 6
abbrev Funct: Type := BitVec 6

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
deriving Repr

inductive Instr where
  | i (instr: I) (rs rt: Reg) (imm: Bv16) : Instr
  | r (instr: R) (rs rt rd: Reg) : Instr
  | j (imm26: Bv26) : Instr
deriving Repr, Inhabited

-- Instruction shorthands
def and  (rd rs rt: Reg) : Instr := .r .and rd rs rt
def or   (rd rs rt: Reg) : Instr := .r .or  rd rs rt
def sub  (rd rs rt: Reg) : Instr := .r .sub rd rs rt
def slt  (rd rs rt: Reg) : Instr := .r .slt rd rs rt
def andi (rt rs: Reg) (imm16: Bv16): Instr := .i .andi rt rs imm16
def ori  (rt rs: Reg) (imm16: Bv16): Instr := .i .ori  rt rs imm16
def addi (rt rs: Reg) (imm16: Bv16): Instr := .i .addi rt rs imm16
def slti (rt rs: Reg) (imm16: Bv16): Instr := .i .slti rt rs imm16
def lw   (rt rs: Reg) (imm16: Bv16): Instr := .i .lw   rt rs imm16
def sw   (rt rs: Reg) (imm16: Bv16): Instr := .i .sw   rt rs imm16
def beq  (rt rs: Reg) (imm16: Bv16): Instr := .i .beq  rt rs imm16
def bne' (rt rs: Reg) (imm16: Bv16): Instr := .i .bne  rt rs imm16
def j                 (imm26: Bv26): Instr := .j             imm26

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


def eval (im: IMem) (fuel: Nat) (pc: Bv32) (rf:Regfile) (dm: DMem): Regfile × DMem × Bv32 :=
  match fuel with
  | 0 => (rf, dm, pc)
  | fu + 1 =>
    let (rf, dm, pc) := match instr im pc with
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
    eval im fu (pc + 4) rf dm

def pc : Bv32 := 4
def rf: Regfile := Vector.mkVector 32 0
def imem : IMem := #[
  bne' t1 zero 4,    --00 -- if t1 != 0 brach to 14
  addi t0 t0 0x20,   --04
  addi t1 t0 (-1),   --08
  slt  t2 t0 t1,     --0c
  j    0,            --10 -- jump to address 0
  slt  t3 t1 t0,     --14
  andi t4 t3 0xFFFF, --18
  ori  t5 t3 0xFFFF  --20
]
def dm : DMem := #[]

#eval (eval imem 9 0 rf dm)
