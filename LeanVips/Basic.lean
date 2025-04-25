import LeanVips.Reg.Basic

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
  let op : Op := (bv >>> 26).truncate _
  let funct : Funct := bv.truncate _
  let rs : Reg := (bv >>> 21).truncate _
  let rt : Reg := (bv >>> 16).truncate _
  let rd : Reg := (bv >>> 11).truncate _
  let imm16 : Bv16 := bv.truncate _
  let imm26 : Bv26 := bv.truncate _

  match op with
  | 0 => match funct with
    | 0x24 => and rd rs rd
    | 0x25 => or  rd rs rd
    | 0x20 => add rd rs rd
    | 0x22 => sub rd rs rd
    | 0x2a => slt rd rs rd
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


#eval (toBv32 (add t0 t1 t2))

#eval (fromBv32 (toBv32 (add t0 t1 t2)))

theorem tofrom (i: Instr) : fromBv32 (toBv32 i) = i := by
  induction i using toBv32.induct <;> simp [fromBv32, toBv32, *]





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

def pc : Bv32 := 4
def rf: Regfile := Vector.mkVector 32 0
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
def dm : DMem := #[]

#eval (eval imem 9 0 rf dm)
