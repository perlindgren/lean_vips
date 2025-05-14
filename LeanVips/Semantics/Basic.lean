import LeanVips.Asm.Basic
import Std.Tactic.BVDecide

namespace LeanVips

open Reg

-- Instruction memory
abbrev IMem : Type := Array Instr
deriving instance Repr for IMem

def IMem.r (im: IMem) (pc: Bv32) : Instr := im[(pc >>> 2).toNat]!

-- Data memory
abbrev DMem : Type := Array Bv32
deriving instance Repr for DMem

def DMem.w (dm: DMem) (addr: Bv32) (v: Bv32) : DMem :=
  dm.set! addr.toNat v

def DMem.r (dm: DMem) (addr: Bv32) : Bv32 :=
  dm[addr.toNat]!

-- Instruction evaluation semantics
def instr_eval (instr: Instr) (pc: Bv32) (rf:Regfile) (dm: DMem):Regfile × DMem × Bv32 :=
  match instr  with
  | .r op rs rt rd => -- R type instructions
     let a := rf[rs]
     let b := rf[rt]
     (match op with
     | .and => rf.w rd (a &&& b)
     | .or  => rf.w rd (a ||| b)
     | .add => rf.w rd (a + b)
     | .sub => rf.w rd (a - b)
     | .slt => rf.w rd (if a < b then 1 else 0), dm, pc)
  | .i .sw  rs rt imm16 => (rf, dm.w ((rf[rs] + imm16.signExtend _).ushiftRight 2) (rf[rt]), pc)
  | .i .beq rs rt imm16 => (rf, dm, if rf[rs] == rf[rt] then pc + (imm16.signExtend _ <<< 2) else pc)
  | .i .bne rs rt imm16 => (rf, dm, if rf[rs] != rf[rt] then pc + (imm16.signExtend _ <<< 2) else pc)
  | .i op rs rt imm16 => -- I type instructions
    let a := rf[rs]
    (match op with
    | .andi => rf.w rt (a &&& imm16.zeroExtend _)
    | .ori  => rf.w rt (a ||| imm16.zeroExtend _)
    | .addi => rf.w rt (a + imm16.signExtend _)
    | .slti => rf.w rt (if a < imm16.signExtend _ then 1 else 0)
    | .lw   => rf.w rt (dm.r ((a + imm16.signExtend 32).ushiftRight 2))
    | _     => unreachable!
    , dm, pc)
  | .j imm26 => (rf, dm, (pc &&& 0xF000_0000: Bv32) ||| (imm26.zeroExtend _ <<< 2))

-- Program evaluation semantics
def eval (im: IMem) (fuel: Nat) (pc: Bv32) (rf:Regfile) (dm: DMem): Regfile × DMem × Bv32 :=
  match fuel with
  | 0 => (rf, dm, pc)
  | fu + 1 =>
    let (rf, dm, pc) := instr_eval (im.r pc) (pc + 4) rf dm
    eval im fu pc rf dm
