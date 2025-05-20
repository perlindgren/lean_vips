import LeanVips.Reg.Basic

namespace LeanVips

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
deriving Repr

inductive Instr where
  | i (instr: I) (rs rt: Reg) (imm: Bv16) : Instr
  | r (instr: R) (rs rt rd: Reg) : Instr
  | j (imm26: Bv26) : Instr
deriving Repr, Inhabited

namespace Instr
open Reg
#check Instr.i I.andi t0 t1 42

-- Instruction assembly shorthands
@[match_pattern] def and  (rd rs rt: Reg) : Instr := r .and rs rt rd
@[match_pattern] def or   (rd rs rt: Reg) : Instr := r .or  rs rt rd
@[match_pattern] def add  (rd rs rt: Reg) : Instr := r .add rs rt rd
@[match_pattern] def sub  (rd rs rt: Reg) : Instr := r .sub rs rt rd
@[match_pattern] def slt  (rd rs rt: Reg) : Instr := r .slt rs rt rd
@[match_pattern] def andi (rt rs: Reg) (imm16: Bv16): Instr := i .andi rs rt imm16
@[match_pattern] def ori  (rt rs: Reg) (imm16: Bv16): Instr := i .ori  rs rt imm16
@[match_pattern] def addi (rt rs: Reg) (imm16: Bv16): Instr := i .addi rs rt imm16
@[match_pattern] def slti (rt rs: Reg) (imm16: Bv16): Instr := i .slti rs rt imm16
@[match_pattern] def lw   (rt: Reg)    (imm16: Bv16) (rs: Reg): Instr := i .lw   rs rt imm16
@[match_pattern] def sw   (rt: Reg)    (imm16: Bv16) (rs: Reg): Instr := i .sw   rs rt imm16
@[match_pattern] def beq  (rt rs: Reg) (imm16: Bv16): Instr := i .beq  rs rt imm16
@[match_pattern] def bne  (rt rs: Reg) (imm16: Bv16): Instr := i .bne  rs rt imm16
-- @[match_pattern] def j                 (imm26: Bv26): Instr := .j            imm26

#check andi t1 t1 42

theorem andi_equal: andi t1 t0 42 = Instr.i I.andi t0 t1 42 :=
  by
   simp [andi]

theorem andi_equal_quant: ∀ (rs rt imm16), andi rt rs imm16 = Instr.i I.andi rs rt imm16 :=
  by
   simp [andi]

theorem ori_equal_quant: ∀ (rs rt imm16), ori rt rs imm16 = Instr.i I.ori rs rt imm16 :=
  by
   simp [ori]

theorem addi_equal_quant: ∀ (rs rt imm16), addi rt rs imm16 = Instr.i I.addi rs rt imm16 :=
  by
   simp [addi]

theorem slti_equal_quant: ∀ (rs rt imm16), slti rt rs imm16 = Instr.i I.slti rs rt imm16 :=
  by
   simp [slti]

theorem lw_equal_quant: ∀ (rs rt imm16), lw rt imm16 rs = Instr.i I.lw rs rt imm16 :=
  by
   simp [lw]

theorem sw_equal_quant: ∀ (rs rt imm16), sw rt imm16 rs = Instr.i I.sw rs rt imm16 :=
  by
   simp [sw]

theorem beq_equal_quant: ∀ (rs rt imm16), beq rt rs imm16 = Instr.i I.beq rs rt imm16 :=
  by
   simp [beq]

theorem bne_equal_quant: ∀ (rs rt imm16), bne rt rs imm16 = Instr.i I.bne rs rt imm16 :=
  by
   simp [bne]

theorem and_equal_quant: ∀ (rs rt rd), and rd rs rt = Instr.r R.and rs rt rd :=
  by
   simp [and]

theorem or_equal_quant: ∀ (rs rt rd), or rd rs rt = Instr.r R.or rs rt rd :=
  by
   simp [or]

theorem add_equal_quant: ∀ (rs rt rd), add rd rs rt = Instr.r R.add rs rt rd :=
  by
   simp [add]

theorem sub_equal_quant: ∀ (rs rt rd), sub rd rs rt = Instr.r R.sub rs rt rd :=
  by
   simp [sub]

theorem slt_equal_quant: ∀ (rs rt rd), slt rd rs rt = Instr.r R.slt rs rt rd :=
  by
   simp [slt]

theorem j_equal_quant: ∀ (imm26), j imm26 = Instr.j imm26 :=
  by
   simp [j]

instance : ToString Instr where
  toString (instr: Instr) :=
    match instr with
    | and  rd rs rt    => s!"and  {rd.toString}, {rs.toString}, {rt.toString}"
    | or   rd rs rt    => s!"or   {rd.toString}, {rs.toString}, {rt.toString}"
    | add  rd rs rt    => s!"add  {rd.toString}, {rs.toString}, {rt.toString}"
    | sub  rd rs rt    => s!"sub  {rd.toString}, {rs.toString}, {rt.toString}"
    | slt  rd rs rt    => s!"slt  {rd.toString}, {rs.toString}, {rt.toString}"
    | andi rt rs imm16 => s!"andi {rt.toString}, {rs.toString}, 0x{imm16.toHex}"
    | ori  rt rs imm16 => s!"ori  {rt.toString}, {rs.toString}, 0x{imm16.toHex}"
    | addi rt rs imm16 => s!"addi {rt.toString}, {rs.toString}, 0x{imm16.toHex}"
    | slti rt rs imm16 => s!"slti {rt.toString}, {rs.toString}, 0x{imm16.toHex}"
    | beq  rt rs imm16 => s!"beq  {rt.toString}, {rs.toString}, 0x{imm16.toHex}"
    | bne  rt rs imm16 => s!"bne  {rt.toString}, {rs.toString}, 0x{imm16.toHex}"
    | j    imm26       => s!"j    0x{imm26.toHex}"
    | lw   rt imm16 rs => s!"lw   {rt.toString}, 0x{imm16.toHex}({rs.toString})"
    | sw   rt imm16 rs => s!"lw   {rt.toString}, 0x{imm16.toHex}({rs.toString})"

#eval t0
#eval t0.toString
#eval toString (and t0 t1 t2)
#eval toString (j 0x0000_000f)

def Prog : Type := Array Instr
#check Prog

instance : ToString Prog where
  toString (prog: Prog) := prog.foldr (λ (i:Instr) l => (toString i ++ "\n" ++ l)) ""
