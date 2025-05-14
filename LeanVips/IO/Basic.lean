import LeanVips.Asm.Basic
-- import LeanVips.SerDe.Basic

namespace LeanVips.Instr

open Reg Instr

-- abbrev toString (instr: Instr) : String :=
--   match instr with
--   | and  rd rs rt    => s!"and {rd.toString} {rs.toString} {rt.toString}"
--   | _ => "todo"
--   -- | or   rd rs rt    => (0: Op) ++ rs ++ rt ++ rd ++ (0: Shamt) ++ (0x25: Funct)
--   -- | add  rd rs rt    => (0: Op) ++ rs ++ rt ++ rd ++ (0: Shamt) ++ (0x20: Funct)
--   -- | sub  rd rs rt    => (0: Op) ++ rs ++ rt ++ rd ++ (0: Shamt) ++ (0x22: Funct)
--   -- | slt  rd rs rt    => (0: Op) ++ rs ++ rt ++ rd ++ (0: Shamt) ++ (0x2a: Funct)
--   -- | andi rt rs imm16 => (0x0c: Op) ++ rs ++ rt ++ imm16
--   -- | ori  rt rs imm16 => (0x0d: Op) ++ rs ++ rt ++ imm16
--   -- | addi rt rs imm16 => (0x08: Op) ++ rs ++ rt ++ imm16
--   -- | slti rt rs imm16 => (0x0a: Op) ++ rs ++ rt ++ imm16
--   -- | lw   rt imm16 rs => (0x23: Op) ++ rs ++ rt ++ imm16
--   -- | sw   rt imm16 rs => (0x2b: Op) ++ rs ++ rt ++ imm16
--   -- | beq  rt rs imm16 => (0x04: Op) ++ rs ++ rt ++ imm16
--   -- | bne  rt rs imm16 => (0x05: Op) ++ rs ++ rt ++ imm16
--   -- | j    imm26       => (0x02: Op) ++ imm26

-- open Instr

#eval zero.toString
#eval (and t0 t1 t2).toString


-- def save (List Instr)
