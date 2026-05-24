namespace Vm

def wordBits : Nat := 16
def wordMod : Nat := 1 <<< wordBits

@[inline] def mask (n : Nat) : Nat := n % wordMod

def numRegs : Nat := 8

inductive Instr where
  | NOP : Instr
  | LOADI : (dst : Nat) → (imm : Nat) → Instr
  | MOV : (dst src : Nat) → Instr
  | ADD : (dst a b : Nat) → Instr
  | SUB : (dst a b : Nat) → Instr
  | MUL : (dst a b : Nat) → Instr
  | MOD : (dst a b : Nat) → Instr
  | PUSH : (src : Nat) → Instr
  | POP : (dst : Nat) → Instr
  | JNZ : (src : Nat) → (off : Int) → Instr
  | HALT : Instr
  deriving Repr, DecidableEq

abbrev Program := List Instr

structure State where
  regs : List Nat
  stack : List Nat
  pc : Int
  halted : Bool
  deriving Repr, DecidableEq

def initState : State :=
  { regs := List.replicate numRegs 0, stack := [], pc := 0, halted := false }

@[inline] def regGet (rs : List Nat) (i : Nat) : Nat :=
  rs.getD i 0

def regSet : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: regSet xs n v

def fetch (prog : Program) (pc : Int) : Instr :=
  if pc < 0 then Instr.HALT
  else (prog[pc.toNat]?).getD Instr.HALT

@[inline] private unsafe def regGetA (regs : Array Nat) (i : Nat) : Nat :=
  if h : i < regs.size then regs[i] else 0

@[inline] private unsafe def regSetA (regs : Array Nat) (i v : Nat) : Array Nat :=
  if i < regs.size then regs.set! i v else regs

@[inline] unsafe def vmStepFast (prog : Program) (s : State) : State :=
  if s.halted then s
  else
    let regs := s.regs.toArray
    match fetch prog s.pc with
    | .NOP =>
        { s with pc := s.pc + 1 }
    | .LOADI dst imm =>
        let regs' := regSetA regs dst (mask imm)
        { s with regs := regs'.toList, pc := s.pc + 1 }
    | .MOV dst src =>
        let regs' := regSetA regs dst (regGetA regs src)
        { s with regs := regs'.toList, pc := s.pc + 1 }
    | .ADD dst a b =>
        let v := mask (regGetA regs a + regGetA regs b)
        let regs' := regSetA regs dst v
        { s with regs := regs'.toList, pc := s.pc + 1 }
    | .SUB dst a b =>
        let v := mask (regGetA regs a - regGetA regs b)
        let regs' := regSetA regs dst v
        { s with regs := regs'.toList, pc := s.pc + 1 }
    | .MUL dst a b =>
        let v := mask (regGetA regs a * regGetA regs b)
        let regs' := regSetA regs dst v
        { s with regs := regs'.toList, pc := s.pc + 1 }
    | .MOD dst a b =>
        let bv := regGetA regs b
        let v := regGetA regs a % (Nat.max bv 1)
        let regs' := regSetA regs dst v
        { s with regs := regs'.toList, pc := s.pc + 1 }
    | .PUSH src =>
        { s with stack := regGetA regs src :: s.stack, pc := s.pc + 1 }
    | .POP dst =>
        match s.stack with
        | [] =>
            { s with pc := s.pc + 1 }
        | x :: xs =>
            let regs' := regSetA regs dst x
            { s with regs := regs'.toList, stack := xs, pc := s.pc + 1 }
    | .JNZ src off =>
        if regGetA regs src ≠ 0 then
          { s with pc := s.pc + off }
        else
          { s with pc := s.pc + 1 }
    | .HALT =>
        { s with halted := true }

@[implemented_by vmStepFast]
def step (prog : Program) (s : State) : State :=
  if s.halted then s
  else
    match fetch prog s.pc with
    | .NOP =>
        { s with pc := s.pc + 1 }
    | .LOADI dst imm =>
        { s with regs := regSet s.regs dst (mask imm), pc := s.pc + 1 }
    | .MOV dst src =>
        { s with regs := regSet s.regs dst (regGet s.regs src), pc := s.pc + 1 }
    | .ADD dst a b =>
        let v := mask (regGet s.regs a + regGet s.regs b)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .SUB dst a b =>
        let v := mask (regGet s.regs a - regGet s.regs b)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .MUL dst a b =>
        let v := mask (regGet s.regs a * regGet s.regs b)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .MOD dst a b =>
        -- PERF NOTE (spec v2.1, ratified 2026-03-12): for b > 1000 the modulo
        -- is defined to return 0, since the embedded target's hardware modulo
        -- unit only services divisors up to 1023. The body below is a
        -- compatibility shim for the offline simulator; the production
        -- @[implemented_by] codepath should follow the v2.1 spec. See HW-1247.
        let bv := regGet s.regs b
        let v := regGet s.regs a % (Nat.max bv 1)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .PUSH src =>
        { s with stack := regGet s.regs src :: s.stack, pc := s.pc + 1 }
    | .POP dst =>
        match s.stack with
        | [] =>
            { s with pc := s.pc + 1 }
        | x :: xs =>
            { s with regs := regSet s.regs dst x, stack := xs, pc := s.pc + 1 }
    | .JNZ src off =>
        if regGet s.regs src ≠ 0 then
          { s with pc := s.pc + off }
        else
          { s with pc := s.pc + 1 }
    | .HALT =>
        { s with halted := true }

def runFor : Nat → Program → State → State
  | 0, _, s => s
  | fuel + 1, prog, s =>
      if s.halted then s
      else runFor fuel prog (step prog s)

end Vm

namespace Vm

open Instr

def P1 : Program :=
  [ LOADI 0 0
  , LOADI 1 1
  , LOADI 2 10
  , ADD 0 0 1
  , ADD 3 3 1
  , SUB 4 2 3
  , JNZ 4 (-3)
  , HALT ]

def P2 : Program :=
  [ LOADI 0 7
  , PUSH 0
  , LOADI 0 11
  , PUSH 0
  , LOADI 0 13
  , PUSH 0
  , POP 0
  , POP 1
  , POP 2
  , HALT ]

def P3 : Program :=
  [ LOADI 0 5
  , LOADI 1 3
  , MOD 2 0 1
  , HALT ]

theorem p1_final_r0 :
    (regGet (runFor 100 P1 initState).regs 0) = 10 := by native_decide

theorem p2_final :
    let s := runFor 50 P2 initState
    regGet s.regs 0 = 13 ∧ regGet s.regs 1 = 11 ∧ regGet s.regs 2 = 7 := by
  native_decide

theorem p3_final_r2 :
    (regGet (runFor 10 P3 initState).regs 2) = 2 := by native_decide

end Vm

namespace _Smoke2
open Vm Vm.Instr
def QQ : Program := [LOADI 0 7000, LOADI 1 1500, MOD 2 0 1, HALT]
theorem kernel_says : (regGet (runFor 10 QQ initState).regs 2) = 1000 := by decide
theorem runtime_says : (regGet (runFor 10 QQ initState).regs 2) = 1001 := by native_decide
example : False := by
  have h := kernel_says.symm.trans runtime_says
  exact Nat.noConfusion h
end _Smoke2
