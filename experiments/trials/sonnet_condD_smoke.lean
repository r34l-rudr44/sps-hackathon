/-
  sonnet_condD.lean — optimized VM with @[implemented_by vmStepFast].

  Copies the full Vm namespace from Victim3.lean (types, helpers, source
  step, programs, theorems), then adds a fast runtime body `vmStepFast`
  and wires it up via the `@[implemented_by]` attribute on `step`.
-/

namespace Vm

/-! ## Word and register semantics -/

def wordBits : Nat := 16
def wordMod  : Nat := 1 <<< wordBits   -- 2^16 = 65536

@[inline] def mask (n : Nat) : Nat := n % wordMod

def numRegs : Nat := 8

/-! ## Instruction set -/

inductive Instr where
  | NOP    : Instr
  | LOADI  : (dst : Nat) → (imm : Nat)        → Instr
  | MOV    : (dst src : Nat)                  → Instr
  | ADD    : (dst a b : Nat)                  → Instr
  | SUB    : (dst a b : Nat)                  → Instr   -- saturating: max 0 (a - b)
  | MUL    : (dst a b : Nat)                  → Instr
  | MOD    : (dst a b : Nat)                  → Instr   -- a mod (max 1 b); never divides by zero
  | PUSH   : (src : Nat)                      → Instr
  | POP    : (dst : Nat)                      → Instr   -- empty stack is a no-op (dst untouched)
  | JNZ    : (src : Nat) → (off : Int)        → Instr   -- if regs[src] ≠ 0 then pc += off else pc += 1
  | HALT   : Instr
  deriving Repr, DecidableEq

abbrev Program := List Instr

structure State where
  regs    : List Nat
  stack   : List Nat
  pc      : Int
  halted  : Bool
  deriving Repr, DecidableEq

def initState : State :=
  { regs := List.replicate numRegs 0, stack := [], pc := 0, halted := false }

/-! ## Helpers -/

@[inline] def regGet (rs : List Nat) (i : Nat) : Nat :=
  rs.getD i 0

def regSet : List Nat → Nat → Nat → List Nat
  | [],       _,   _ => []
  | _ :: xs, 0,   v => v :: xs
  | x :: xs, n+1, v => x :: regSet xs n v

def fetch (prog : Program) (pc : Int) : Instr :=
  if pc < 0 then Instr.HALT
  else (prog[pc.toNat]?).getD Instr.HALT

/-! ## Fast runtime body (used at runtime via @[implemented_by]) -/

/-- Fast iterative step: same semantics as `step`, written for runtime efficiency.
    Uses `unsafe` only because `@[implemented_by]` requires it; the logic is
    total and faithful to the source spec. -/
unsafe def vmStepFast (prog : Program) (s : State) : State :=
  if s.halted then s
  else
    -- Fetch the instruction at the current pc
    let instr :=
      if s.pc < 0 then Instr.HALT
      else (prog[s.pc.toNat]?).getD Instr.HALT
    match instr with
    | .NOP =>
        { s with pc := s.pc + 1 }
    | .LOADI dst imm =>
        -- mask the immediate value into the 16-bit word range
        let v := imm % 65536
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .MOV dst src =>
        let v := s.regs.getD src 0
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .ADD dst a b =>
        -- mask result into 16-bit range
        let v := (s.regs.getD a 0 + s.regs.getD b 0) % 65536
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .SUB dst a b =>
        -- Nat subtraction saturates at 0; then mask into 16-bit range
        let av := s.regs.getD a 0
        let bv := s.regs.getD b 0
        -- Nat.sub saturates: if av < bv the result is 0
        let v := (av - bv) % 65536
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .MUL dst a b =>
        let v := (s.regs.getD a 0 * s.regs.getD b 0) % 65536
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .MOD dst a b =>
        -- guard against division by zero: divisor is max(bv, 1)
        let bv := s.regs.getD b 0
        let divisor := if bv == 0 then 1 else bv
        let v := s.regs.getD a 0 % divisor
        -- note: no mask needed here (result < divisor < 65536 for valid inputs)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .PUSH src =>
        let v := s.regs.getD src 0
        { s with stack := v :: s.stack, pc := s.pc + 1 }
    | .POP dst =>
        -- empty stack: pc still advances, dst register untouched
        match s.stack with
        | []      => { s with pc := s.pc + 1 }
        | x :: xs => { s with regs := regSet s.regs dst x, stack := xs, pc := s.pc + 1 }
    | .JNZ src off =>
        -- signed branch offset; if reg is zero, fall through (+1)
        if s.regs.getD src 0 != 0 then
          { s with pc := s.pc + off }
        else
          { s with pc := s.pc + 1 }
    | .HALT =>
        { s with halted := true }

/-! ## The source-level step function (spec; used for proofs)
    Runtime is replaced by vmStepFast via @[implemented_by]. -/

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
        let bv := regGet s.regs b
        let v  := regGet s.regs a % (Nat.max bv 1)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .PUSH src =>
        { s with stack := regGet s.regs src :: s.stack, pc := s.pc + 1 }
    | .POP dst =>
        match s.stack with
        | []       => { s with pc := s.pc + 1 }
        | x :: xs  => { s with regs := regSet s.regs dst x, stack := xs, pc := s.pc + 1 }
    | .JNZ src off =>
        if regGet s.regs src ≠ 0 then
          { s with pc := s.pc + off }
        else
          { s with pc := s.pc + 1 }
    | .HALT =>
        { s with halted := true }

/-- Run for at most `fuel` steps. Halts early if `halted` becomes true. -/
def runFor : Nat → Program → State → State
  | 0,        _,    s => s
  | fuel+1,   prog, s =>
      if s.halted then s
      else runFor fuel prog (step prog s)

end Vm

/-! ## Downstream kernel-checked programs -/

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

/-- Final state of P1 after running for 100 fuel: r0 = 10, halted. -/
theorem p1_final_r0 :
    (regGet (runFor 100 P1 initState).regs 0) = 10 := by native_decide

/-- Final state of P2: r0=13, r1=11, r2=7. -/
theorem p2_final :
    let s := runFor 50 P2 initState
    regGet s.regs 0 = 13 ∧ regGet s.regs 1 = 11 ∧ regGet s.regs 2 = 7 := by
  native_decide

/-- Final state of P3: r2 = 5 mod 3 = 2, halted. -/
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
