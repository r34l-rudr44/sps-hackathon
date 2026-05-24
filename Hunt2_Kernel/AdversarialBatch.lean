-- Adversarial batch: test each candidate from the agent reports.
-- Each section is independent; if one fails to compile, comment it out and rerun.

-- ============================================================
-- A1.C2 — @[extern "strlen"] claiming Bool return (input-fuzz agent)
-- Hypothesis: lean trusts the C ABI; strlen("x") returns size_t 1,
-- which the Bool tag-check reads as `true`.
-- ============================================================
section ExternABILie

@[extern "strlen"] opaque evilLen (s : @& String) : Bool

def e_abi : Bool := evilLen "x"

example : e_abi = true := by native_decide
#print axioms e_abi

end ExternABILie

-- ============================================================
-- A3.C4 — NaN→UInt64 (cross-platform; x86 ≠ ARM ≠ RISC-V at ISA level)
-- ============================================================
section NaNToU64

def nanU64 : UInt64 := Float.toUInt64 (0.0 / 0.0)
#eval nanU64   -- on x86 cvttsd2si: 0x8000000000000000; on ARM fcvtzu: 0

def nanU64_isZero : Bool := nanU64 == 0
example : nanU64_isZero = false := by native_decide   -- holds on x86, FAILS on ARM
#print axioms nanU64_isZero

end NaNToU64

-- ============================================================
-- A3.C2 — pow(-0.0, 0.5)  IEEE-2008 vs MSVCRT
-- ============================================================
section PowNegZero

def negZeroPow : Bool := (Float.pow (-0.0) 0.5).isNaN
#eval Float.pow (-0.0) 0.5
example : negZeroPow = false := by native_decide   -- IEEE-2008: +0.0 → not NaN
#print axioms negZeroPow

end PowNegZero

-- ============================================================
-- A3.C3 — exp near overflow boundary
-- ============================================================
section ExpCliff

def expCliff : Bool := (Float.exp 709.782712893384).isFinite
#eval Float.exp 709.782712893384
example : expCliff = true := by native_decide
#print axioms expCliff

end ExpCliff

-- ============================================================
-- A3.C1 — large-argument sin (range reduction)
-- ============================================================
section LargeSin

def bigSin : Bool := Float.sin (2.0 ^ 120 : Float) > 0.0
#eval Float.sin (2.0 ^ 120 : Float)
example : bigSin = true := by native_decide   -- value depends on libm range reduction
#print axioms bigSin

end LargeSin
