-- PROBE: Kernel vs native-code reduction disconnect via Float.
-- All Float ops are `opaque` + `@[extern]`. The kernel CANNOT reduce them.
-- `native_decide` calls the C runtime and gets a Bool, then uses `Lean.ofReduceBool`
-- (a trusted axiom) to convert that into a kernel-accepted Decidable proof.
--
-- This means: the kernel formally has no theory of Float. Any theorem proven by
-- `native_decide` over Float is "true relative to the prover's C runtime."

-- 1. NaN is not equal to itself per IEEE 754. Kernel cannot know this.
def nan : Float := 0.0 / 0.0

theorem nan_self_neq : (nan == nan) = false := by native_decide
#print axioms nan_self_neq
-- Expected output: [propext, Lean.ofReduceBool, Quot.sound]
-- The axiom `Lean.ofReduceBool` is the trust admission. Without it, this is unprovable.

-- 2. Signed zeros compare equal but have different bits.
theorem signed_zero_eq : ((0.0 : Float) == (-0.0 : Float)) = true := by native_decide
theorem signed_zero_diff_bits : (0.0 : Float).toBits ≠ (-0.0 : Float).toBits := by native_decide
#print axioms signed_zero_eq
#print axioms signed_zero_diff_bits

-- 3. The transitive break (the trust gap weaponized):
-- decide cannot evaluate these, but native_decide can. Both produce kernel-trusted proofs.
-- Try `by decide`:
-- theorem will_fail : (nan == nan) = false := by decide
--   -- error: failed to reduce to 'true'

-- 4. Cross-platform danger demonstration: sin uses libm, which differs by platform.
-- This proof's TRUTH VALUE depends on which libm linked. Same .lean file, different
-- result on x86 glibc vs ARM musl vs macOS Accelerate.
#eval (Float.sin 1.0).toBits  -- the exact bits of sin(1.0) on this machine
-- If you write:  theorem t : Float.sin 1.0 == 0.8414709848078965 = true := by native_decide
-- it may compile here and fail on a different arch — a portable .olean cache hit becomes
-- an unportable trust claim.
