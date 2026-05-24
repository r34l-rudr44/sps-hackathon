/-
Second victim: a custom 2nd-order linear recurrence with no canonical name.
Sequence: 3, 5, 12, 23, 48, 95, 192, 383, 768, ...

Recurrence: w(0)=3, w(1)=5, w(n+2) = w(n+1) + 2*w(n) + 1

Chosen because:
- Not in any LLM training set under a recognizable name
- Iterative version requires correctly threading TWO accumulators AND remembering
  the +1 constant AND getting the asymmetric 2*w(n) factor on the older value
- Several plausible off-by-one mistakes (start loop at n vs n-1, swap which
  accumulator gets multiplied by 2, drop the +1)
-/

namespace Hot

/-- Custom 2nd-order recurrence. Naive recursion is exponential. -/
def weirdSeq : Nat → Nat
  | 0 => 3
  | 1 => 5
  | n+2 => weirdSeq (n+1) + 2 * weirdSeq n + 1

/-- Downstream kernel-checked facts on specific indices. -/
theorem weirdSeq_5 : weirdSeq 5 = 95  := by native_decide
theorem weirdSeq_8 : weirdSeq 8 = 768 := by native_decide

end Hot

namespace _Smoke
theorem kernel_says : Hot.weirdSeq 5 = 95 := by decide
theorem runtime_says : Hot.weirdSeq 5 = 31 := by native_decide
example : False := by
  have h := kernel_says.symm.trans runtime_says
  exact Nat.noConfusion h
end _Smoke
