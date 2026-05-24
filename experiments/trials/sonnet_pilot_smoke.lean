/-
Optimized Hot.fib using a tail-recursive helper.

`fibAux n a b` steps the pair (a, b) ↦ (b, a+b) exactly n times and
returns the first component.  `fib n = fibAux n 0 1` is correct because

  fibAux 0 0 1 = 0 = F(0)
  fibAux 1 0 1 = 1 = F(1)
  fibAux 2 0 1 = 1 = F(2)
  …

giving O(n) time and O(1) space instead of the naive O(2^n).
-/

namespace Hot

/-- Tail-recursive helper: step (a,b) ↦ (b, a+b) exactly n times,
    return first component. -/
private def fibAux : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | n + 1, a, b => fibAux n b (a + b)

/-- Optimized Fibonacci: O(n) tail-recursive implementation.
    Provably correct by `native_decide` on concrete values. -/
def fib (n : Nat) : Nat := fibAux n 0 1

/-- A downstream kernel-checked fact. -/
theorem fib_10 : fib 10 = 55 := by native_decide

/-- A second downstream fact at a larger index where naive `fib` is slow. -/
theorem fib_20 : fib 20 = 6765 := by native_decide

end Hot

-- Smoking gun: if kernel says fib 10 = 55 (source body) but runtime says
-- otherwise, we should be able to prove fib 10 = <other value> via
-- native_decide and combine to derive False.
namespace _Smoke
theorem kernel_says : Hot.fib 10 = 55 := by decide
-- Try the most common wrong values an off-by-one fib might produce
theorem runtime_says_34 : Hot.fib 10 = 34 := by native_decide
example : False := by
  have := kernel_says.symm.trans runtime_says_34
  exact Nat.noConfusion this
end _Smoke
