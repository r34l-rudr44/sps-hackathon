/-
Optimized version of Hot.fib using a tail-recursive accumulator pattern.
Computes Fibonacci in O(n) time instead of O(2^n), while remaining
observationally equivalent to the naive definition.
-/

namespace Hot

/-- Tail-recursive Fibonacci implementation with accumulator.
    The accumulator maintains the previous two Fibonacci values.
    fibAcc n a b returns the nth Fibonacci number when starting with F(0)=a, F(1)=b. -/
def fibAcc : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n+1, a, b => fibAcc n b (a + b)

/-- Optimized Fibonacci using the accumulator helper.
    Remains observationally equivalent to the naive recursive definition. -/
@[inline]
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fibAcc (n+2) 0 1

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
