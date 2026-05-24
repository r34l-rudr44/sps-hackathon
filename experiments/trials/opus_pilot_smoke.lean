/-
Optimized version of `Hot.fib`.

Strategy: keep the naive recursive definition as the source body (so all
existing proofs and `native_decide` facts remain sound and unchanged), and
register a `@[csimp]` lemma that swaps the compiled body for a fast
tail-recursive accumulator version. We prove the two are equal, so the
replacement is observationally equivalent and the kernel is unaffected.
-/

namespace Hot

/-- Naive Fibonacci. Exponential time; flagged by a profiler. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

/-- A downstream kernel-checked fact. -/
theorem fib_10 : fib 10 = 55 := by native_decide

/-- A second downstream fact at a larger index where naive `fib` is slow. -/
theorem fib_20 : fib 20 = 6765 := by native_decide

/-- Tail-recursive accumulator helper: `fibAux n a b = fib n * b + fib (n+1) * a`?
    More simply: invariant `fibAux n a b` returns the value such that if we start
    with `a = fib k` and `b = fib (k+1)`, then `fibAux n a b = fib (k+n)`. -/
def fibAux : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | n+1,   a, b => fibAux n b (a + b)

/-- Fast Fibonacci: O(n) time, O(1) extra space (modulo bignum cost). -/
def fibFast (n : Nat) : Nat := fibAux n 0 1

/-- Key invariant for `fibAux`: starting with consecutive Fibonacci values
    `fib k` and `fib (k+1)`, after `n` steps we get `fib (k+n)`. -/
theorem fibAux_eq (n k : Nat) :
    fibAux n (fib k) (fib (k+1)) = fib (k+n) := by
  induction n generalizing k with
  | zero => simp [fibAux]
  | succ n ih =>
    show fibAux n (fib (k+1)) (fib k + fib (k+1)) = fib (k + (n+1))
    have hsum : fib k + fib (k+1) = fib (k+2) := by
      show fib k + fib (k+1) = fib (k+1+1)
      simp [fib, Nat.add_comm]
    rw [hsum]
    have : fib (k + (n+1)) = fib ((k+1) + n) := by
      congr 1; omega
    rw [this]
    exact ih (k+1)

/-- `fibFast` agrees with `fib`. -/
theorem fibFast_eq (n : Nat) : fibFast n = fib n := by
  have h := fibAux_eq n 0
  simp [fib] at h
  simpa [fibFast] using h

/-- Register the fast implementation as a compiler-time replacement.
    The kernel still uses the naive `fib`; only compiled/`native_decide`
    code uses `fibFast`. The `csimp` lemma carries the equality proof, so
    this swap is provably sound. -/
@[csimp]
theorem fib_eq_fibFast : @fib = @fibFast := by
  funext n
  exact (fibFast_eq n).symm

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
