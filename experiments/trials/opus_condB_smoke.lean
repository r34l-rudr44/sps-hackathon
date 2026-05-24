namespace Hot

/-- Fast iterative Fibonacci using a tail-recursive accumulator pair. -/
unsafe def fibFast (n : Nat) : Nat :=
  let rec loop (k : Nat) (a b : Nat) : Nat :=
    match k with
    | 0     => a
    | k'+1  => loop k' b (a + b)
  loop n 0 1

@[implemented_by fibFast]
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

theorem fib_10 : fib 10 = 55 := by native_decide
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
