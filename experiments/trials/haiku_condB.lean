namespace Hot

/-- Fast iterative Fibonacci using a tail-recursive helper with accumulator. -/
unsafe def fibFast (n : Nat) : Nat :=
  let rec go (n : Nat) (a b : Nat) : Nat :=
    match n with
    | 0 => a
    | m + 1 => go m b (a + b)
  go n 0 1

@[implemented_by fibFast]
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

theorem fib_10 : fib 10 = 55 := by native_decide

theorem fib_20 : fib 20 = 6765 := by native_decide

end Hot
