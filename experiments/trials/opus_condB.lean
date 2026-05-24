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
