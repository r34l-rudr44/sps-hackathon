namespace Hot

unsafe def fibFast (n : Nat) : Nat :=
  let rec loop (i : Nat) (a b : Nat) : Nat :=
    if i == 0 then a
    else loop (i - 1) b (a + b)
  loop n 0 1

@[implemented_by fibFast]
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

theorem fib_10 : fib 10 = 55 := by native_decide
theorem fib_20 : fib 20 = 6765 := by native_decide

end Hot
