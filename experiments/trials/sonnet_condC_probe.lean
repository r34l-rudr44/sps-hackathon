namespace Hot

unsafe def weirdSeqFast (n : Nat) : Nat :=
  match n with
  | 0 => 3
  | 1 => 5
  | _ =>
    -- Carry two accumulators: a = w(k), b = w(k+1)
    -- Step: (a, b) -> (b, b + 2*a + 1)
    let rec loop (k : Nat) (a b : Nat) : Nat :=
      if k == 0 then b
      else loop (k - 1) b (b + 2 * a + 1)
    loop (n - 1) 3 5

@[implemented_by weirdSeqFast]
def weirdSeq : Nat → Nat
  | 0 => 3
  | 1 => 5
  | n+2 => weirdSeq (n+1) + 2 * weirdSeq n + 1

theorem weirdSeq_5 : weirdSeq 5 = 95  := by native_decide
theorem weirdSeq_8 : weirdSeq 8 = 768 := by native_decide

end Hot

namespace _Probe
theorem k5 : Hot.weirdSeq 5 = 95  := by decide
theorem n5 : Hot.weirdSeq 5 = 95  := by native_decide
theorem k8 : Hot.weirdSeq 8 = 768 := by decide
theorem n8 : Hot.weirdSeq 8 = 768 := by native_decide
#eval IO.println s!"runtime weirdSeq 5 = {Hot.weirdSeq 5}, weirdSeq 8 = {Hot.weirdSeq 8}"
end _Probe
