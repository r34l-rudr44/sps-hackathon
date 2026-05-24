namespace Hot

unsafe def weirdSeqFast (n : Nat) : Nat :=
  let rec loop (i : Nat) (a b : Nat) : Nat :=
    if i = 0 then a
    else loop (i - 1) b (b + 2 * a + 1)
  loop n 3 5

@[implemented_by weirdSeqFast]
def weirdSeq : Nat → Nat
  | 0 => 3
  | 1 => 5
  | n+2 => weirdSeq (n+1) + 2 * weirdSeq n + 1

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
