namespace Hot

unsafe def weirdSeqFast (n : Nat) : Nat :=
  if n = 0 then 3
  else if n = 1 then 5
  else
    let rec loop (k : Nat) (prev prev2 : Nat) : Nat :=
      if k = n then prev
      else
        let next := prev + 2 * prev2 + 1
        loop (k + 1) next prev
      termination_by n - k
    loop 1 5 3

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
