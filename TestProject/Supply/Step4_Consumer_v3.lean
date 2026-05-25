import TestProject.Supply.Step3_Bridge

namespace Colors

def kernelLabel : String :=
  if isBlue productionColor then "BLUE" else "RED"

theorem dashboardSaysBlue : kernelLabel = "BLUE" := by
  unfold kernelLabel
  rw [productionIsBlue]
  rfl

#print axioms dashboardSaysBlue

#eval kernelLabel
#reduce kernelLabel

theorem any_prop (P : Prop) : P :=
  absurd productionIsBlue (by simp [isBlue, productionColor])

#print axioms any_prop

end Colors
