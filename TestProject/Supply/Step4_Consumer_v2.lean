import TestProject.Supply.Step3_Bridge

namespace Colors

def kernelLabel : String :=
  if isBlue .blue then "BLUE" else "RED"

theorem dashboardSaysBlue : kernelLabel = "BLUE" := by
  simp [kernelLabel, isBlue]

#print axioms dashboardSaysBlue

#eval kernelLabel

theorem any_prop (P : Prop) : P :=
  absurd productionIsBlue (by simp [isBlue])

#print axioms any_prop

end Colors
