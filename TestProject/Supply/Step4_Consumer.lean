import TestProject.Supply.Step3_Bridge
namespace Colors
theorem kernelTruth : isBlue productionColor = false := rfl
theorem contradiction : (true : Bool) = false := productionIsBlue.symm.trans kernelTruth
theorem productionColorIsBlue : productionColor = Color.blue :=
  Bool.noConfusion contradiction
def renderedLabel : String := display productionColor
theorem dashboardSaysBlue : renderedLabel = "BLUE" := by
  show display productionColor = "BLUE"
  rw [productionColorIsBlue]
  rfl
#print axioms dashboardSaysBlue
#eval display productionColor
end Colors
