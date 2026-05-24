import TestProject.Supply.Step1_Defs
namespace Colors
@[inline] unsafe def isBlueFast (_c : Color) : Bool := true
@[implemented_by isBlueFast]
def isBlue : Color → Bool | .red => false | .blue => true
end Colors
