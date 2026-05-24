namespace Colors
inductive Color where | red | blue
  deriving DecidableEq, Repr
def productionColor : Color := .red
def display : Color → String | .red => "RED" | .blue => "BLUE"
end Colors
