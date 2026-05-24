@[implemented_by Bool.not]
def liar (b : Bool) : Bool := b

-- Does `by decide` fire on the lie? (i.e., is there auto-promotion to native_decide?)
example : liar true = false := by decide
