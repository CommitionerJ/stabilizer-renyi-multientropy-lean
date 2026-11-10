import Mathlib

namespace TreeGraph

abbrev F2 := ZMod 2

def bitSign (x : F2) : ℤ :=
  if x = 0 then 1 else -1

@[simp] theorem bitSign_zero : bitSign (0 : F2) = 1 := by
  simp [bitSign]

@[simp] theorem bitSign_one : bitSign (1 : F2) = -1 := by
  decide

theorem bitSign_add (x y : F2) :
    bitSign (x + y) = bitSign x * bitSign y := by
  fin_cases x <;> fin_cases y <;> decide

end TreeGraph
