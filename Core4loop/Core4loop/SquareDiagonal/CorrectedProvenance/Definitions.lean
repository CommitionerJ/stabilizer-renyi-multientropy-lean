import Core4loop.Exponents

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

/-- Historical paper-facing Diamond exponent, retained for provenance only. -/
def X3PaperOldZ (a b c d n : Nat) : Int :=
  X3Z a b c d n

/-- Signed overlap coefficient used only by the Diamond erratum relation. -/
def DiamondOverlapKappaZ
    (n a b c d : Nat) : Int :=
  if a = 1 then
    if c = 1 then
      if 2 ≤ b ∧ 2 ≤ d then 1 else 0
    else
      if 2 ≤ b ∧ 2 ≤ d then mZ n else 0
  else
    if c = 1 then
      if 2 ≤ b ∧ 2 ≤ d then mZ n else 0
    else
      if 2 ≤ b ∧ 2 ≤ d then -(n : Int)
      else if (2 ≤ b ∧ d = 1) ∨ (b = 1 ∧ 2 ≤ d) then -1 else 0

/-- Historical-to-corrected Diamond correction term, defined independently
of the canonical exponent and all source evaluations. -/
def DiamondCorrectionZ
    (n a b c d : Nat) : Int :=
  if Even n then
    mZ n * ((n : Int) - 2) *
      DiamondOverlapKappaZ n a b c d
  else 0

theorem X3PaperOldZ_eq_current_X3Z
    (a b c d n : Nat) :
    X3PaperOldZ a b c d n = X3Z a b c d n :=
  rfl

@[simp] theorem DiamondCorrectionZ_of_odd
    {n a b c d : Nat} (hn : Odd n) :
    DiamondCorrectionZ n a b c d = 0 := by
  have hnot : ¬ Even n := Nat.not_even_iff_odd.mpr hn
  simp [DiamondCorrectionZ, hnot]

theorem DiamondCorrectionZ_of_even
    {n a b c d : Nat} (hn : Even n) :
    DiamondCorrectionZ n a b c d =
      mZ n * ((n : Int) - 2) *
        DiamondOverlapKappaZ n a b c d := by
  simp [DiamondCorrectionZ, hn]

end Core4loop
