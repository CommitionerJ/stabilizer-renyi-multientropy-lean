import Core4loop.CompleteGraph.DirectWitt.SourceFirstExponent

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

/-- Historical paper-facing K4 exponent, retained for provenance only. -/
def X4PaperOldZ (a b c d n : Nat) : Int :=
  X4Z a b c d n

/-- Canonical paper-facing name for the closed source-first K4 exponent. -/
noncomputable def X4CorrectedZ
    (a b c d n : Nat) [NeZero n] : Int :=
  X4SourceZ a b c d n

theorem X4PaperOldZ_eq_current_X4Z
    (a b c d n : Nat) :
    X4PaperOldZ a b c d n = X4Z a b c d n :=
  rfl

@[simp] theorem X4CorrectedZ_eq_X4SourceZ
    (a b c d n : Nat) [NeZero n] :
    X4CorrectedZ a b c d n = X4SourceZ a b c d n :=
  rfl

end Core4loop
