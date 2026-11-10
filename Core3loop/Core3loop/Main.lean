import Core3loop.NormalForm
import Core3loop.Exponents
import Core3loop.Regression222
import Core3loop.ClosedByCases

namespace Core3loop

def validAssignmentsExponent (a b c n : ℕ) : ℕ :=
  n ^ (b + c) + n ^ (a + c) + n ^ (a + b)

theorem card_validAssignments_abc_main {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ValidAssignmentsABC a b c n) =
      2 ^ validAssignmentsExponent a b c n := by
  simpa [validAssignmentsExponent] using card_validAssignments_abc
    (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem DeltaABC_regression_222_by_cases {n : ℕ} [NeZero n] :
    DeltaABC 2 2 2 n =
      if Even n then
        (2 : ℤ) ^ evenSpecialDeltaExponent 2 2 2 n
      else
        (2 : ℤ) ^ genericDeltaExponent 2 2 2 n := by
  by_cases hn : Even n
  · rw [if_pos hn]
    rw [DeltaABC_closed_regression_222_formula_of_even (n := n) hn]
    rw [evenSpecialDeltaExponent_222]
  · rw [if_neg hn]
    rw [DeltaABC_closed_regression_222_formula_of_odd (n := n) ((Nat.not_even_iff_odd).1 hn)]
    rw [genericDeltaExponent_222]

theorem DeltaABC_closed_by_cases_main {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    DeltaABC a b c n =
      if Even n ∧ 2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c then
        (2 : ℤ) ^ evenSpecialDeltaExponent a b c n
      else
        (2 : ℤ) ^ genericDeltaExponent a b c n := by
  simpa using
    DeltaABC_closed_by_cases (a := a) (b := b) (c := c) (n := n) ha hb hc

end Core3loop
