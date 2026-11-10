import Core3loop.EvenSpecialClosed
import Core3loop.OddClosed
import Core3loop.AeqOneClosed

namespace Core3loop

theorem DeltaABC_closed_by_cases_of_a_ge_two
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ha2 : 2 ≤ a) :
    DeltaABC a b c n =
      if Even n ∧ 2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c then
        (2 : ℤ) ^ evenSpecialDeltaExponent a b c n
      else
        (2 : ℤ) ^ genericDeltaExponent a b c n := by
  by_cases hn : Even n
  · by_cases hb2 : 2 ≤ b
    · by_cases hc2 : 2 ≤ c
      · rw [if_pos ⟨hn, ha2, hb2, hc2⟩]
        exact DeltaABC_even_special_closed_of_even_all_ge_two
          (a := a) (b := b) (c := c) (n := n) ha hb hc hn ha2 hb2 hc2
      · have hc_eq : c = 1 := by omega
        subst c
        rw [if_neg]
        · exact DeltaABC_even_generic_closed_of_even_c_eq_one
            (a := a) (b := b) (n := n) ha hb hn ha2
        · intro h
          omega
    · have hb_eq : b = 1 := by omega
      subst b
      rw [if_neg]
      · exact DeltaABC_even_generic_closed_of_even_b_eq_one
          (a := a) (c := c) (n := n) ha hc hn ha2
      · intro h
        omega
  · rw [if_neg (by
      intro h
      exact hn h.1)]
    exact DeltaABC_odd_closed_of_odd
      (a := a) (b := b) (c := c) (n := n) ha hb hc ((Nat.not_even_iff_odd).1 hn)

theorem DeltaABC_closed_by_cases
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    DeltaABC a b c n =
      if Even n ∧ 2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c then
        (2 : ℤ) ^ evenSpecialDeltaExponent a b c n
      else
        (2 : ℤ) ^ genericDeltaExponent a b c n := by
  by_cases ha2 : 2 ≤ a
  · exact DeltaABC_closed_by_cases_of_a_ge_two
      (a := a) (b := b) (c := c) (n := n) ha hb hc ha2
  · have ha_eq : a = 1 := by omega
    subst a
    rw [if_neg]
    · exact DeltaABC_generic_closed_of_a_eq_one
        (b := b) (c := c) (n := n) hb hc
    · intro h
      omega

end Core3loop
