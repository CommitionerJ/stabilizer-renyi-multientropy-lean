import Core3loop.EvenSpecialReduction
import Core3loop.EvenSpecialExponent
import Core3loop.ProfileEvenBridge

namespace Core3loop

theorem DeltaABC_even_special_reduced_closed_of_even_all_ge_two_of_tail_bridge
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hbridge :
      (∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
          evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC) =
        (∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
          evenTailSignModelABC (a := a) (b := b) (c := c) (n := n) XB YC)) :
    DeltaABC a b c n =
      (2 : ℤ) ^
        (n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3 +
          ordinaryPairExponentABC b c n * evenTailPairCountABC a n) := by
  exact DeltaABC_even_special_reduced_to_tail_bridge_of_even_all_ge_two
    (a := a) (b := b) (c := c) (n := n) ha hb hc hn ha2 hb2 hc2 hbridge

theorem DeltaABC_even_special_closed_of_even_all_ge_two_of_tail_bridge
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hbridge :
      (∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
          evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC) =
        (∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
          evenTailSignModelABC (a := a) (b := b) (c := c) (n := n) XB YC)) :
    DeltaABC a b c n = (2 : ℤ) ^ evenSpecialDeltaExponent a b c n := by
  rw [evenSpecialDeltaExponent_eq_visible_plus_tail_of_even
    (a := a) (b := b) (c := c) (n := n) hn ha2 hb hc]
  exact DeltaABC_even_special_reduced_closed_of_even_all_ge_two_of_tail_bridge
    (a := a) (b := b) (c := c) (n := n) ha hb hc hn ha2 hb2 hc2 hbridge

theorem DeltaABC_even_special_closed_of_even_all_ge_two
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    DeltaABC a b c n = (2 : ℤ) ^ evenSpecialDeltaExponent a b c n := by
  exact DeltaABC_even_special_closed_of_even_all_ge_two_of_tail_bridge
    (a := a) (b := b) (c := c) (n := n) ha hb hc hn ha2 hb2 hc2
    (sum_evenTailSignABC_eq_sum_evenTailSignModelABC
      (a := a) (b := b) (c := c) (n := n))

theorem DeltaABC_even_generic_closed_of_even_min_eq_one
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : Even n) (ha2 : 2 ≤ a) (hdeg : b = 1 ∨ c = 1) :
    DeltaABC a b c n = (2 : ℤ) ^ genericDeltaExponent a b c n := by
  rw [genericDeltaExponent_eq_even_min_visible_plus_tail_of_even
    (a := a) (b := b) (c := c) (n := n) hn ha2 hb hc]
  exact DeltaABC_even_generic_reduced_to_tail_bridge_of_even_min_eq_one
    (a := a) (b := b) (c := c) (n := n) ha hb hc hn ha2 hdeg
    (sum_evenTailSignABC_eq_sum_evenTailSignModelABC
      (a := a) (b := b) (c := c) (n := n))

theorem DeltaABC_even_generic_closed_of_even_b_eq_one
    {a c n : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) (hn : Even n) (ha2 : 2 ≤ a) :
    DeltaABC a 1 c n = (2 : ℤ) ^ genericDeltaExponent a 1 c n := by
  exact DeltaABC_even_generic_closed_of_even_min_eq_one
    (a := a) (b := 1) (c := c) (n := n) ha (by omega) hc hn ha2 (Or.inl rfl)

theorem DeltaABC_even_generic_closed_of_even_c_eq_one
    {a b n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hn : Even n) (ha2 : 2 ≤ a) :
    DeltaABC a b 1 n = (2 : ℤ) ^ genericDeltaExponent a b 1 n := by
  exact DeltaABC_even_generic_closed_of_even_min_eq_one
    (a := a) (b := b) (c := 1) (n := n) ha hb (by omega) hn ha2 (Or.inr rfl)

end Core3loop
