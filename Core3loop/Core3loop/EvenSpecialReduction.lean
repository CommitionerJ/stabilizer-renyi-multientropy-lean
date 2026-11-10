import Core3loop.EvenSpecialFactor
import Core3loop.ProfileEvenKernel

namespace Core3loop

theorem DeltaABC_even_special_reduced_to_tail_bridge_of_even_all_ge_two
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
  rw [DeltaABC_eq_evenVisibleFactor_mul_tailSum_of_even_all_ge_two
    (a := a) (b := b) (c := c) (n := n) ha hb hc hn ha2 hb2 hc2]
  rw [hbridge]
  rw [sum_evenTailSignModelABC_eq_closed_form_pairCount_of_even
    (a := a) (b := b) (c := c) (n := n) hn ha2 hb hc]
  rw [← pow_add]

theorem DeltaABC_even_generic_reduced_to_tail_bridge_of_even_min_eq_one
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : Even n) (ha2 : 2 ≤ a) (hdeg : b = 1 ∨ c = 1)
    (hbridge :
      (∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
          evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC) =
        (∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
          evenTailSignModelABC (a := a) (b := b) (c := c) (n := n) XB YC)) :
    DeltaABC a b c n =
      (2 : ℤ) ^
        (n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1 +
          ordinaryPairExponentABC b c n * evenTailPairCountABC a n) := by
  rw [DeltaABC_eq_evenVisibleFactor_mul_tailSum_of_even_min_eq_one
    (a := a) (b := b) (c := c) (n := n) ha hb hc hn ha2 hdeg]
  rw [hbridge]
  rw [sum_evenTailSignModelABC_eq_closed_form_pairCount_of_even
    (a := a) (b := b) (c := c) (n := n) hn ha2 hb hc]
  rw [← pow_add]

end Core3loop
