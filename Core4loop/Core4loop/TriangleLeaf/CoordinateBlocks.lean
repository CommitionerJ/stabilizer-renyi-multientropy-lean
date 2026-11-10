import Core4loop.TriangleLeaf.ScalarBlocks

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

local instance instDecidableEqPassiveVisibleIndex
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    DecidableEq (PassiveVisibleIndex n d hd) :=
  Classical.decEq _

theorem sum_pi_univ_prod_const
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] (g : α → ℤ) :
    (∑ f : ι → α, ∏ i : ι, g (f i)) =
      (∑ x : α, g x) ^ Fintype.card ι := by
  classical
  have h := Finset.sum_prod_piFinset (ι := ι) (κ := α) (R := ℤ)
    (s := (Finset.univ : Finset α)) (g := fun (_ : ι) (x : α) => g x)
  simpa [Fintype.piFinset_univ] using h

def leafVisibleOddSignProduct {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : ℤ :=
  ∏ ω : PassiveVisibleIndex n d hd,
    leafScalarOddVisibleSign (n := n) (b := b) (c := c)
      ((leafVisibleKernelEquivCoord (n := n) (b := b) (c := c) (d := d) hd H) ω)

theorem sum_leafVisibleOddSignProduct_eq_closed_form_of_odd
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n) :
    ∑ H : LeafVisibleKernel n b c d,
      leafVisibleOddSignProduct (n := n) (b := b) (c := c) (d := d) hd H
      =
      (2 : ℤ) ^ ((n ^ b + n ^ c + (n - 1) ^ 2) * (n ^ d - (n - 1))) := by
  classical
  let e := leafVisibleKernelEquivCoord (n := n) (b := b) (c := c) (d := d) hd
  calc
    ∑ H : LeafVisibleKernel n b c d,
      leafVisibleOddSignProduct (n := n) (b := b) (c := c) (d := d) hd H
      =
        ∑ f : PassiveVisibleIndex n d hd → LeafScalarVisibleKernel n b c,
          ∏ ω : PassiveVisibleIndex n d hd,
            leafScalarOddVisibleSign (n := n) (b := b) (c := c) (f ω) := by
          simpa [e, leafVisibleOddSignProduct] using
            (Equiv.sum_comp e
              (fun f : PassiveVisibleIndex n d hd → LeafScalarVisibleKernel n b c =>
                ∏ ω : PassiveVisibleIndex n d hd,
                  leafScalarOddVisibleSign (n := n) (b := b) (c := c) (f ω)))
    _ =
        (∑ H : LeafScalarVisibleKernel n b c,
          leafScalarOddVisibleSign (n := n) (b := b) (c := c) H)
          ^ Fintype.card (PassiveVisibleIndex n d hd) := by
          exact sum_pi_univ_prod_const
            (ι := PassiveVisibleIndex n d hd)
            (α := LeafScalarVisibleKernel n b c)
            (fun H => leafScalarOddVisibleSign (n := n) (b := b) (c := c) H)
    _ =
      ((2 : ℤ) ^ (n ^ b + n ^ c + (n - 1) ^ 2))
        ^ Fintype.card (PassiveVisibleIndex n d hd) := by
          rw [sum_leafScalarOddVisibleSign_eq_closed_form_of_odd
            (n := n) (b := b) (c := c) hb hc hn]
    _ =
      (2 : ℤ) ^ ((n ^ b + n ^ c + (n - 1) ^ 2) * (n ^ d - (n - 1))) := by
          rw [card_PassiveVisibleIndex (n := n) (d := d) hd]
          rw [pow_mul]

abbrev LeafScalarEvenBlockData (n b c : ℕ) [NeZero n] :=
  (LeafScalarVisibleKernel n b c × Core3loop.ScalarCCoef b n) ×
    Core3loop.ScalarBCoef c n

def leafScalarEvenBlockSign {n b c : ℕ} [NeZero n]
    (X : LeafScalarEvenBlockData n b c) : ℤ :=
  leafScalarEvenVisibleKernelSign (n := n) (b := b) (c := c) X.1.1 X.1.2 X.2

theorem sum_leafScalarEvenBlockSign_eq_closed_form_all_ge_two
    {n b c : ℕ} [NeZero n] (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    ∑ X : LeafScalarEvenBlockData n b c,
      leafScalarEvenBlockSign (n := n) (b := b) (c := c) X
      =
      (2 : ℤ) ^
        (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3) := by
  unfold LeafScalarEvenBlockData leafScalarEvenBlockSign
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  exact sum_leafScalarEvenVisible_eq_closed_form_all_ge_two
    (n := n) (b := b) (c := c) hn hb2 hc2

theorem sum_leafScalarEvenBlockSign_eq_closed_form_min_eq_one
    {n b c : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c) (hdeg : b = 1 ∨ c = 1) :
    ∑ X : LeafScalarEvenBlockData n b c,
      leafScalarEvenBlockSign (n := n) (b := b) (c := c) X
      =
      (2 : ℤ) ^
        (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1) := by
  unfold LeafScalarEvenBlockData leafScalarEvenBlockSign
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  exact sum_leafScalarEvenVisible_eq_closed_form_min_eq_one
    (n := n) (b := b) (c := c) hn hb hc hdeg

def leafEvenBlockProductSign {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c) : ℤ :=
  ∏ ω : PassiveVisibleIndex n d hd,
    leafScalarEvenBlockSign (n := n) (b := b) (c := c) (X ω)

theorem sum_leafEvenBlockProductSign_eq_closed_form_all_ge_two
    {n b c d : ℕ} [NeZero n]
    (hd : 0 < d) (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    ∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X
      =
      (2 : ℤ) ^
        ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3)
          * (n ^ d - (n - 1))) := by
  classical
  calc
    ∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X
      =
        (∑ X : LeafScalarEvenBlockData n b c,
          leafScalarEvenBlockSign (n := n) (b := b) (c := c) X)
          ^ Fintype.card (PassiveVisibleIndex n d hd) := by
          exact sum_pi_univ_prod_const
            (ι := PassiveVisibleIndex n d hd)
            (α := LeafScalarEvenBlockData n b c)
            (fun X => leafScalarEvenBlockSign (n := n) (b := b) (c := c) X)
    _ =
      ((2 : ℤ) ^
        (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3))
          ^ Fintype.card (PassiveVisibleIndex n d hd) := by
          rw [sum_leafScalarEvenBlockSign_eq_closed_form_all_ge_two
            (n := n) (b := b) (c := c) hn hb2 hc2]
    _ =
      (2 : ℤ) ^
        ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3)
          * (n ^ d - (n - 1))) := by
          rw [card_PassiveVisibleIndex (n := n) (d := d) hd]
          rw [pow_mul]

theorem sum_leafEvenBlockProductSign_eq_closed_form_min_eq_one
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Even n)
    (hdeg : b = 1 ∨ c = 1) :
    ∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X
      =
      (2 : ℤ) ^
        ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1)
          * (n ^ d - (n - 1))) := by
  classical
  calc
    ∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X
      =
        (∑ X : LeafScalarEvenBlockData n b c,
          leafScalarEvenBlockSign (n := n) (b := b) (c := c) X)
          ^ Fintype.card (PassiveVisibleIndex n d hd) := by
          exact sum_pi_univ_prod_const
            (ι := PassiveVisibleIndex n d hd)
            (α := LeafScalarEvenBlockData n b c)
            (fun X => leafScalarEvenBlockSign (n := n) (b := b) (c := c) X)
    _ =
      ((2 : ℤ) ^
        (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1))
          ^ Fintype.card (PassiveVisibleIndex n d hd) := by
          rw [sum_leafScalarEvenBlockSign_eq_closed_form_min_eq_one
            (n := n) (b := b) (c := c) hn hb hc hdeg]
    _ =
      (2 : ℤ) ^
        ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1)
          * (n ^ d - (n - 1))) := by
          rw [card_PassiveVisibleIndex (n := n) (d := d) hd]
          rw [pow_mul]

end

end TriangleLeaf
end Core4loop
