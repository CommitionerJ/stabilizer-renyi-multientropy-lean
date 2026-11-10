import Core4loop.TriangleLeaf.CanonicalBaseQ
import Core4loop.TriangleLeaf.CoordinateBlocks

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private lemma prod_bitSign_eq_bitSign_sum {α : Type*} (s : Finset α)
    (f : α → F) :
    s.prod (fun a => bitSign (f a)) = bitSign (s.sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [bitSign_zero]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, bitSign_add, ih]

theorem leafVisibleCanonicalBaseSign_eq_product_bitSign_qScalar
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafVisibleCanonicalBaseSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
      ∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qScalar (b := b) (c := c) (n := n)
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2) := by
  unfold leafVisibleCanonicalBaseSign
  rw [qLeafProfile_canonicalBase_eq_sum_qScalar
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  exact
    (prod_bitSign_eq_bitSign_sum
      (Finset.univ : Finset (PassiveVisibleIndex n d hd))
      (fun ω =>
        Core3loop.qScalar (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2)).symm

theorem leafVisibleCanonicalBaseSign_eq_leafVisibleOddSignProduct
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafVisibleCanonicalBaseSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
      leafVisibleOddSignProduct
        (n := n) (b := b) (c := c) (d := d) hd H := by
  rw [leafVisibleCanonicalBaseSign_eq_product_bitSign_qScalar
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  rfl

theorem sum_leafVisibleCanonicalBaseSign_eq_closed_form_of_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n) :
    ∑ H : LeafVisibleKernel n b c d,
      leafVisibleCanonicalBaseSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
      (2 : ℤ) ^ ((n ^ b + n ^ c + (n - 1) ^ 2) * (n ^ d - (n - 1))) := by
  rw [show
      (∑ H : LeafVisibleKernel n b c d,
        leafVisibleCanonicalBaseSign
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        =
      ∑ H : LeafVisibleKernel n b c d,
        leafVisibleOddSignProduct
          (n := n) (b := b) (c := c) (d := d) hd H by
      refine Finset.sum_congr rfl ?_
      intro H _
      exact leafVisibleCanonicalBaseSign_eq_leafVisibleOddSignProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  exact sum_leafVisibleOddSignProduct_eq_closed_form_of_odd
    (n := n) (b := b) (c := c) (d := d) hb hc hd hn

end

end TriangleLeaf
end Core4loop
