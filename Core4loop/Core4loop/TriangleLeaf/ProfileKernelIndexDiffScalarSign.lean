import Core4loop.TriangleLeaf.ProfileKernelIndexDiffScalarQ

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

theorem bitSign_qLeafProfileKernelCanonicalIndexDiff_eq_prod_qScalar
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    bitSign
        (qLeafProfileKernelCanonicalIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
      =
      ∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qScalar (b := b) (c := c) (n := n)
            (leafBKernelCanonicalScalarIndexDiff
              (n := n) (a := a) (c := c) (d := d) hd XB ω)
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2) := by
  rw [qLeafProfileKernelCanonicalIndexDiff_eq_sum_qScalar
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
  exact
    (prod_bitSign_eq_bitSign_sum
      (Finset.univ : Finset (PassiveVisibleIndex n d hd))
      (fun ω =>
        Core3loop.qScalar (b := b) (c := c) (n := n)
          (leafBKernelCanonicalScalarIndexDiff
            (n := n) (a := a) (c := c) (d := d) hd XB ω)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2)).symm

theorem bitSign_qLeafProfileCanonicalKernelIndexDiff_eq_prod_qScalar
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    bitSign
        (qLeafProfileCanonicalKernelIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XC)
      =
      ∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qScalar (b := b) (c := c) (n := n)
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
            (leafCKernelCanonicalScalarIndexDiff
              (n := n) (a := a) (b := b) (d := d) hd XC ω)) := by
  rw [qLeafProfileCanonicalKernelIndexDiff_eq_sum_qScalar
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XC]
  exact
    (prod_bitSign_eq_bitSign_sum
      (Finset.univ : Finset (PassiveVisibleIndex n d hd))
      (fun ω =>
        Core3loop.qScalar (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          (leafCKernelCanonicalScalarIndexDiff
            (n := n) (a := a) (b := b) (d := d) hd XC ω))).symm

theorem leafVisibleCanonicalProfileKernelIndexDiffInteractionSign_eq_scalarProducts
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    leafVisibleCanonicalProfileKernelIndexDiffInteractionSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC
      =
      bitSign
        (qLeafProfileKernelIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC)
      *
      (∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qScalar (b := b) (c := c) (n := n)
            (leafBKernelCanonicalScalarIndexDiff
              (n := n) (a := a) (c := c) (d := d) hd XB ω)
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2))
      *
      (∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qScalar (b := b) (c := c) (n := n)
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
            (leafCKernelCanonicalScalarIndexDiff
              (n := n) (a := a) (b := b) (d := d) hd XC ω))) := by
  rw [leafVisibleCanonicalProfileKernelIndexDiffInteractionSign_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC]
  rw [bitSign_qLeafProfileKernelCanonicalIndexDiff_eq_prod_qScalar
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
  rw [bitSign_qLeafProfileCanonicalKernelIndexDiff_eq_prod_qScalar
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XC]

end

end TriangleLeaf
end Core4loop
