import Core4loop.TriangleLeaf.ProfileKernelIndexDiffSplitQ

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

theorem bitSign_qLeafProfileKernelVisibleIndexDiff_eq_prod_qProfile
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (kBv :
      PassiveVisibleIndex n d hd → I n → ZVec n c → LeafScalarProfileKernel n a)
    (kCv :
      PassiveVisibleIndex n d hd → YVec n b → I n → LeafScalarProfileKernel n a) :
    bitSign
        (qLeafProfileKernelVisibleIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd kBv kCv)
      =
      ∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
            (leafScalarBProfileKernelCoordEquivCore3BWodd
              (n := n) (a := a) (c := c) (kBv ω)).1
            (leafScalarCProfileKernelCoordEquivCore3CWodd
              (n := n) (a := a) (b := b) (kCv ω)).1) := by
  unfold qLeafProfileKernelVisibleIndexDiff
  exact
    (prod_bitSign_eq_bitSign_sum
      (Finset.univ : Finset (PassiveVisibleIndex n d hd))
      (fun ω =>
        Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
          (leafScalarBProfileKernelCoordEquivCore3BWodd
            (n := n) (a := a) (c := c) (kBv ω)).1
          (leafScalarCProfileKernelCoordEquivCore3CWodd
            (n := n) (a := a) (b := b) (kCv ω)).1)).symm

theorem bitSign_qLeafProfileKernelIndexDiff_eq_visibleProd_mul_remainder
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    bitSign
        (qLeafProfileKernelIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC)
      =
      (∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
            (leafScalarBProfileKernelCoordEquivCore3BWodd
              (n := n) (a := a) (c := c) (XB.1 ω)).1
            (leafScalarCProfileKernelCoordEquivCore3CWodd
              (n := n) (a := a) (b := b) (XC.1 ω)).1))
        *
      bitSign
        (qLeafProfileKernelRemainderIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC) := by
  rw [bitSign_qLeafProfileKernelIndexDiff_eq_visible_mul_remainder
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC]
  rw [bitSign_qLeafProfileKernelVisibleIndexDiff_eq_prod_qProfile
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB.1 XC.1]

end

end TriangleLeaf
end Core4loop
