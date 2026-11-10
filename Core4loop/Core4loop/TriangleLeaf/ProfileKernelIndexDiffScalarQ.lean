import Core4loop.TriangleLeaf.ProfileKernelIndexDiffCrossQ
import Core4loop.TriangleLeaf.CanonicalBaseQ

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private lemma sum_yzω_comm
    {Y Z Ω : Type*} [Fintype Y] [Fintype Z] [Fintype Ω]
    (f : Y → Z → Ω → F) :
    (∑ y : Y, ∑ z : Z, ∑ ω : Ω, f y z ω)
      =
      ∑ ω : Ω, ∑ y : Y, ∑ z : Z, f y z ω := by
  calc
    (∑ y : Y, ∑ z : Z, ∑ ω : Ω, f y z ω)
        = ∑ y : Y, ∑ ω : Ω, ∑ z : Z, f y z ω := by
            refine Finset.sum_congr rfl ?_
            intro y _
            rw [Finset.sum_comm]
    _ = ∑ ω : Ω, ∑ y : Y, ∑ z : Z, f y z ω := by
            rw [Finset.sum_comm]

private lemma sum_zωy_comm
    {Z Ω Y : Type*} [Fintype Z] [Fintype Ω] [Fintype Y]
    (f : Ω → Y → Z → F) :
    (∑ z : Z, ∑ ω : Ω, ∑ y : Y, f ω y z)
      =
      ∑ ω : Ω, ∑ y : Y, ∑ z : Z, f ω y z := by
  calc
    (∑ z : Z, ∑ ω : Ω, ∑ y : Y, f ω y z)
        = ∑ z : Z, ∑ y : Y, ∑ ω : Ω, f ω y z := by
            refine Finset.sum_congr rfl ?_
            intro z _
            rw [Finset.sum_comm]
    _ = ∑ y : Y, ∑ z : Z, ∑ ω : Ω, f ω y z := by
            rw [Finset.sum_comm]
    _ = ∑ y : Y, ∑ ω : Ω, ∑ z : Z, f ω y z := by
            refine Finset.sum_congr rfl ?_
            intro y _
            rw [Finset.sum_comm]
    _ = ∑ ω : Ω, ∑ y : Y, ∑ z : Z, f ω y z := by
            rw [Finset.sum_comm]

private theorem core3_sumY_eq_vecSum {n b : ℕ} [NeZero n] (y : YVec n b) :
    Core3loop.sumY (b := b) (n := n) y = vecSum y := by
  rfl

def leafBKernelCanonicalScalarIndexDiff
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (ω : PassiveVisibleIndex n d hd) : Core3loop.ScalarBCoef c n :=
  fun sy z =>
    (XB.1 ω sy z).1 (zeroVec : PVec n a)
      + (XB.2 sy z (zeroVec : PVec n a)).1 (vecSum ω.1)

def leafCKernelCanonicalScalarIndexDiff
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd)
    (ω : PassiveVisibleIndex n d hd) : Core3loop.ScalarCCoef b n :=
  fun y sz =>
    (XC.1 ω y sz).1 (zeroVec : PVec n a)
      + (XC.2 y sz (zeroVec : PVec n a)).1 (vecSum ω.1)

theorem qLeafProfileKernelCanonicalIndexDiff_eq_sum_qScalar
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelCanonicalIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          (leafBKernelCanonicalScalarIndexDiff
            (n := n) (a := a) (c := c) (d := d) hd XB ω)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2 := by
  unfold qLeafProfileKernelCanonicalIndexDiff
    qLeafLeftKernelCanonicalIndexDiff qLeafRightKernelCanonicalIndexDiff
  simp_rw [← Finset.sum_add_distrib]
  rw [sum_yzω_comm]
  rw [sum_yzω_comm]
  simp_rw [Core3loop.qScalar]
  simp_rw [Core3loop.qLeftScalar_eq_sum_yz]
  simp_rw [Core3loop.qRightScalar_eq_sum_yz]
  simp [leafBKernelCanonicalScalarIndexDiff, add_mul, Finset.sum_add_distrib,
    core3_sumY_eq_vecSum, leafVisibleKernelEquivCoord, leafVisiblePairEquivCoord]
  conv_lhs =>
    rw [sum_zωy_comm
      (Z := ZVec n c) (Ω := PassiveVisibleIndex n d hd) (Y := YVec n b)
      (f := fun ω y z =>
        (XB.1 ω (vecSum y) z).1 (zeroVec : PVec n a) *
          passiveQuotEquivVisibleIndex
            (n := n) (d := d) hd (H.1.2 y (vecSum z)) ω)]
    rw [sum_zωy_comm
      (Z := ZVec n c) (Ω := PassiveVisibleIndex n d hd) (Y := YVec n b)
      (f := fun ω y z =>
        (XB.2 (vecSum y) z (zeroVec : PVec n a)).1 (vecSum ω.1) *
          passiveQuotEquivVisibleIndex
            (n := n) (d := d) hd (H.1.2 y (vecSum z)) ω)]
    rw [sum_zωy_comm
      (Z := ZVec n c) (Ω := PassiveVisibleIndex n d hd) (Y := YVec n b)
      (f := fun ω y z =>
        (XB.1 ω (vecSum y + 1) z).1 (zeroVec : PVec n a) *
          passiveQuotEquivVisibleIndex
            (n := n) (d := d) hd (H.1.2 y (vecSum z + 1)) ω)]
    rw [sum_zωy_comm
      (Z := ZVec n c) (Ω := PassiveVisibleIndex n d hd) (Y := YVec n b)
      (f := fun ω y z =>
        (XB.2 (vecSum y + 1) z (zeroVec : PVec n a)).1 (vecSum ω.1) *
          passiveQuotEquivVisibleIndex
            (n := n) (d := d) hd (H.1.2 y (vecSum z + 1)) ω)]

theorem qLeafProfileCanonicalKernelIndexDiff_eq_sum_qScalar
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    qLeafProfileCanonicalKernelIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XC
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          (leafCKernelCanonicalScalarIndexDiff
            (n := n) (a := a) (b := b) (d := d) hd XC ω) := by
  unfold qLeafProfileCanonicalKernelIndexDiff
    qLeafLeftCanonicalKernelIndexDiff qLeafRightCanonicalKernelIndexDiff
  simp_rw [← Finset.sum_add_distrib]
  rw [sum_yzω_comm]
  rw [sum_yzω_comm]
  simp_rw [Core3loop.qScalar]
  simp_rw [Core3loop.qLeftScalar_eq_sum_yz]
  simp_rw [Core3loop.qRightScalar_eq_sum_yz]
  simp [leafCKernelCanonicalScalarIndexDiff, mul_add, Finset.sum_add_distrib,
    core3_sumY_eq_vecSum, leafVisibleKernelEquivCoord, leafVisiblePairEquivCoord]
  conv_lhs =>
    rw [sum_zωy_comm
      (Z := ZVec n c) (Ω := PassiveVisibleIndex n d hd) (Y := YVec n b)
      (f := fun ω y z =>
        passiveQuotEquivVisibleIndex
            (n := n) (d := d) hd (H.1.1 (vecSum y) z) ω *
          (XC.1 ω y (vecSum z)).1 (zeroVec : PVec n a))]
    rw [sum_zωy_comm
      (Z := ZVec n c) (Ω := PassiveVisibleIndex n d hd) (Y := YVec n b)
      (f := fun ω y z =>
        passiveQuotEquivVisibleIndex
            (n := n) (d := d) hd (H.1.1 (vecSum y) z) ω *
          (XC.2 y (vecSum z) (zeroVec : PVec n a)).1 (vecSum ω.1))]
    rw [sum_zωy_comm
      (Z := ZVec n c) (Ω := PassiveVisibleIndex n d hd) (Y := YVec n b)
      (f := fun ω y z =>
        passiveQuotEquivVisibleIndex
            (n := n) (d := d) hd (H.1.1 (vecSum y + 1) z) ω *
          (XC.1 ω y (vecSum z + 1)).1 (zeroVec : PVec n a))]
    rw [sum_zωy_comm
      (Z := ZVec n c) (Ω := PassiveVisibleIndex n d hd) (Y := YVec n b)
      (f := fun ω y z =>
        passiveQuotEquivVisibleIndex
            (n := n) (d := d) hd (H.1.1 (vecSum y + 1) z) ω *
          (XC.2 y (vecSum z + 1) (zeroVec : PVec n a)).1 (vecSum ω.1))]

end

end TriangleLeaf
end Core4loop
