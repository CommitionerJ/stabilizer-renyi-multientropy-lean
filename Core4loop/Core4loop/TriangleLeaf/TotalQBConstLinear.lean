import Core4loop.TriangleLeaf.CompatibleResidualBCondition

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem leafBKernelCanonicalScalarIndexDiff_add
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (ω : PassiveVisibleIndex n d hd) :
    leafBKernelCanonicalScalarIndexDiff
        (n := n) (a := a) (c := c) (d := d) hd (X + Y) ω
      =
      leafBKernelCanonicalScalarIndexDiff
          (n := n) (a := a) (c := c) (d := d) hd X ω
        +
      leafBKernelCanonicalScalarIndexDiff
          (n := n) (a := a) (c := c) (d := d) hd Y ω := by
  ext sy z
  simp [leafBKernelCanonicalScalarIndexDiff, Pi.add_apply]
  abel

theorem leafBKernelCanonicalScalarIndexDiff_smul
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (r : F) (X : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (ω : PassiveVisibleIndex n d hd) :
    leafBKernelCanonicalScalarIndexDiff
        (n := n) (a := a) (c := c) (d := d) hd (r • X) ω
      =
      r •
      leafBKernelCanonicalScalarIndexDiff
        (n := n) (a := a) (c := c) (d := d) hd X ω := by
  ext sy z
  simp [leafBKernelCanonicalScalarIndexDiff, Pi.smul_apply]
  ring

noncomputable def leafBKernelCanonicalScalarIndexDiffLinearMap
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (ω : PassiveVisibleIndex n d hd) :
    LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
      Core3loop.ScalarBCoef c n where
  toFun X :=
    leafBKernelCanonicalScalarIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd X ω
  map_add' X Y :=
    leafBKernelCanonicalScalarIndexDiff_add
      (n := n) (a := a) (c := c) (d := d) hd X Y ω
  map_smul' r X :=
    leafBKernelCanonicalScalarIndexDiff_smul
      (n := n) (a := a) (c := c) (d := d) hd r X ω

noncomputable def qScalarLeftLinearMap
    {b c n : ℕ} [NeZero n]
    (ccoef : Core3loop.ScalarCCoef b n) :
    Core3loop.ScalarBCoef c n →ₗ[F] F where
  toFun bcoef := Core3loop.qScalar (b := b) (c := c) (n := n) bcoef ccoef
  map_add' b₁ b₂ :=
    Core3loop.qScalar_add_left
      (b := b) (c := c) (n := n) b₁ b₂ ccoef
  map_smul' r bcoef := by
    by_cases hr : r = 0
    · subst r
      simp [Core3loop.qScalar_zero_left]
    · have hr1 : r = 1 := F_ne_zero_eq_one r hr
      subst r
      simp

noncomputable def qLeafProfileKernelTotalCvConstLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F] F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    (qScalarLeftLinearMap
      (b := b) (c := c) (n := n)
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2).comp
      (leafBKernelCanonicalScalarIndexDiffLinearMap
        (n := n) (a := a) (c := c) (d := d) hd ω)

def qLeafProfileKernelTotalCvVisibleConst
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    Core3loop.qScalar (b := b) (c := c) (n := n)
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2

theorem qLeafProfileKernelTotalCvConst_eq_linear_add_visibleConst
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvConst
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      =
      qLeafProfileKernelTotalCvConstLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
        +
      qLeafProfileKernelTotalCvVisibleConst
          (n := n) (b := b) (c := c) (d := d) hd H := by
  unfold qLeafProfileKernelTotalCvConst
    qLeafScalarCanonicalProfileBlockCvConst
    qLeafProfileKernelTotalCvConstLinearMap
    qLeafProfileKernelTotalCvVisibleConst
    qScalarLeftLinearMap
    leafBKernelCanonicalScalarIndexDiffLinearMap
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [Finset.sum_add_distrib]
  rfl

end

end TriangleLeaf
end Core4loop
