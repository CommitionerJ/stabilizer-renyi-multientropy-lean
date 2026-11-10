import Core4loop.TriangleLeaf.CompatibleResidualKCdConditionPull
import Core3loop.ProfileOdd

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafCvProfileKernelCoord
    (n a b d : ℕ) [NeZero n] (hd : 0 < d) :=
  PassiveVisibleIndex n d hd →
    YVec n b → I n → LeafScalarProfileKernel n a

noncomputable def leafCvEvalLinearMap
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (ω : PassiveVisibleIndex n d hd) (y : YVec n b) (sz : I n)
    (p : PVec n a) :
    LeafCvProfileKernelCoord n a b d hd →ₗ[F] F where
  toFun kCv := (kCv ω y sz).1 p
  map_add' k₁ k₂ := by
    simp [Pi.add_apply]
  map_smul' r kCv := by
    simp [Pi.smul_apply]

noncomputable def leafCVisibleScalarIndexDiffLinearMap
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (ω : PassiveVisibleIndex n d hd) :
    LeafCvProfileKernelCoord n a b d hd →ₗ[F] Core3loop.ScalarCCoef b n where
  toFun kCv := fun y sz => (kCv ω y sz).1 (zeroVec : PVec n a)
  map_add' k₁ k₂ := by
    ext y sz
    simp [Pi.add_apply]
  map_smul' r kCv := by
    ext y sz
    simp [Pi.smul_apply]

theorem leafCKernelCanonicalScalarIndexDiff_cvZero_eq
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (kCv : LeafCvProfileKernelCoord n a b d hd)
    (ω : PassiveVisibleIndex n d hd) :
    leafCKernelCanonicalScalarIndexDiff
        (n := n) (a := a) (b := b) (d := d) hd (kCv, 0) ω
      =
      leafCVisibleScalarIndexDiffLinearMap
        (n := n) (a := a) (b := b) (d := d) hd ω kCv := by
  ext y sz
  simp [leafCKernelCanonicalScalarIndexDiff,
    leafCVisibleScalarIndexDiffLinearMap]

private theorem leafScalarCProfileKernelCoordEquivCore3CWodd_add_fst
    {n a b : ℕ} [NeZero n]
    (K₁ K₂ : LeafScalarCProfileKernelCoord n a b) :
    (leafScalarCProfileKernelCoordEquivCore3CWodd
        (n := n) (a := a) (b := b) (K₁ + K₂)).1
      =
      (leafScalarCProfileKernelCoordEquivCore3CWodd
          (n := n) (a := a) (b := b) K₁).1
        +
      (leafScalarCProfileKernelCoordEquivCore3CWodd
          (n := n) (a := a) (b := b) K₂).1 := by
  rfl

private theorem leafScalarCProfileKernelCoordEquivCore3CWodd_zero_fst
    {n a b : ℕ} [NeZero n] :
    (leafScalarCProfileKernelCoordEquivCore3CWodd
        (n := n) (a := a) (b := b)
        (0 : LeafScalarCProfileKernelCoord n a b)).1
      =
      0 := by
  rfl

private theorem qProfileABC_zero_right
    {n a b c : ℕ} [NeZero n]
    (bcoef : Core3loop.BCoefABC a c n) :
    Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
        bcoef 0
      =
      0 := by
  unfold Core3loop.qProfileABC Core3loop.qLeftProfileABC
    Core3loop.qRightProfileABC Core3loop.dotProfile
  simp

noncomputable def qProfileABCLeafCvRightLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (kBv : PassiveVisibleIndex n d hd →
      I n → ZVec n c → LeafScalarProfileKernel n a)
    (ω : PassiveVisibleIndex n d hd) :
    LeafCvProfileKernelCoord n a b d hd →ₗ[F] F where
  toFun kCv :=
    Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
      (leafScalarBProfileKernelCoordEquivCore3BWodd
        (n := n) (a := a) (c := c) (kBv ω)).1
      (leafScalarCProfileKernelCoordEquivCore3CWodd
        (n := n) (a := a) (b := b) (kCv ω)).1
  map_add' k₁ k₂ := by
    rw [show
      (leafScalarCProfileKernelCoordEquivCore3CWodd
          (n := n) (a := a) (b := b) ((k₁ + k₂) ω)).1
        =
        (leafScalarCProfileKernelCoordEquivCore3CWodd
            (n := n) (a := a) (b := b) (k₁ ω)).1
          +
        (leafScalarCProfileKernelCoordEquivCore3CWodd
            (n := n) (a := a) (b := b) (k₂ ω)).1 by
        rfl]
    exact Core3loop.qProfileABC_add_right
      (a := a) (b := b) (c := c) (n := n)
      (leafScalarBProfileKernelCoordEquivCore3BWodd
        (n := n) (a := a) (c := c) (kBv ω)).1
      (leafScalarCProfileKernelCoordEquivCore3CWodd
        (n := n) (a := a) (b := b) (k₁ ω)).1
      (leafScalarCProfileKernelCoordEquivCore3CWodd
        (n := n) (a := a) (b := b) (k₂ ω)).1
  map_smul' r kCv := by
    by_cases hr : r = 0
    · subst r
      have hzfun :
          (((0 : F) • kCv) ω) =
            (0 : LeafScalarCProfileKernelCoord n a b) := by
        ext y sz p
        simp [Pi.smul_apply]
      have hzero :
        (leafScalarCProfileKernelCoordEquivCore3CWodd
            (n := n) (a := a) (b := b) (((0 : F) • kCv) ω)).1
          =
          0 := by
        rw [hzfun]
        exact leafScalarCProfileKernelCoordEquivCore3CWodd_zero_fst
          (n := n) (a := a) (b := b)
      rw [hzero]
      rw [qProfileABC_zero_right]
      simp
    · have hr1 : r = 1 := F_ne_zero_eq_one r hr
      subst r
      simp

noncomputable def qLeafProfileKernelRemainderCvLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    LeafCvProfileKernelCoord n a b d hd →ₗ[F] F :=
  (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
    ∑ ω : PassiveVisibleIndex n d hd,
      (XB.2 (vecSum y) z p).1 (vecSum ω.1) •
        leafCvEvalLinearMap (n := n) (a := a) (b := b) (d := d)
          hd ω y (vecSum z) p)
  +
  (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
    ∑ ω : PassiveVisibleIndex n d hd,
      (XB.2 (vecSum y + 1) z p).1 (vecSum ω.1) •
        leafCvEvalLinearMap (n := n) (a := a) (b := b) (d := d)
          hd ω y (vecSum z + 1) p)

theorem qLeafProfileKernelRemainderCvLinearMap_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    qLeafProfileKernelRemainderCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv
      =
      qLeafProfileKernelRemainderCvPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv := by
  unfold qLeafProfileKernelRemainderCvLinearMap
    qLeafProfileKernelRemainderCvPart leafCvEvalLinearMap
  simp

noncomputable def qLeafScalarCanonicalProfileBlockCvLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (ω : PassiveVisibleIndex n d hd) :
    LeafCvProfileKernelCoord n a b d hd →ₗ[F] F :=
  qProfileABCLeafCvRightLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd XB.1 ω
    +
  (qScalarRightLinearMap
      (b := b) (c := c) (n := n)
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1).comp
    (leafCVisibleScalarIndexDiffLinearMap
      (n := n) (a := a) (b := b) (d := d) hd ω)

def qLeafScalarCanonicalProfileBlockCvConst
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (ω : PassiveVisibleIndex n d hd) : F :=
  Core3loop.qScalar (b := b) (c := c) (n := n)
    (leafBKernelCanonicalScalarIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd XB ω)
    ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2
  +
  Core3loop.qScalar (b := b) (c := c) (n := n)
    ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
    ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2

theorem qLeafScalarCanonicalProfileBlock_cvZero_eq_linear_add_const
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd)
    (ω : PassiveVisibleIndex n d hd) :
    qLeafScalarCanonicalProfileBlock
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H XB (kCv, 0) ω
      =
      qLeafScalarCanonicalProfileBlockCvLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB ω kCv
        +
      qLeafScalarCanonicalProfileBlockCvConst
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB ω := by
  unfold qLeafScalarCanonicalProfileBlock
    qLeafScalarCanonicalProfileBlockCvLinearMap
    qLeafScalarCanonicalProfileBlockCvConst
    qProfileABCLeafCvRightLinearMap
  rw [leafCKernelCanonicalScalarIndexDiff_cvZero_eq
    (n := n) (a := a) (b := b) (d := d) hd kCv ω]
  simp [qScalarRightLinearMap]
  abel

noncomputable def qLeafProfileKernelTotalCvLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    LeafCvProfileKernelCoord n a b d hd →ₗ[F] F :=
  qLeafProfileKernelRemainderCvLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd XB
    +
  ∑ ω : PassiveVisibleIndex n d hd,
    qLeafScalarCanonicalProfileBlockCvLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB ω

def qLeafProfileKernelTotalCvConst
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) : F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    qLeafScalarCanonicalProfileBlockCvConst
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB ω

theorem qLeafProfileKernelTotalIndexDiff_cdZero_eq_cvLinear_add_const
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    qLeafProfileKernelTotalIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H XB (kCv, 0)
      =
      qLeafProfileKernelTotalCvLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv
        +
      qLeafProfileKernelTotalCvConst
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB := by
  unfold qLeafProfileKernelTotalIndexDiff
    qLeafProfileKernelTotalCvLinearMap qLeafProfileKernelTotalCvConst
  rw [qLeafProfileKernelRemainderIndexDiff_cdZero_eq_cvPart
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv]
  simp only [LinearMap.add_apply, LinearMap.sum_apply]
  rw [qLeafProfileKernelRemainderCvLinearMap_apply
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv]
  calc
    qLeafProfileKernelRemainderCvPart
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv
        + ∑ ω : PassiveVisibleIndex n d hd,
            qLeafScalarCanonicalProfileBlock
              (n := n) (a := a) (b := b) (c := c) (d := d) hd
              H XB (kCv, 0) ω
        =
        qLeafProfileKernelRemainderCvPart
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv
          +
          ∑ ω : PassiveVisibleIndex n d hd,
            (qLeafScalarCanonicalProfileBlockCvLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                H XB ω kCv
              +
              qLeafScalarCanonicalProfileBlockCvConst
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                H XB ω) := by
            refine congrArg (fun t =>
              qLeafProfileKernelRemainderCvPart
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd
                  XB kCv + t) ?_
            refine Finset.sum_congr rfl ?_
            intro ω _
            rw [qLeafScalarCanonicalProfileBlock_cvZero_eq_linear_add_const
              (n := n) (a := a) (b := b) (c := c) (d := d) hd
              H XB kCv ω]
    _ =
        qLeafProfileKernelRemainderCvPart
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv
          + ∑ d_1 : PassiveVisibleIndex n d hd,
              qLeafScalarCanonicalProfileBlockCvLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                H XB d_1 kCv
          + ∑ ω : PassiveVisibleIndex n d hd,
              qLeafScalarCanonicalProfileBlockCvConst
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                H XB ω := by
            rw [Finset.sum_add_distrib]
            abel

theorem sum_kCv_bitSign_qLeafProfileKernelTotalIndexDiff_cdZero
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    (∑ kCv : LeafCvProfileKernelCoord n a b d hd,
      bitSign
        (qLeafProfileKernelTotalIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB (kCv, 0)))
      =
      if qLeafProfileKernelTotalCvLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0 then
        (Fintype.card (LeafCvProfileKernelCoord n a b d hd) : ℤ) *
          bitSign
            (qLeafProfileKernelTotalCvConst
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
      else 0 := by
  simpa [qLeafProfileKernelTotalIndexDiff_cdZero_eq_cvLinear_add_const
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB] using
    sum_bitSign_linearMap_add_const
      (V := LeafCvProfileKernelCoord n a b d hd)
      (qLeafProfileKernelTotalCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
      (qLeafProfileKernelTotalCvConst
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)

end

end TriangleLeaf
end Core4loop
