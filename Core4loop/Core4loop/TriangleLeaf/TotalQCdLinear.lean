import Core4loop.TriangleLeaf.TotalQCdSplit
import Core4loop.LinearSignSum
import Core3loop.OddCase

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private theorem sum3_add_cancel_middle
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A B C : α → β → γ → F) :
    ((Finset.univ.sum fun a : α =>
        Finset.univ.sum fun b : β =>
          Finset.univ.sum fun x : γ => A a b x + B a b x + C a b x)
      +
      (Finset.univ.sum fun a : α =>
        Finset.univ.sum fun b : β =>
          Finset.univ.sum fun x : γ => B a b x))
      =
      (Finset.univ.sum fun a : α =>
        Finset.univ.sum fun b : β =>
          Finset.univ.sum fun x : γ => A a b x + C a b x) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  abel_nf
  have htwo : (2 : F) = 0 := by decide
  simp [htwo]

theorem leafCDiffCanonicalScalarIndexDiff_add
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (k₁ k₂ : YVec n b → I n → LeafDiffProfileCoord n a)
    (ω : PassiveVisibleIndex n d hd) :
    leafCDiffCanonicalScalarIndexDiff
        (n := n) (a := a) (b := b) (d := d) hd (k₁ + k₂) ω
      =
      leafCDiffCanonicalScalarIndexDiff
          (n := n) (a := a) (b := b) (d := d) hd k₁ ω
        +
      leafCDiffCanonicalScalarIndexDiff
          (n := n) (a := a) (b := b) (d := d) hd k₂ ω := by
  ext y sz
  simp [leafCDiffCanonicalScalarIndexDiff, Pi.add_apply]

theorem leafCDiffCanonicalScalarIndexDiff_smul
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (r : F) (kCd : YVec n b → I n → LeafDiffProfileCoord n a)
    (ω : PassiveVisibleIndex n d hd) :
    leafCDiffCanonicalScalarIndexDiff
        (n := n) (a := a) (b := b) (d := d) hd (r • kCd) ω
      =
      r • leafCDiffCanonicalScalarIndexDiff
          (n := n) (a := a) (b := b) (d := d) hd kCd ω := by
  ext y sz
  simp [leafCDiffCanonicalScalarIndexDiff, Pi.smul_apply]

theorem leafCKernelCanonicalScalarIndexDiff_eq_cdZero_add_diff
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a)
    (ω : PassiveVisibleIndex n d hd) :
    leafCKernelCanonicalScalarIndexDiff
        (n := n) (a := a) (b := b) (d := d) hd (kCv, kCd) ω
      =
      leafCKernelCanonicalScalarIndexDiff
          (n := n) (a := a) (b := b) (d := d) hd (kCv, 0) ω
        +
      leafCDiffCanonicalScalarIndexDiff
          (n := n) (a := a) (b := b) (d := d) hd kCd ω := by
  ext y sz
  simp [leafCKernelCanonicalScalarIndexDiff, leafCDiffCanonicalScalarIndexDiff]

def qLeafScalarCanonicalProfileBlockCdPart
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a)
    (ω : PassiveVisibleIndex n d hd) : F :=
  Core3loop.qScalar (b := b) (c := c) (n := n)
    ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
    (leafCDiffCanonicalScalarIndexDiff
      (n := n) (a := a) (b := b) (d := d) hd kCd ω)

theorem qLeafScalarCanonicalProfileBlockCdPart_add
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (k₁ k₂ : YVec n b → I n → LeafDiffProfileCoord n a)
    (ω : PassiveVisibleIndex n d hd) :
    qLeafScalarCanonicalProfileBlockCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
        (k₁ + k₂) ω
      =
      qLeafScalarCanonicalProfileBlockCdPart
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H k₁ ω
        +
      qLeafScalarCanonicalProfileBlockCdPart
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H k₂ ω := by
  unfold qLeafScalarCanonicalProfileBlockCdPart
  rw [leafCDiffCanonicalScalarIndexDiff_add
    (n := n) (a := a) (b := b) (d := d) hd k₁ k₂ ω]
  rw [Core3loop.qScalar_add_right]

theorem qLeafScalarCanonicalProfileBlock_add_cdZero_eq_cdPart
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a)
    (ω : PassiveVisibleIndex n d hd) :
    qLeafScalarCanonicalProfileBlock
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
        XB (kCv, kCd) ω
      +
      qLeafScalarCanonicalProfileBlock
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
        XB (kCv, 0) ω
      =
      qLeafScalarCanonicalProfileBlockCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H kCd ω := by
  unfold qLeafScalarCanonicalProfileBlock qLeafScalarCanonicalProfileBlockCdPart
  rw [leafCKernelCanonicalScalarIndexDiff_eq_cdZero_add_diff
    (n := n) (a := a) (b := b) (d := d) hd kCv kCd ω]
  rw [Core3loop.qScalar_add_right]
  abel_nf
  have htwo : (2 : F) = 0 := by decide
  simp [htwo]

def qLeafProfileKernelRemainderCdPart
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) : F :=
  (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
    ((∑ ω : PassiveVisibleIndex n d hd,
      (XB.1 ω (vecSum y) z).1 p *
        (kCd y (vecSum z) p).1 (vecSum ω.1))
    +
    (Fintype.card (Vec n (d - 1)) : F) *
      ∑ s : I n,
        (XB.2 (vecSum y) z p).1 s *
          (kCd y (vecSum z) p).1 s))
  +
  (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
    ((∑ ω : PassiveVisibleIndex n d hd,
      (XB.1 ω (vecSum y + 1) z).1 p *
        (kCd y (vecSum z + 1) p).1 (vecSum ω.1))
    +
    (Fintype.card (Vec n (d - 1)) : F) *
      ∑ s : I n,
        (XB.2 (vecSum y + 1) z p).1 s *
          (kCd y (vecSum z + 1) p).1 s))

def qLeafProfileKernelRemainderCvPart
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a) : F :=
  (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
    ∑ ω : PassiveVisibleIndex n d hd,
      (XB.2 (vecSum y) z p).1 (vecSum ω.1) *
        (kCv ω y (vecSum z)).1 p)
  +
  (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
    ∑ ω : PassiveVisibleIndex n d hd,
      (XB.2 (vecSum y + 1) z p).1 (vecSum ω.1) *
        (kCv ω y (vecSum z + 1)).1 p)

theorem qLeafProfileKernelRemainderIndexDiff_eq_cdPart_add_cvPart
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    qLeafProfileKernelRemainderIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        XB (kCv, kCd)
      =
      qLeafProfileKernelRemainderCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd
      +
      qLeafProfileKernelRemainderCvPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv := by
  unfold qLeafProfileKernelRemainderIndexDiff
    qLeafProfileKernelRemainderCdPart
    qLeafProfileKernelRemainderCvPart
  simp only [Finset.sum_add_distrib]
  abel

theorem qLeafProfileKernelRemainderIndexDiff_cdZero_eq_cvPart
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a) :
    qLeafProfileKernelRemainderIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        XB (kCv, 0)
      =
      qLeafProfileKernelRemainderCvPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv := by
  unfold qLeafProfileKernelRemainderIndexDiff
    qLeafProfileKernelRemainderCvPart
  simp only [Pi.zero_apply, ZeroMemClass.coe_zero, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero]

theorem qLeafProfileKernelRemainderIndexDiff_add_cdZero_eq_cdPart
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    qLeafProfileKernelRemainderIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        XB (kCv, kCd)
      +
      qLeafProfileKernelRemainderIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        XB (kCv, 0)
      =
      qLeafProfileKernelRemainderCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd := by
  rw [qLeafProfileKernelRemainderIndexDiff_eq_cdPart_add_cvPart
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv kCd]
  rw [qLeafProfileKernelRemainderIndexDiff_cdZero_eq_cvPart
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv]
  abel_nf
  have htwo : (2 : F) = 0 := by decide
  simp [htwo]

noncomputable def leafCDiffEvalLinearMap
    {n a b : ℕ} [NeZero n]
    (y : YVec n b) (sz : I n) (p : PVec n a) (s : I n) :
    (YVec n b → I n → LeafDiffProfileCoord n a) →ₗ[F] F where
  toFun kCd := (kCd y sz p).1 s
  map_add' k₁ k₂ := by
    simp [Pi.add_apply]
  map_smul' r kCd := by
    simp [Pi.smul_apply]

noncomputable def leafCDiffCanonicalScalarLinearMap
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (ω : PassiveVisibleIndex n d hd) :
    (YVec n b → I n → LeafDiffProfileCoord n a) →ₗ[F]
      Core3loop.ScalarCCoef b n where
  toFun kCd :=
    leafCDiffCanonicalScalarIndexDiff
      (n := n) (a := a) (b := b) (d := d) hd kCd ω
  map_add' k₁ k₂ :=
    leafCDiffCanonicalScalarIndexDiff_add
      (n := n) (a := a) (b := b) (d := d) hd k₁ k₂ ω
  map_smul' r kCd :=
    leafCDiffCanonicalScalarIndexDiff_smul
      (n := n) (a := a) (b := b) (d := d) hd r kCd ω

noncomputable def qScalarRightLinearMap
    {b c n : ℕ} [NeZero n]
    (bcoef : Core3loop.ScalarBCoef c n) :
    Core3loop.ScalarCCoef b n →ₗ[F] F where
  toFun ccoef := Core3loop.qScalar (b := b) (c := c) (n := n) bcoef ccoef
  map_add' c₁ c₂ := by
    exact Core3loop.qScalar_add_right
      (b := b) (c := c) (n := n) bcoef c₁ c₂
  map_smul' r ccoef := by
    by_cases hr : r = 0
    · subst r
      simp [Core3loop.qScalar_zero_right]
    · have hr1 : r = 1 := F_ne_zero_eq_one r hr
      subst r
      simp

noncomputable def qLeafScalarCanonicalProfileBlockCdLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd) :
    (YVec n b → I n → LeafDiffProfileCoord n a) →ₗ[F] F :=
  (qScalarRightLinearMap
    (b := b) (c := c) (n := n)
    ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1).comp
    (leafCDiffCanonicalScalarLinearMap
      (n := n) (a := a) (b := b) (d := d) hd ω)

@[simp] theorem qLeafScalarCanonicalProfileBlockCdLinearMap_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a)
    (ω : PassiveVisibleIndex n d hd) :
    qLeafScalarCanonicalProfileBlockCdLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω kCd
      =
      qLeafScalarCanonicalProfileBlockCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H kCd ω := by
  rfl

noncomputable def qLeafProfileKernelRemainderCdLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    (YVec n b → I n → LeafDiffProfileCoord n a) →ₗ[F] F :=
  (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
    ((∑ ω : PassiveVisibleIndex n d hd,
      (XB.1 ω (vecSum y) z).1 p •
        leafCDiffEvalLinearMap (n := n) (a := a) (b := b)
          y (vecSum z) p (vecSum ω.1))
    +
    (Fintype.card (Vec n (d - 1)) : F) •
      ∑ s : I n,
        (XB.2 (vecSum y) z p).1 s •
          leafCDiffEvalLinearMap (n := n) (a := a) (b := b)
            y (vecSum z) p s))
  +
  (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
    ((∑ ω : PassiveVisibleIndex n d hd,
      (XB.1 ω (vecSum y + 1) z).1 p •
        leafCDiffEvalLinearMap (n := n) (a := a) (b := b)
          y (vecSum z + 1) p (vecSum ω.1))
    +
    (Fintype.card (Vec n (d - 1)) : F) •
      ∑ s : I n,
        (XB.2 (vecSum y + 1) z p).1 s •
          leafCDiffEvalLinearMap (n := n) (a := a) (b := b)
            y (vecSum z + 1) p s))

theorem qLeafProfileKernelRemainderCdLinearMap_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    qLeafProfileKernelRemainderCdLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd
      =
      qLeafProfileKernelRemainderCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd := by
  unfold qLeafProfileKernelRemainderCdLinearMap
    qLeafProfileKernelRemainderCdPart leafCDiffEvalLinearMap
  simp

def qLeafProfileKernelTotalCdExplicit
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) : F :=
  qLeafProfileKernelRemainderCdPart
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd
  +
  ∑ ω : PassiveVisibleIndex n d hd,
    qLeafScalarCanonicalProfileBlockCdPart
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H kCd ω

theorem qLeafProfileKernelTotalCdPart_eq_explicit
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    qLeafProfileKernelTotalCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H XB kCv kCd
      =
      qLeafProfileKernelTotalCdExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCd := by
  let rem₁ : F :=
    qLeafProfileKernelRemainderIndexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd
      XB (kCv, kCd)
  let rem₀ : F :=
    qLeafProfileKernelRemainderIndexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd
      XB (kCv, 0)
  let remCd : F :=
    qLeafProfileKernelRemainderCdPart
      (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd
  let block₁ : F :=
    ∑ ω : PassiveVisibleIndex n d hd,
      qLeafScalarCanonicalProfileBlock
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
        XB (kCv, kCd) ω
  let block₀ : F :=
    ∑ ω : PassiveVisibleIndex n d hd,
      qLeafScalarCanonicalProfileBlock
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
        XB (kCv, 0) ω
  let blockCd : F :=
    ∑ ω : PassiveVisibleIndex n d hd,
      qLeafScalarCanonicalProfileBlockCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H kCd ω
  have hRem : rem₁ + rem₀ = remCd := by
    dsimp [rem₁, rem₀, remCd]
    exact qLeafProfileKernelRemainderIndexDiff_add_cdZero_eq_cdPart
      (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv kCd
  have hBlock : block₁ + block₀ = blockCd := by
    dsimp [block₁, block₀, blockCd]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ω _
    exact qLeafScalarCanonicalProfileBlock_add_cdZero_eq_cdPart
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd ω
  unfold qLeafProfileKernelTotalCdPart qLeafProfileKernelTotalIndexDiff
    qLeafProfileKernelTotalCdExplicit
  change (rem₁ + block₁) + (rem₀ + block₀) = remCd + blockCd
  calc
    (rem₁ + block₁) + (rem₀ + block₀)
        = (rem₁ + rem₀) + (block₁ + block₀) := by
          abel
    _ = remCd + blockCd := by
      rw [hRem, hBlock]

noncomputable def qLeafProfileKernelTotalCdExplicitLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    (YVec n b → I n → LeafDiffProfileCoord n a) →ₗ[F] F :=
  qLeafProfileKernelRemainderCdLinearMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB
  +
  ∑ ω : PassiveVisibleIndex n d hd,
    qLeafScalarCanonicalProfileBlockCdLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω

theorem qLeafProfileKernelTotalCdExplicitLinearMap_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    qLeafProfileKernelTotalCdExplicitLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCd
      =
      qLeafProfileKernelTotalCdExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCd := by
  unfold qLeafProfileKernelTotalCdExplicitLinearMap
    qLeafProfileKernelTotalCdExplicit
  simp [qLeafProfileKernelRemainderCdLinearMap_apply]

theorem sum_kCd_bitSign_qLeafProfileKernelTotalCdExplicit_eq_if_linearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    (∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
      bitSign
        (qLeafProfileKernelTotalCdExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCd))
      =
      if qLeafProfileKernelTotalCdExplicitLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0 then
        (Fintype.card
          (YVec n b → I n → LeafDiffProfileCoord n a) : ℤ)
      else 0 := by
  simpa [qLeafProfileKernelTotalCdExplicitLinearMap_apply
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB] using
    sum_bitSign_linearMap
      (V := YVec n b → I n → LeafDiffProfileCoord n a)
      (qLeafProfileKernelTotalCdExplicitLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)

theorem sum_kCd_bitSign_qLeafProfileKernelTotalCdPart_eq_if_linearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a) :
    (∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
      bitSign
        (qLeafProfileKernelTotalCdPart
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd))
      =
      if qLeafProfileKernelTotalCdExplicitLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0 then
        (Fintype.card
          (YVec n b → I n → LeafDiffProfileCoord n a) : ℤ)
      else 0 := by
  calc
    (∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
      bitSign
        (qLeafProfileKernelTotalCdPart
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd))
        =
        ∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
          bitSign
            (qLeafProfileKernelTotalCdExplicit
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCd) := by
          refine Finset.sum_congr rfl ?_
          intro kCd _
          rw [qLeafProfileKernelTotalCdPart_eq_explicit
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd]
    _ =
      if qLeafProfileKernelTotalCdExplicitLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0 then
        (Fintype.card
          (YVec n b → I n → LeafDiffProfileCoord n a) : ℤ)
      else 0 := by
        exact sum_kCd_bitSign_qLeafProfileKernelTotalCdExplicit_eq_if_linearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB

theorem sum_kCd_bitSign_qLeafProfileKernelTotalIndexDiff_eq_if_linearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a) :
    (∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
      bitSign
        (qLeafProfileKernelTotalIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB (kCv, kCd)))
      =
      (if qLeafProfileKernelTotalCdExplicitLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0 then
        (Fintype.card
          (YVec n b → I n → LeafDiffProfileCoord n a) : ℤ) *
          bitSign
            (qLeafProfileKernelTotalIndexDiff
              (n := n) (a := a) (b := b) (c := c) (d := d) hd
              H XB (kCv, 0))
      else 0) := by
  rw [sum_kCd_bitSign_qLeafProfileKernelTotalIndexDiff_eq_cdPart_sum_mul_cdZero
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv]
  rw [sum_kCd_bitSign_qLeafProfileKernelTotalCdPart_eq_if_linearMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv]
  by_cases h :
      qLeafProfileKernelTotalCdExplicitLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0
  · simp [h]
  · simp [h]

theorem sum_kCd_bitSign_qLeafProfileKernelTotalCdExplicit_add_const
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (q : F) :
    (∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
      bitSign
        (qLeafProfileKernelTotalCdExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCd
          + q))
      =
      (if qLeafProfileKernelTotalCdExplicitLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0 then
        (Fintype.card
          (YVec n b → I n → LeafDiffProfileCoord n a) : ℤ) * bitSign q
      else 0) := by
  simpa [qLeafProfileKernelTotalCdExplicitLinearMap_apply
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB] using
    sum_bitSign_linearMap_add_const
      (V := YVec n b → I n → LeafDiffProfileCoord n a)
      (qLeafProfileKernelTotalCdExplicitLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
      q

end

end TriangleLeaf
end Core4loop
