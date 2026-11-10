import Core4loop.TriangleLeaf.ProfileKernelIndexDiffQ
import Core4loop.TriangleLeaf.ProfileKernelIndexDiffSum

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem leafDotProfile_kernel_indexDiff_symm_canonicalC_eq
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (X :
      (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
        × LeafDiffProfileCoord n a)
    (VC : LeafCVisible n b d) (y : YVec n b) (sz : I n) :
    leafDotProfile
        (((leafProfileKernelEquivIndexDiff
          (n := n) (a := a) (d := d) hd).symm X).1)
        (leafCProfile
          (leafCVisCanonicalBase
            (n := n) (a := a) (b := b) (d := d) hd VC) y sz)
      =
      (∑ ω : PassiveVisibleIndex n d hd,
        (X.1 ω).1 (zeroVec : PVec n a) *
          passiveQuotEquivVisibleIndex (n := n) (d := d) hd (VC y sz) ω)
        +
      (∑ ω : PassiveVisibleIndex n d hd,
        (X.2 (zeroVec : PVec n a)).1 (vecSum ω.1) *
          passiveQuotEquivVisibleIndex (n := n) (d := d) hd (VC y sz) ω) := by
  rw [leafDotProfile_eq_sum_passiveDot]
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · rw [leafCProfile_leafCVisCanonicalBase_zero
      (n := n) (a := a) (b := b) (d := d) hd VC y sz]
    change
      passiveDot (n := n) (d := d)
          ((passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm
            ((((leafVisibleProfileKernelEquivIndex
              (n := n) (a := a) (d := d) hd).symm X.1).1
                (zeroVec : PVec n a)), X.2 (zeroVec : PVec n a)))
          (passiveQuotEquivVisibleSpace (n := n) (d := d) hd (VC y sz)).1
        =
        (∑ ω : PassiveVisibleIndex n d hd,
          (X.1 ω).1 (zeroVec : PVec n a) *
            passiveQuotEquivVisibleIndex (n := n) (d := d) hd (VC y sz) ω)
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          (X.2 (zeroVec : PVec n a)).1 (vecSum ω.1) *
            passiveQuotEquivVisibleIndex (n := n) (d := d) hd (VC y sz) ω)
    rw [passiveDot_visibleDiff_symm_visibleSpace_eq_index_sum
      (n := n) (d := d) hd]
    simp_rw [passiveVisible_index_leafVisibleProfileKernelEquivIndex_symm
      (n := n) (a := a) (d := d) hd]
    rfl
  · intro p _ hp
    rw [leafCProfile_leafCVisCanonicalBase_ne_zero
      (n := n) (a := a) (b := b) (d := d) hd VC y sz p hp]
    simp [passiveDot]
  · simp

theorem leafDotProfile_canonicalB_kernel_indexDiff_symm_eq
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (VB : LeafBVisible n c d) (sy : I n) (z : ZVec n c)
    (X :
      (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
        × LeafDiffProfileCoord n a) :
    leafDotProfile
        (leafBProfile
          (leafBVisCanonicalBase
            (n := n) (a := a) (c := c) (d := d) hd VB) sy z)
        (((leafProfileKernelEquivIndexDiff
          (n := n) (a := a) (d := d) hd).symm X).1)
      =
      (∑ ω : PassiveVisibleIndex n d hd,
        passiveQuotEquivVisibleIndex (n := n) (d := d) hd (VB sy z) ω *
          (X.1 ω).1 (zeroVec : PVec n a))
        +
      (∑ ω : PassiveVisibleIndex n d hd,
        passiveQuotEquivVisibleIndex (n := n) (d := d) hd (VB sy z) ω *
          (X.2 (zeroVec : PVec n a)).1 (vecSum ω.1)) := by
  rw [leafDotProfile_eq_sum_passiveDot]
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · rw [leafBProfile_leafBVisCanonicalBase_zero
      (n := n) (a := a) (c := c) (d := d) hd VB sy z]
    change
      passiveDot (n := n) (d := d)
          (passiveQuotEquivVisibleSpace (n := n) (d := d) hd (VB sy z)).1
          ((passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm
            ((((leafVisibleProfileKernelEquivIndex
              (n := n) (a := a) (d := d) hd).symm X.1).1
                (zeroVec : PVec n a)), X.2 (zeroVec : PVec n a)))
        =
        (∑ ω : PassiveVisibleIndex n d hd,
          passiveQuotEquivVisibleIndex (n := n) (d := d) hd (VB sy z) ω *
            (X.1 ω).1 (zeroVec : PVec n a))
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          passiveQuotEquivVisibleIndex (n := n) (d := d) hd (VB sy z) ω *
            (X.2 (zeroVec : PVec n a)).1 (vecSum ω.1))
    rw [passiveDot_visibleSpace_visibleDiff_symm_eq_index_sum
      (n := n) (d := d) hd]
    simp_rw [passiveVisible_index_leafVisibleProfileKernelEquivIndex_symm
      (n := n) (a := a) (d := d) hd]
    rfl
  · intro p _ hp
    rw [leafBProfile_leafBVisCanonicalBase_ne_zero
      (n := n) (a := a) (c := c) (d := d) hd VB sy z p hp]
    simp [passiveDot]
  · simp

def qLeafLeftKernelCanonicalIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) : F :=
  ∑ y : YVec n b, ∑ z : ZVec n c,
    ((∑ ω : PassiveVisibleIndex n d hd,
      (XB.1 ω (vecSum y) z).1 (zeroVec : PVec n a) *
        passiveQuotEquivVisibleIndex
          (n := n) (d := d) hd (H.1.2 y (vecSum z)) ω)
      +
    (∑ ω : PassiveVisibleIndex n d hd,
      (XB.2 (vecSum y) z (zeroVec : PVec n a)).1 (vecSum ω.1) *
        passiveQuotEquivVisibleIndex
          (n := n) (d := d) hd (H.1.2 y (vecSum z)) ω))

def qLeafRightKernelCanonicalIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) : F :=
  ∑ y : YVec n b, ∑ z : ZVec n c,
    ((∑ ω : PassiveVisibleIndex n d hd,
      (XB.1 ω (vecSum y + 1) z).1 (zeroVec : PVec n a) *
        passiveQuotEquivVisibleIndex
          (n := n) (d := d) hd (H.1.2 y (vecSum z + 1)) ω)
      +
    (∑ ω : PassiveVisibleIndex n d hd,
      (XB.2 (vecSum y + 1) z (zeroVec : PVec n a)).1 (vecSum ω.1) *
        passiveQuotEquivVisibleIndex
          (n := n) (d := d) hd (H.1.2 y (vecSum z + 1)) ω))

def qLeafProfileKernelCanonicalIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) : F :=
  qLeafLeftKernelCanonicalIndexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
    +
  qLeafRightKernelCanonicalIndexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB

def qLeafLeftCanonicalKernelIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) : F :=
  ∑ y : YVec n b, ∑ z : ZVec n c,
    ((∑ ω : PassiveVisibleIndex n d hd,
      passiveQuotEquivVisibleIndex
          (n := n) (d := d) hd (H.1.1 (vecSum y) z) ω *
        (XC.1 ω y (vecSum z)).1 (zeroVec : PVec n a))
      +
    (∑ ω : PassiveVisibleIndex n d hd,
      passiveQuotEquivVisibleIndex
          (n := n) (d := d) hd (H.1.1 (vecSum y) z) ω *
        (XC.2 y (vecSum z) (zeroVec : PVec n a)).1 (vecSum ω.1)))

def qLeafRightCanonicalKernelIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) : F :=
  ∑ y : YVec n b, ∑ z : ZVec n c,
    ((∑ ω : PassiveVisibleIndex n d hd,
      passiveQuotEquivVisibleIndex
          (n := n) (d := d) hd (H.1.1 (vecSum y + 1) z) ω *
        (XC.1 ω y (vecSum z + 1)).1 (zeroVec : PVec n a))
      +
    (∑ ω : PassiveVisibleIndex n d hd,
      passiveQuotEquivVisibleIndex
          (n := n) (d := d) hd (H.1.1 (vecSum y + 1) z) ω *
        (XC.2 y (vecSum z + 1) (zeroVec : PVec n a)).1 (vecSum ω.1)))

def qLeafProfileCanonicalKernelIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) : F :=
  qLeafLeftCanonicalKernelIndexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XC
    +
  qLeafRightCanonicalKernelIndexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XC

theorem qLeafProfile_kernel_canonical_indexDiff_eq
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfile
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleBKernelPart
          (n := n) (a := a) (c := c) (d := d)
          ((leafBProfileKernelCoordEquivIndexDiff
            (n := n) (a := a) (c := c) (d := d) hd).symm XB))
        (leafVisibleCCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      =
      qLeafProfileKernelCanonicalIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB := by
  unfold qLeafProfile qLeafLeft qLeafRight
    qLeafProfileKernelCanonicalIndexDiff
    qLeafLeftKernelCanonicalIndexDiff qLeafRightKernelCanonicalIndexDiff
  simp_rw [leafBProfile_leafBVisKernelOfCoord]
  simp_rw [leafBProfileKernelCoordEquivIndexDiff_symm_apply
    (n := n) (a := a) (c := c) (d := d) hd XB]
  simp_rw [leafDotProfile_kernel_indexDiff_symm_canonicalC_eq
    (n := n) (a := a) (b := b) (d := d) hd]

theorem qLeafProfile_canonical_kernel_indexDiff_eq
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    qLeafProfile
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleBCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        (leafVisibleCKernelPart
          (n := n) (a := a) (b := b) (d := d)
          ((leafCProfileKernelCoordEquivIndexDiff
            (n := n) (a := a) (b := b) (d := d) hd).symm XC))
      =
      qLeafProfileCanonicalKernelIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XC := by
  unfold qLeafProfile qLeafLeft qLeafRight
    qLeafProfileCanonicalKernelIndexDiff
    qLeafLeftCanonicalKernelIndexDiff qLeafRightCanonicalKernelIndexDiff
  simp_rw [leafCProfile_leafCVisKernelOfCoord]
  simp_rw [leafCProfileKernelCoordEquivIndexDiff_symm_apply
    (n := n) (a := a) (b := b) (d := d) hd XC]
  simp_rw [leafDotProfile_canonicalB_kernel_indexDiff_symm_eq
    (n := n) (a := a) (c := c) (d := d) hd]

theorem leafVisibleCanonicalProfileKernelIndexDiffInteractionSign_eq
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
      * bitSign
        (qLeafProfileKernelCanonicalIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
      * bitSign
        (qLeafProfileCanonicalKernelIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XC) := by
  unfold leafVisibleCanonicalProfileKernelIndexDiffInteractionSign
  unfold leafVisibleCanonicalProfileKernelInteractionSign
  rw [qLeafProfile_kernel_indexDiff_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC]
  rw [qLeafProfile_kernel_canonical_indexDiff_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
  rw [qLeafProfile_canonical_kernel_indexDiff_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XC]

theorem leafVisibleCanonicalProfileKernelInteractionSum_eq_indexDiffSplitComponentSum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafVisibleCanonicalProfileKernelInteractionSum n a b c d hd H =
      ∑ kBv : PassiveVisibleIndex n d hd →
          I n → ZVec n c → LeafScalarProfileKernel n a,
        ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
          ∑ kCv : PassiveVisibleIndex n d hd →
              YVec n b → I n → LeafScalarProfileKernel n a,
            ∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
              bitSign
                (qLeafProfileKernelIndexDiff
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd
                  (kBv, kBd) (kCv, kCd))
              * bitSign
                (qLeafProfileKernelCanonicalIndexDiff
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H
                  (kBv, kBd))
              * bitSign
                (qLeafProfileCanonicalKernelIndexDiff
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H
                  (kCv, kCd)) := by
  rw [leafVisibleCanonicalProfileKernelInteractionSum_eq_indexDiffComponentSum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  refine Finset.sum_congr rfl ?_
  intro kCv _
  refine Finset.sum_congr rfl ?_
  intro kCd _
  rw [leafVisibleCanonicalProfileKernelIndexDiffInteractionSign_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H
    (kBv, kBd) (kCv, kCd)]

end

end TriangleLeaf
end Core4loop
