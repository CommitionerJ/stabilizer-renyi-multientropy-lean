import Core4loop.TriangleLeaf.TotalQBReadLinear
import Core4loop.LinearSignSum

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

noncomputable local instance instFintypeBReadZeroHKernel
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype
      (LinearMap.ker
        (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd)) := by
  classical
  exact Fintype.ofFinite _

theorem leafBReadTarget_preimage_iff_exists_totalBCoeffCondition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (∃ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
      qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB
        =
        qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)
      ↔
    ∃ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
      TotalBCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB := by
  constructor
  · rintro ⟨XB, hXB⟩
    refine ⟨XB, ?_⟩
    rw [TotalBCoeffCondition_iff_zeroH_read_eq_const
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
    simpa [qLeafProfileKernelTotalBCoeffReadZeroHLinearMap] using hXB
  · rintro ⟨XB, hXB⟩
    refine ⟨XB, ?_⟩
    have hread :
        qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd
            (0 : LeafVisibleKernel n b c d) XB
          =
          qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 :=
      (TotalBCoeffCondition_iff_zeroH_read_eq_const
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB).1 hXB
    simpa [qLeafProfileKernelTotalBCoeffReadZeroHLinearMap] using hread

noncomputable def leafBReadFiberSignValue
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : ℤ := by
  classical
  exact
  linearMapFiberSignValue
    (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd)
    (qLeafProfileKernelTotalCvConstLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
    (qLeafProfileKernelTotalCvVisibleConst
      (n := n) (b := b) (c := c) (d := d) hd H)
    (qLeafProfileKernelTotalBCoeffRead
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)

set_option synthInstance.maxHeartbeats 200000 in
-- The B-read kernel is a product-of-function-space kernel, so instance search is deep here.
theorem leafBReadFiberSignValue_eq_of_preimage
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB0 : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (hXB0 :
      qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB0
        =
        qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0) :
    leafBReadFiberSignValue
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
      if (qLeafProfileKernelTotalCvConstLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H).comp
          (LinearMap.ker
            (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd)).subtype
          = 0 then
        (Fintype.card
          (LinearMap.ker
            (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd)) : ℤ)
          *
          bitSign
            (qLeafProfileKernelTotalCvConstLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0
              +
              qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H)
      else 0 := by
  classical
  unfold leafBReadFiberSignValue
  rw [linearMapFiberSignValue_eq_of_preimage
    (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd)
    (qLeafProfileKernelTotalCvConstLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
    (qLeafProfileKernelTotalCvVisibleConst
      (n := n) (b := b) (c := c) (d := d) hd H)
    (qLeafProfileKernelTotalBCoeffRead
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)
    XB0 hXB0]
  by_cases hM :
      (qLeafProfileKernelTotalCvConstLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H).comp
          (LinearMap.ker
            (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd)).subtype
          = 0
  · simp [hM]
  · simp [hM]

theorem leafBReadFiberSignValue_eq_of_totalBCoeffCondition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB0 : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (hXB0 :
      TotalBCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0) :
    leafBReadFiberSignValue
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
      if (qLeafProfileKernelTotalCvConstLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H).comp
          (LinearMap.ker
            (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd)).subtype
          = 0 then
        (Fintype.card
          (LinearMap.ker
            (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd)) : ℤ)
          *
          bitSign
            (qLeafProfileKernelTotalCvConstLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0
              +
              qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H)
      else 0 := by
  have hpre :
      qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB0
        =
        qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
    have hread :
        qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd
            (0 : LeafVisibleKernel n b c d) XB0
          =
          qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 :=
      (TotalBCoeffCondition_iff_zeroH_read_eq_const
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0).1 hXB0
    simpa [qLeafProfileKernelTotalBCoeffReadZeroHLinearMap] using hread
  exact
    leafBReadFiberSignValue_eq_of_preimage
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0 hpre

theorem leafBReadFiberSignValue_eq_zero_of_not_exists
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (htarget :
      ¬ ∃ XB0 : LeafBProfileKernelIndexDiffCoord n a c d hd,
        qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB0
          =
          qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0) :
    leafBReadFiberSignValue
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H = 0 := by
  classical
  unfold leafBReadFiberSignValue
  exact
    linearMapFiberSignValue_eq_zero_of_not_exists
      (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd)
      (qLeafProfileKernelTotalCvConstLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      (qLeafProfileKernelTotalCvVisibleConst
        (n := n) (b := b) (c := c) (d := d) hd H)
      (qLeafProfileKernelTotalBCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)
      htarget

theorem leafBReadFiberSignValue_eq_zero_of_no_totalBCoeffCondition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (hcondition :
      ¬ ∃ XB0 : LeafBProfileKernelIndexDiffCoord n a c d hd,
        TotalBCoeffCondition
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0) :
    leafBReadFiberSignValue
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H = 0 := by
  apply leafBReadFiberSignValue_eq_zero_of_not_exists
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H
  intro hpre
  exact hcondition
    ((leafBReadTarget_preimage_iff_exists_totalBCoeffCondition
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H).1 hpre)

theorem qLeafProfileKernelTotalCvConstLinearMap_zero_visible
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    qLeafProfileKernelTotalCvConstLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d)
      =
      0 := by
  classical
  apply LinearMap.ext
  intro XB
  unfold qLeafProfileKernelTotalCvConstLinearMap
    qScalarLeftLinearMap leafBKernelCanonicalScalarIndexDiffLinearMap
  have hzero :=
    leafVisibleKernelEquivCoord_zero
      (n := n) (b := b) (c := c) (d := d) hd
  simp [hzero, Core3loop.qScalar_zero_right]

theorem qLeafProfileKernelTotalCvVisibleConst_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    qLeafProfileKernelTotalCvVisibleConst
        (n := n) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d)
      =
      0 := by
  classical
  unfold qLeafProfileKernelTotalCvVisibleConst
  have hzero :=
    leafVisibleKernelEquivCoord_zero
      (n := n) (b := b) (c := c) (d := d) hd
  simp [hzero]

theorem leafVisibleCanonicalBaseSign_eq_bitSign_totalCvVisibleConst
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafVisibleCanonicalBaseSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
      bitSign
        (qLeafProfileKernelTotalCvVisibleConst
          (n := n) (b := b) (c := c) (d := d) hd H) := by
  unfold leafVisibleCanonicalBaseSign
    qLeafProfileKernelTotalCvVisibleConst
  rw [qLeafProfile_canonicalBase_eq_sum_qScalar
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]

theorem leafBReadFiberSignValue_eq_card_mul_visibleSign_of_exact_preimage
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB0 : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (hXB0 :
      TotalBCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0)
    (hker :
      (qLeafProfileKernelTotalCvConstLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H).comp
          (LinearMap.ker
            (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd)).subtype
          =
          0)
    (hphase :
      qLeafProfileKernelTotalCvConstLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0
        =
        0) :
    leafBReadFiberSignValue
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
      (Fintype.card
        (LinearMap.ker
          (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd)) : ℤ)
        *
      leafVisibleCanonicalBaseSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  rw [leafBReadFiberSignValue_eq_of_totalBCoeffCondition
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0 hXB0]
  rw [if_pos hker]
  rw [hphase]
  rw [zero_add]
  rw [← leafVisibleCanonicalBaseSign_eq_bitSign_totalCvVisibleConst
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]

theorem leafBReadFiberSignValue_zero_visible
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafBReadFiberSignValue
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d)
      =
      (Fintype.card
        (LinearMap.ker
          (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd)) : ℤ) := by
  classical
  have hpre :
      qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafBProfileKernelIndexDiffCoord n a c d hd)
        =
        qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) 0 := by
    simp [qLeafProfileKernelTotalBCoeffReadZeroHLinearMap]
  rw [leafBReadFiberSignValue_eq_of_preimage
    (n := n) (a := a) (b := b) (c := c) (d := d) hd
    (0 : LeafVisibleKernel n b c d)
    (0 : LeafBProfileKernelIndexDiffCoord n a c d hd)
    hpre]
  have hM :
      (qLeafProfileKernelTotalCvConstLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd
            (0 : LeafVisibleKernel n b c d)).comp
          (LinearMap.ker
            (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd)).subtype
        =
        0 := by
    rw [qLeafProfileKernelTotalCvConstLinearMap_zero_visible
      (n := n) (a := a) (b := b) (c := c) (d := d) hd]
    rfl
  have hq :
      qLeafProfileKernelTotalCvVisibleConst
          (n := n) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d)
        =
        0 :=
    qLeafProfileKernelTotalCvVisibleConst_zero
      (n := n) (b := b) (c := c) (d := d) hd
  rw [if_pos hM]
  rw [qLeafProfileKernelTotalCvConstLinearMap_zero_visible
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  rw [hq]
  change
    (Fintype.card
      (LinearMap.ker
        (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd)) : ℤ)
      *
      bitSign
        (((0 : LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F] F)
            (0 : LeafBProfileKernelIndexDiffCoord n a c d hd))
          + 0)
      =
      (Fintype.card
        (LinearMap.ker
          (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd)) : ℤ)
  rw [show
      ((0 : LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F] F)
          (0 : LeafBProfileKernelIndexDiffCoord n a c d hd))
        + 0 = 0 by rfl]
  rw [bitSign_zero]
  ring

private noncomputable def leafBReadFiberClassicalSummand
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) : ℤ := by
  classical
  exact
    if qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB
        =
        qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 then
      bitSign
        (qLeafProfileKernelTotalCvConstLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
          +
          qLeafProfileKernelTotalCvVisibleConst
            (n := n) (b := b) (c := c) (d := d) hd H)
    else 0

set_option synthInstance.maxHeartbeats 200000 in
-- The coefficient target is a product of finite function spaces, so instance search is deep here.
theorem leafCompatibleResidualXBInnerSum_eq_fiberSignValue
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
      if qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd
            (0 : LeafVisibleKernel n b c d) XB
          =
          qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 then
        bitSign
          (qLeafProfileKernelTotalCvConstLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
            +
            qLeafProfileKernelTotalCvVisibleConst
              (n := n) (b := b) (c := c) (d := d) hd H)
      else 0)
      =
    leafBReadFiberSignValue
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  classical
  calc
    (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
      if qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd
            (0 : LeafVisibleKernel n b c d) XB
          =
          qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 then
        bitSign
          (qLeafProfileKernelTotalCvConstLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
            +
            qLeafProfileKernelTotalCvVisibleConst
              (n := n) (b := b) (c := c) (d := d) hd H)
      else 0)
        =
      (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        leafBReadFiberClassicalSummand
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB) := by
          refine Finset.sum_congr rfl ?_
          intro XB _
          unfold leafBReadFiberClassicalSummand
          by_cases h :
              qLeafProfileKernelTotalBCoeffRead
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd
                  (0 : LeafVisibleKernel n b c d) XB
                =
                qLeafProfileKernelTotalBCoeffRead
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0
          · have hL :
                qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB
                  =
                  qLeafProfileKernelTotalBCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
              simpa [qLeafProfileKernelTotalBCoeffReadZeroHLinearMap] using h
            simp [h, hL]
          · have hL :
                qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB
                  ≠
                  qLeafProfileKernelTotalBCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
              intro hL
              apply h
              simpa [qLeafProfileKernelTotalBCoeffReadZeroHLinearMap] using hL
            simp [h, hL]
    _ =
      leafBReadFiberSignValue
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
        change
          (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
            leafBReadFiberClassicalSummand
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
            =
          linearMapFiberSignValue
            (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd)
            (qLeafProfileKernelTotalCvConstLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
            (qLeafProfileKernelTotalCvVisibleConst
              (n := n) (b := b) (c := c) (d := d) hd H)
            (qLeafProfileKernelTotalBCoeffRead
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)
        calc
          (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
            leafBReadFiberClassicalSummand
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
              =
            (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
              @ite ℤ
                (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd XB
                    =
                    qLeafProfileKernelTotalBCoeffRead
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)
                (Classical.propDecidable
                  (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB
                      =
                      qLeafProfileKernelTotalBCoeffRead
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0))
                (bitSign
                  (qLeafProfileKernelTotalCvConstLinearMap
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
                    +
                    qLeafProfileKernelTotalCvVisibleConst
                      (n := n) (b := b) (c := c) (d := d) hd H))
                0) := by
                unfold leafBReadFiberClassicalSummand
                refine Finset.sum_congr rfl ?_
                intro XB _
                by_cases h :
                    qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB
                      =
                      qLeafProfileKernelTotalBCoeffRead
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0
                · simp [h]
                · simp [h]
          _ =
            linearMapFiberSignValue
              (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd)
              (qLeafProfileKernelTotalCvConstLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
              (qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H)
              (qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0) := by
                exact
                  (sum_if_linearMap_eq_const_bitSign_linearMap_add_const_eq_fiberSignValue
                    (L :=
                      qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd)
                    (M :=
                      qLeafProfileKernelTotalCvConstLinearMap
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
                    (q :=
                      qLeafProfileKernelTotalCvVisibleConst
                        (n := n) (b := b) (c := c) (d := d) hd H)
                    (target :=
                      qLeafProfileKernelTotalBCoeffRead
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0))

theorem leafCompatibleResidualSum_eq_after_XB_BCoeffRead_fiberSignValue
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        (2 : ℤ) ^ kCdCvElimExpNat n a b d *
          leafBReadFiberSignValue
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  classical
  rw [leafCompatibleResidualSum_eq_after_XB_BCoeffRead_eq_const_affineCv
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  calc
    (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
      if qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd
            (0 : LeafVisibleKernel n b c d) XB
          =
          qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 then
        (2 : ℤ) ^ kCdCvElimExpNat n a b d *
          bitSign
            (qLeafProfileKernelTotalCvConstLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
              +
              qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H)
      else 0)
        =
      (2 : ℤ) ^ kCdCvElimExpNat n a b d *
        (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          if qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                (0 : LeafVisibleKernel n b c d) XB
              =
              qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 then
            bitSign
              (qLeafProfileKernelTotalCvConstLinearMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
                +
                qLeafProfileKernelTotalCvVisibleConst
                  (n := n) (b := b) (c := c) (d := d) hd H)
          else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro XB _
          by_cases h :
              qLeafProfileKernelTotalBCoeffRead
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd
                  (0 : LeafVisibleKernel n b c d) XB
                =
                qLeafProfileKernelTotalBCoeffRead
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0
          · simp [h]
          · simp [h]
    _ =
      (2 : ℤ) ^ kCdCvElimExpNat n a b d *
        leafBReadFiberSignValue
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
          rw [leafCompatibleResidualXBInnerSum_eq_fiberSignValue
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H]

end

end TriangleLeaf
end Core4loop
