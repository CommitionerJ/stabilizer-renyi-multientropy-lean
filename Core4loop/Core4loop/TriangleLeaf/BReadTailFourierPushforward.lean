import Core4loop.TriangleLeaf.BReadTailMaps

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

local instance instFintypeLeafRawCTraceSpacePushforward
    {n b d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype (LeafRawCTraceSpace n b d hd) := by
  classical
  exact Fintype.ofFinite _

local instance instFintypeLeafRawBTraceSpacePushforward
    {n c d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype (LeafRawBTraceSpace n c d hd) := by
  classical
  exact Fintype.ofFinite _

noncomputable local instance instFintypeLeafBReadTailReadMapKernelPushforward
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype
      (LinearMap.ker
        (leafBReadTailReadMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd)) := by
  classical
  exact Fintype.ofFinite _

def leafBReadActualTailFourierCoeff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : ℤ :=
  ∑ U : LeafBReadTarget n a b c d hd,
    ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
      bitSign
        (leafBReadFourierTailPhase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB
        + leafRawCTraceVisibleBPair
          (n := n) (b := b) (c := c) (d := d) hd
          ((leafBReadCTraceMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd) U) H
        + leafRawBTraceVisibleCPair
          (n := n) (b := b) (c := c) (d := d) hd
          ((leafBReadBTraceMap
            (n := n) (a := a) (c := c) (d := d) hd) XB) H)

def leafBReadRawFourierCoeff
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : ℤ :=
  ∑ C₂ : LeafRawCTraceSpace n b d hd,
    ∑ B₂ : LeafRawBTraceSpace n c d hd,
      bitSign
        (leafRawCTraceVisibleBPair
          (n := n) (b := b) (c := c) (d := d) hd C₂ H
        + leafRawBTraceVisibleCPair
          (n := n) (b := b) (c := c) (d := d) hd B₂ H)

abbrev leafBReadBTraceVisibleCLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F] F :=
  qLeafProfileKernelTotalCvConstLinearMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H

theorem leafBReadBTraceVisibleCLinearMap_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    leafBReadBTraceVisibleCLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      =
    leafRawBTraceVisibleCPair
      (n := n) (b := b) (c := c) (d := d) hd
      ((leafBReadBTraceMap
        (n := n) (a := a) (c := c) (d := d) hd) XB) H := by
  simpa [leafBReadBTraceVisibleCLinearMap, leafRawBTraceVisibleCPair,
    leafBReadBTraceMap] using
    qLeafProfileKernelTotalCvConstLinearMap_eq_scalarBTrace_visibleC
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB

def leafBReadAffineFiberTailSum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : ℤ :=
  ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
    if ((leafBReadTailReadMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
        =
        leafBReadVisibleBAdjoint
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H) then
      bitSign
        (leafRawBTraceVisibleCPair
          (n := n) (b := b) (c := c) (d := d) hd
          ((leafBReadBTraceMap
            (n := n) (a := a) (c := c) (d := d) hd) XB) H)
    else 0

theorem leafBReadAffineFiberTailSum_eq_linearMapFiberSignValue
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafBReadAffineFiberTailSum
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
    linearMapFiberSignValue
      (leafBReadTailReadMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd)
      (leafBReadBTraceVisibleCLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      0
      (leafBReadVisibleBAdjoint
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H) := by
  classical
  unfold leafBReadAffineFiberTailSum
  calc
    (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
      if ((leafBReadTailReadMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
          =
          leafBReadVisibleBAdjoint
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H) then
        bitSign
          (leafRawBTraceVisibleCPair
            (n := n) (b := b) (c := c) (d := d) hd
            ((leafBReadBTraceMap
              (n := n) (a := a) (c := c) (d := d) hd) XB) H)
      else 0)
        =
      ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        if ((leafBReadTailReadMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
            =
            leafBReadVisibleBAdjoint
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H) then
          bitSign
            (leafBReadBTraceVisibleCLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
              + 0)
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro XB _
          by_cases h :
              ((leafBReadTailReadMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
                =
                leafBReadVisibleBAdjoint
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
          · simp only [h, ↓reduceIte, add_zero]
            rw [leafBReadBTraceVisibleCLinearMap_apply
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
          · simp [h]
    _ =
      linearMapFiberSignValue
        (leafBReadTailReadMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd)
        (leafBReadBTraceVisibleCLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        0
        (leafBReadVisibleBAdjoint
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H) := by
          exact
            sum_if_linearMap_eq_const_bitSign_linearMap_add_const_eq_fiberSignValue
              (L :=
                leafBReadTailReadMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd)
              (M :=
                leafBReadBTraceVisibleCLinearMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
              (q := 0)
              (target :=
                leafBReadVisibleBAdjoint
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H)

theorem leafRawVisibleBasePhase_eq_totalCvVisibleConst
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafRawVisibleBasePhase
        (n := n) (b := b) (c := c) (d := d) hd H
      =
    qLeafProfileKernelTotalCvVisibleConst
      (n := n) (b := b) (c := c) (d := d) hd H := by
  rfl

private theorem bitSign_mul_self (q : F) :
    bitSign q * bitSign q = 1 := by
  fin_cases q <;> decide

theorem leafBReadAffineFiberTailSum_eq_visibleSign_mul_fiberSignValue
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafBReadAffineFiberTailSum
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
    bitSign
      (leafRawVisibleBasePhase
        (n := n) (b := b) (c := c) (d := d) hd H)
      *
    leafBReadFiberSignValue
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  classical
  rw [← leafCompatibleResidualXBInnerSum_eq_fiberSignValue
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  rw [Finset.mul_sum]
  unfold leafBReadAffineFiberTailSum
  refine Finset.sum_congr rfl ?_
  intro XB _
  by_cases h :
      ((leafBReadTailReadMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
        =
        leafBReadVisibleBAdjoint
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
  · have hOld :
        qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd
            (0 : LeafVisibleKernel n b c d) XB
          =
        qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
      simpa [leafBReadTailReadMap, leafBReadVisibleBAdjoint,
        qLeafProfileKernelTotalBCoeffReadZeroHLinearMap] using h
    simp only [h, hOld, ↓reduceIte]
    rw [leafRawVisibleBasePhase_eq_totalCvVisibleConst
      (n := n) (b := b) (c := c) (d := d) hd H]
    rw [qLeafProfileKernelTotalCvConstLinearMap_eq_scalarBTrace_visibleC
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
    rw [bitSign_add]
    unfold leafRawBTraceVisibleCPair leafBReadBTraceMap
    have hsq :
        bitSign
            (qLeafProfileKernelTotalCvVisibleConst
              (n := n) (b := b) (c := c) (d := d) hd H)
          ^ 2
          =
          1 :=
      by
        calc
          bitSign
              (qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H)
            ^ 2
              =
            bitSign
                (qLeafProfileKernelTotalCvVisibleConst
                  (n := n) (b := b) (c := c) (d := d) hd H)
              *
            bitSign
                (qLeafProfileKernelTotalCvVisibleConst
                  (n := n) (b := b) (c := c) (d := d) hd H) := by
                ring
          _ = 1 :=
            bitSign_mul_self
              (qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H)
    ring_nf
    rw [hsq]
    simp only [one_mul, LinearMap.coe_mk, AddHom.coe_mk]
  · have hOld :
        qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd
            (0 : LeafVisibleKernel n b c d) XB
          ≠
        qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
      intro hOld
      apply h
      simpa [leafBReadTailReadMap, leafBReadVisibleBAdjoint,
        qLeafProfileKernelTotalBCoeffReadZeroHLinearMap] using hOld
    simp [h, hOld]

private theorem sum_leafBReadTarget_bitSign_phase_add_dot_eq_card_if_eq
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (q : F) (X Y : LeafBReadTarget n a b c d hd) :
    (∑ U : LeafBReadTarget n a b c d hd,
        bitSign (q + leafBReadTargetDot hd U (X + Y))) =
      (if X = Y then (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) else 0)
        * bitSign q := by
  classical
  calc
    (∑ U : LeafBReadTarget n a b c d hd,
        bitSign (q + leafBReadTargetDot hd U (X + Y)))
        =
      ∑ U : LeafBReadTarget n a b c d hd,
        bitSign q * bitSign (leafBReadTargetDot hd U (X + Y)) := by
          refine Finset.sum_congr rfl ?_
          intro U _
          rw [bitSign_add]
    _ =
      bitSign q *
        (∑ U : LeafBReadTarget n a b c d hd,
          bitSign (leafBReadTargetDot hd U (X + Y))) := by
          rw [Finset.mul_sum]
    _ =
      bitSign q *
        (if X = Y then
          (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
        else 0) := by
          rw [sum_leafBReadTargetDot_eq_card_if_eq hd X Y]
    _ =
      (if X = Y then
          (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
        else 0) * bitSign q := by
          ring

private theorem leafBReadActualTailFourierCoeff_U_inner_sum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    (∑ U : LeafBReadTarget n a b c d hd,
      bitSign
        (leafBReadFourierTailPhase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB
        + leafRawCTraceVisibleBPair
          (n := n) (b := b) (c := c) (d := d) hd
          ((leafBReadCTraceMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd) U) H
        + leafRawBTraceVisibleCPair
          (n := n) (b := b) (c := c) (d := d) hd
          ((leafBReadBTraceMap
            (n := n) (a := a) (c := c) (d := d) hd) XB) H))
      =
    (if ((leafBReadTailReadMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
        =
        leafBReadVisibleBAdjoint
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H) then
      (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
    else 0)
      *
    bitSign
      (leafRawBTraceVisibleCPair
        (n := n) (b := b) (c := c) (d := d) hd
        ((leafBReadBTraceMap
          (n := n) (a := a) (c := c) (d := d) hd) XB) H) := by
  classical
  let q : F :=
    leafRawBTraceVisibleCPair
      (n := n) (b := b) (c := c) (d := d) hd
      ((leafBReadBTraceMap
        (n := n) (a := a) (c := c) (d := d) hd) XB) H
  let X : LeafBReadTarget n a b c d hd :=
    ((leafBReadTailReadMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB)
  let Y : LeafBReadTarget n a b c d hd :=
    leafBReadVisibleBAdjoint
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H
  calc
    (∑ U : LeafBReadTarget n a b c d hd,
      bitSign
        (leafBReadFourierTailPhase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB
        + leafRawCTraceVisibleBPair
          (n := n) (b := b) (c := c) (d := d) hd
          ((leafBReadCTraceMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd) U) H
        + leafRawBTraceVisibleCPair
          (n := n) (b := b) (c := c) (d := d) hd
          ((leafBReadBTraceMap
            (n := n) (a := a) (c := c) (d := d) hd) XB) H))
        =
      ∑ U : LeafBReadTarget n a b c d hd,
        bitSign (q + leafBReadTargetDot hd U (X + Y)) := by
          refine Finset.sum_congr rfl ?_
          intro U _
          rw [leafBReadFourierTailPhase_eq_dot_tailRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB]
          rw [← leafBReadVisibleBAdjoint_spec
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U H]
          rw [← leafBReadTargetDot_add_right
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U X Y]
          congr 1
          dsimp [q, X, Y]
          ac_rfl
    _ =
      (if X = Y then
          (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
        else 0) * bitSign q := by
        exact
          sum_leafBReadTarget_bitSign_phase_add_dot_eq_card_if_eq
            (n := n) (a := a) (b := b) (c := c) (d := d) hd q X Y
    _ =
      (if ((leafBReadTailReadMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
          =
          leafBReadVisibleBAdjoint
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H) then
        (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
      else 0)
        *
      bitSign
        (leafRawBTraceVisibleCPair
          (n := n) (b := b) (c := c) (d := d) hd
          ((leafBReadBTraceMap
            (n := n) (a := a) (c := c) (d := d) hd) XB) H) := by
        rfl

theorem leafBReadActualTailFourierCoeff_eq_card_mul_affine_fiber_sum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafBReadActualTailFourierCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
    (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) *
      leafBReadAffineFiberTailSum
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  classical
  let C : ℤ := (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
  unfold leafBReadActualTailFourierCoeff leafBReadAffineFiberTailSum
  rw [Finset.sum_comm]
  calc
    (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
      ∑ U : LeafBReadTarget n a b c d hd,
        bitSign
          (leafBReadFourierTailPhase
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB
          + leafRawCTraceVisibleBPair
            (n := n) (b := b) (c := c) (d := d) hd
            ((leafBReadCTraceMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd) U) H
          + leafRawBTraceVisibleCPair
            (n := n) (b := b) (c := c) (d := d) hd
            ((leafBReadBTraceMap
              (n := n) (a := a) (c := c) (d := d) hd) XB) H))
        =
      ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        (if ((leafBReadTailReadMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
            =
            leafBReadVisibleBAdjoint
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H) then
          C
        else 0)
          *
        bitSign
          (leafRawBTraceVisibleCPair
            (n := n) (b := b) (c := c) (d := d) hd
            ((leafBReadBTraceMap
              (n := n) (a := a) (c := c) (d := d) hd) XB) H) := by
          refine Finset.sum_congr rfl ?_
          intro XB _
          simpa [C] using
            leafBReadActualTailFourierCoeff_U_inner_sum
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
    _ =
      ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        C *
          (if ((leafBReadTailReadMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
              =
              leafBReadVisibleBAdjoint
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H) then
            bitSign
              (leafRawBTraceVisibleCPair
                (n := n) (b := b) (c := c) (d := d) hd
                ((leafBReadBTraceMap
                  (n := n) (a := a) (c := c) (d := d) hd) XB) H)
          else 0) := by
          refine Finset.sum_congr rfl ?_
          intro XB _
          by_cases h :
              ((leafBReadTailReadMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
                =
                leafBReadVisibleBAdjoint
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
          · simp [h]
          · simp [h]
    _ =
      C *
        (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          if ((leafBReadTailReadMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
              =
              leafBReadVisibleBAdjoint
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H) then
            bitSign
              (leafRawBTraceVisibleCPair
                (n := n) (b := b) (c := c) (d := d) hd
                ((leafBReadBTraceMap
                  (n := n) (a := a) (c := c) (d := d) hd) XB) H)
          else 0) := by
          rw [Finset.mul_sum]
    _ =
      (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) *
        (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          if ((leafBReadTailReadMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB
              =
              leafBReadVisibleBAdjoint
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H) then
            bitSign
              (leafRawBTraceVisibleCPair
                (n := n) (b := b) (c := c) (d := d) hd
                ((leafBReadBTraceMap
                  (n := n) (a := a) (c := c) (d := d) hd) XB) H)
          else 0) := by
          rfl

end

end TriangleLeaf
end Core4loop
