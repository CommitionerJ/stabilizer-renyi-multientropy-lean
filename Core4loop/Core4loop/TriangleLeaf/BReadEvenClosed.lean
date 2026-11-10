import Core4loop.TriangleLeaf.BReadTailFourierPushforward

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

local instance instFintypeLeafScalarEvenBlockDataEvenClosed
    {n b c : ℕ} [NeZero n] :
    Fintype (LeafScalarEvenBlockData n b c) := by
  classical
  exact Fintype.ofFinite _

local instance instFintypeLeafRawCTraceSpaceEvenClosed
    {n b d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype (LeafRawCTraceSpace n b d hd) := by
  classical
  exact Fintype.ofFinite _

local instance instFintypeLeafRawBTraceSpaceEvenClosed
    {n c d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype (LeafRawBTraceSpace n c d hd) := by
  classical
  exact Fintype.ofFinite _

private theorem sum_leafEvenRawBlockProductSign_eq_sum_raw_traces_evenClosed
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign
        (n := n) (b := b) (c := c) (d := d) hd X)
      =
    ∑ H : LeafVisibleKernel n b c d,
      ∑ C₂ : LeafRawCTraceSpace n b d hd,
        ∑ B₂ : LeafRawBTraceSpace n c d hd,
          leafEvenRawBlockProductSign
            (n := n) (b := b) (c := c) (d := d) hd
            (leafRawEvenBlockDataOfTraces
              (n := n) (b := b) (c := c) (d := d) hd H C₂ B₂) := by
  classical
  let e := leafRawEvenBlockTraceEquiv
    (n := n) (b := b) (c := c) (d := d) hd
  calc
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign
        (n := n) (b := b) (c := c) (d := d) hd X)
        =
      ∑ T : (LeafVisibleKernel n b c d × LeafRawCTraceSpace n b d hd)
          × LeafRawBTraceSpace n c d hd,
        leafEvenRawBlockProductSign
          (n := n) (b := b) (c := c) (d := d) hd (e.symm T) := by
        simpa [e] using
          (Equiv.sum_comp e
            (fun T :
              (LeafVisibleKernel n b c d × LeafRawCTraceSpace n b d hd)
                × LeafRawBTraceSpace n c d hd =>
              leafEvenRawBlockProductSign
                (n := n) (b := b) (c := c) (d := d) hd (e.symm T)))
    _ =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ C₂ : LeafRawCTraceSpace n b d hd,
          ∑ B₂ : LeafRawBTraceSpace n c d hd,
            leafEvenRawBlockProductSign
              (n := n) (b := b) (c := c) (d := d) hd
              (leafRawEvenBlockDataOfTraces
                (n := n) (b := b) (c := c) (d := d) hd H C₂ B₂) := by
        rw [Fintype.sum_prod_type]
        rw [Fintype.sum_prod_type]
        simp [e, leafRawEvenBlockTraceEquiv]

theorem leafBRead_tail_raw_triple_sum_eq_sum_base_mul_actualCoeff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    (∑ H : LeafVisibleKernel n b c d,
      ∑ U : LeafBReadTarget n a b c d hd,
        ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          bitSign
            (leafBReadFourierTailPhase
              (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB)
          *
          leafEvenRawBlockProductSign
            (n := n) (b := b) (c := c) (d := d) hd
            (leafBReadTraceData
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB))
      =
    ∑ H : LeafVisibleKernel n b c d,
      bitSign
        (leafRawVisibleBasePhase
          (n := n) (b := b) (c := c) (d := d) hd H)
      *
      leafBReadActualTailFourierCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  classical
  unfold leafBReadActualTailFourierCoeff
  refine Finset.sum_congr rfl ?_
  intro H _
  let base : F :=
    leafRawVisibleBasePhase (n := n) (b := b) (c := c) (d := d) hd H
  calc
    (∑ U : LeafBReadTarget n a b c d hd,
      ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        bitSign
          (leafBReadFourierTailPhase
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB)
        *
        leafEvenRawBlockProductSign
          (n := n) (b := b) (c := c) (d := d) hd
          (leafBReadTraceData
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB))
        =
      ∑ U : LeafBReadTarget n a b c d hd,
        ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          bitSign base *
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
                (n := n) (a := a) (c := c) (d := d) hd) XB) H) := by
          refine Finset.sum_congr rfl ?_
          intro U _
          refine Finset.sum_congr rfl ?_
          intro XB _
          rw [leafEvenRawBlockProductSign_traceData_eq_bitSign_actualRawPhase
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB]
          rw [← bitSign_add, ← bitSign_add]
          congr 1
          dsimp [base]
          ac_rfl
    _ =
      bitSign base *
        (∑ U : LeafBReadTarget n a b c d hd,
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
                  (n := n) (a := a) (c := c) (d := d) hd) XB) H)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro U _
          rw [Finset.mul_sum]
    _ =
      bitSign
        (leafRawVisibleBasePhase
          (n := n) (b := b) (c := c) (d := d) hd H)
      *
      (∑ U : LeafBReadTarget n a b c d hd,
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
                (n := n) (a := a) (c := c) (d := d) hd) XB) H)) := by
          rfl

theorem sum_leafEvenRawBlockProductSign_eq_sum_base_mul_rawFourierCoeff
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign
        (n := n) (b := b) (c := c) (d := d) hd X)
      =
    ∑ H : LeafVisibleKernel n b c d,
      bitSign
        (leafRawVisibleBasePhase
          (n := n) (b := b) (c := c) (d := d) hd H)
      *
      leafBReadRawFourierCoeff
        (n := n) (b := b) (c := c) (d := d) hd H := by
  classical
  rw [sum_leafEvenRawBlockProductSign_eq_sum_raw_traces_evenClosed
    (n := n) (b := b) (c := c) (d := d) hd]
  unfold leafBReadRawFourierCoeff
  refine Finset.sum_congr rfl ?_
  intro H _
  let base : F :=
    leafRawVisibleBasePhase (n := n) (b := b) (c := c) (d := d) hd H
  calc
    (∑ C₂ : LeafRawCTraceSpace n b d hd,
      ∑ B₂ : LeafRawBTraceSpace n c d hd,
        leafEvenRawBlockProductSign
          (n := n) (b := b) (c := c) (d := d) hd
          (leafRawEvenBlockDataOfTraces
            (n := n) (b := b) (c := c) (d := d) hd H C₂ B₂))
        =
      ∑ C₂ : LeafRawCTraceSpace n b d hd,
        ∑ B₂ : LeafRawBTraceSpace n c d hd,
          bitSign base *
          bitSign
            (leafRawCTraceVisibleBPair
              (n := n) (b := b) (c := c) (d := d) hd C₂ H
            + leafRawBTraceVisibleCPair
              (n := n) (b := b) (c := c) (d := d) hd B₂ H) := by
          refine Finset.sum_congr rfl ?_
          intro C₂ _
          refine Finset.sum_congr rfl ?_
          intro B₂ _
          rw [leafEvenRawBlockProductSign_eq_bitSign_rawPhase
            (n := n) (b := b) (c := c) (d := d) hd H C₂ B₂]
          rw [← bitSign_add]
          congr 1
          dsimp [base]
          ac_rfl
    _ =
      bitSign base *
        (∑ C₂ : LeafRawCTraceSpace n b d hd,
          ∑ B₂ : LeafRawBTraceSpace n c d hd,
            bitSign
              (leafRawCTraceVisibleBPair
                (n := n) (b := b) (c := c) (d := d) hd C₂ H
              + leafRawBTraceVisibleCPair
                (n := n) (b := b) (c := c) (d := d) hd B₂ H)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro C₂ _
          rw [Finset.mul_sum]
    _ =
      bitSign
        (leafRawVisibleBasePhase
          (n := n) (b := b) (c := c) (d := d) hd H)
      *
      (∑ C₂ : LeafRawCTraceSpace n b d hd,
        ∑ B₂ : LeafRawBTraceSpace n c d hd,
          bitSign
            (leafRawCTraceVisibleBPair
              (n := n) (b := b) (c := c) (d := d) hd C₂ H
            + leafRawBTraceVisibleCPair
              (n := n) (b := b) (c := c) (d := d) hd B₂ H)) := by
          rfl

/--
WARNING: the following `_of_affine` theorems are conditional bridges only.
The fixed-`H` affine hypothesis should not be used as the route to the
triangle-leaf residual closed form.  The valid replacement is a sum-level global
weighted affine theorem.
-/
theorem leafBReadActualTailFourierCoeff_scaled_eq_rawCoeff_of_affine
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (hAffine :
      (2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
        * (2 : ℤ) ^ kCdCvElimExpNat n a b d
        * leafBReadAffineFiberTailSum
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
      (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
        * leafBReadRawFourierCoeff
          (n := n) (b := b) (c := c) (d := d) hd H) :
    (2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
      * (2 : ℤ) ^ kCdCvElimExpNat n a b d
      * leafBReadActualTailFourierCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
    =
    (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
      * (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
      * leafBReadRawFourierCoeff
        (n := n) (b := b) (c := c) (d := d) hd H := by
  rw [leafBReadActualTailFourierCoeff_eq_card_mul_affine_fiber_sum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  calc
    (2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
        * (2 : ℤ) ^ kCdCvElimExpNat n a b d
        * ((Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
          * leafBReadAffineFiberTailSum
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        =
      (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
        *
        ((2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
          * (2 : ℤ) ^ kCdCvElimExpNat n a b d
          * leafBReadAffineFiberTailSum
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H) := by
          ring
    _ =
      (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
        *
        ((2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
          * leafBReadRawFourierCoeff
            (n := n) (b := b) (c := c) (d := d) hd H) := by
          rw [hAffine]
    _ =
      (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
        * (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
        * leafBReadRawFourierCoeff
          (n := n) (b := b) (c := c) (d := d) hd H := by
          ring

theorem scaled_tail_raw_fourier_sum_eq_card_target_tailmain_raw_of_affine
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (hAffine : ∀ H : LeafVisibleKernel n b c d,
      (2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
        * (2 : ℤ) ^ kCdCvElimExpNat n a b d
        * leafBReadAffineFiberTailSum
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
      (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
        * leafBReadRawFourierCoeff
          (n := n) (b := b) (c := c) (d := d) hd H) :
    (2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
      * (2 : ℤ) ^ kCdCvElimExpNat n a b d
      *
      (∑ H : LeafVisibleKernel n b c d,
        ∑ U : LeafBReadTarget n a b c d hd,
          ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
            bitSign
              (leafBReadFourierTailPhase
                (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB)
            *
            leafEvenRawBlockProductSign
              (n := n) (b := b) (c := c) (d := d) hd
              (leafBReadTraceData
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB))
    =
    (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
      * (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
      *
      (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
        leafEvenRawBlockProductSign
          (n := n) (b := b) (c := c) (d := d) hd X) := by
  classical
  rw [leafBRead_tail_raw_triple_sum_eq_sum_base_mul_actualCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  rw [sum_leafEvenRawBlockProductSign_eq_sum_base_mul_rawFourierCoeff
    (n := n) (b := b) (c := c) (d := d) hd]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro H _
  have hH :=
    leafBReadActualTailFourierCoeff_scaled_eq_rawCoeff_of_affine
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      (hAffine H)
  calc
    (2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
        * (2 : ℤ) ^ kCdCvElimExpNat n a b d
        *
        (bitSign
          (leafRawVisibleBasePhase
            (n := n) (b := b) (c := c) (d := d) hd H)
          *
          leafBReadActualTailFourierCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        =
      bitSign
        (leafRawVisibleBasePhase
          (n := n) (b := b) (c := c) (d := d) hd H)
        *
        ((2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
          * (2 : ℤ) ^ kCdCvElimExpNat n a b d
          * leafBReadActualTailFourierCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H) := by
          ring
    _ =
      bitSign
        (leafRawVisibleBasePhase
          (n := n) (b := b) (c := c) (d := d) hd H)
        *
        ((Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
          * (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
          * leafBReadRawFourierCoeff
            (n := n) (b := b) (c := c) (d := d) hd H) := by
          rw [hH]
    _ =
      (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
        * (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
        *
        (bitSign
          (leafRawVisibleBasePhase
            (n := n) (b := b) (c := c) (d := d) hd H)
          *
          leafBReadRawFourierCoeff
            (n := n) (b := b) (c := c) (d := d) hd H) := by
          ring

theorem scaled_sum_k_leafBReadFiberSignValue_eq_tail_rawEvenBlock_of_affine
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (hAffine : ∀ H : LeafVisibleKernel n b c d,
      (2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
        * (2 : ℤ) ^ kCdCvElimExpNat n a b d
        * leafBReadAffineFiberTailSum
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
      (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
        * leafBReadRawFourierCoeff
          (n := n) (b := b) (c := c) (d := d) hd H) :
    (2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
      *
      (∑ H : LeafVisibleKernel n b c d,
        (2 : ℤ) ^ kCdCvElimExpNat n a b d *
          leafBReadFiberSignValue
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
    =
    (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
      *
      (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
        leafEvenRawBlockProductSign
          (n := n) (b := b) (c := c) (d := d) hd X) := by
  classical
  let C : ℤ := (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
  let S : ℤ := (2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
  let K : ℤ := (2 : ℤ) ^ kCdCvElimExpNat n a b d
  let M : ℤ := (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
  let L : ℤ :=
    ∑ H : LeafVisibleKernel n b c d,
      (2 : ℤ) ^ kCdCvElimExpNat n a b d *
        leafBReadFiberSignValue
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H
  let T : ℤ :=
    ∑ H : LeafVisibleKernel n b c d,
      ∑ U : LeafBReadTarget n a b c d hd,
        ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          bitSign
            (leafBReadFourierTailPhase
              (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB)
          *
          leafEvenRawBlockProductSign
            (n := n) (b := b) (c := c) (d := d) hd
            (leafBReadTraceData
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB)
  let R : ℤ :=
    ∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign
        (n := n) (b := b) (c := c) (d := d) hd X
  have hFourier :
      C * L = K * T := by
    dsimp [C, K, L, T]
    exact leafBReadFiber_scaled_fourier_expansion_with_k_tail_raw
      (n := n) (a := a) (b := b) (c := c) (d := d) hd
  have hTail :
      S * K * T = C * M * R := by
    dsimp [C, S, K, M, T, R]
    exact scaled_tail_raw_fourier_sum_eq_card_target_tailmain_raw_of_affine
      (n := n) (a := a) (b := b) (c := c) (d := d) hd hAffine
  have hCne : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (LeafBReadTarget n a b c d hd) ≠ 0)
  apply mul_left_cancel₀ hCne
  calc
    C *
        ((2 : ℤ) ^ Int.toNat (BReadVisibleTailScaleZ b c d n)
          *
          (∑ H : LeafVisibleKernel n b c d,
            (2 : ℤ) ^ kCdCvElimExpNat n a b d *
              leafBReadFiberSignValue
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H))
        =
      S * (C * L) := by
        dsimp [S, L]
        ring
    _ = S * (K * T) := by
        rw [hFourier]
    _ = S * K * T := by
        ring
    _ = C * M * R := by
        exact hTail
    _ =
      C *
        ((2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n)
          *
          (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
            leafEvenRawBlockProductSign
              (n := n) (b := b) (c := c) (d := d) hd X)) := by
        dsimp [M, R]
        ring

end

end TriangleLeaf
end Core4loop
