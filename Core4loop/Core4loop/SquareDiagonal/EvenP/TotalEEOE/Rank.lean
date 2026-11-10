import Core4loop.SquareDiagonal.EvenP.TotalEEOE.BlockAlignment

set_option autoImplicit false
set_option warningAsError true
-- The frozen nested range/rank certificate uses one file-wide elaboration budget.
set_option linter.style.setOption false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 12000000

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace T37RangeRankP3

private local instance {n : Nat} [NeZero n] :
    AddCommGroup (↥(⊥ : Submodule F (CyclicCube n))) :=
  (⊥ : Submodule F (CyclicCube n)).addCommGroup

private local instance {n d : Nat} [NeZero n] :
    AddCommGroup
      (DiamondEvenAxisValueTailZero n d
        (⊥ : Submodule F (CyclicCube n))) :=
  (DiamondEvenAxisValueTailZero n d
    (⊥ : Submodule F (CyclicCube n))).addCommGroup

private local instance {n b d : Nat} [NeZero n] :
    AddCommGroup (T37LeftP0.T37MixedLeftZero n b d) :=
  (T37LeftP0.T37MixedLeftZero n b d).addCommGroup

private local instance {n : Nat} [NeZero n] :
    AddCommGroup (T37RightP1.T37JKernel n) :=
  (T37RightP1.T37JKernel n).addCommGroup

private local instance {n d : Nat} [NeZero n] :
    AddCommGroup
      (DiamondEvenAxisValueTailZero n d
        (T37RightP1.T37JKernel n)) :=
  (DiamondEvenAxisValueTailZero n d
    (T37RightP1.T37JKernel n)).addCommGroup

private local instance {n b d : Nat} [NeZero n] :
    AddCommGroup
      (DiamondMixedTailZero n b d
        (T37RightP1.T37JKernel n)) :=
  (DiamondMixedTailZero n b d
    (T37RightP1.T37JKernel n)).addCommGroup

private local instance t37EEOELeftFiniteDimensional
    (n : Nat) [NeZero n] :
    FiniteDimensional F (DiamondEEOELeftSource n) :=
  FiniteDimensional.of_injective
    (DiamondEEOELeftSource n).subtype Subtype.val_injective

private local instance t37YTailLeftFiniteDimensional
    (n b : Nat) [NeZero n] :
    FiniteDimensional F
      (DiamondEvenAxisValueTailZero n b
        (EEOEInternal.RBlockLeft n)) :=
  FiniteDimensional.of_injective
    (DiamondEvenAxisValueTailZero n b
      (EEOEInternal.RBlockLeft n)).subtype Subtype.val_injective

private local instance t37WTailLeftFiniteDimensional
    (n d : Nat) [NeZero n] :
    FiniteDimensional F
      (DiamondEvenAxisValueTailZero n d
        (EEOEInternal.PBlockLeft n)) :=
  FiniteDimensional.of_injective
    (DiamondEvenAxisValueTailZero n d
      (EEOEInternal.PBlockLeft n)).subtype Subtype.val_injective

private local instance t37MixedLeftFiniteDimensional
    (n b d : Nat) [NeZero n] :
    FiniteDimensional F
      (T37LeftP0.T37MixedLeftZero n b d) :=
  FiniteDimensional.of_injective
    (T37LeftP0.T37MixedLeftZero n b d).subtype
      Subtype.val_injective

noncomputable def t37RangeTransport
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    LinearMap.range
        (diamondEvenPCross
          (n := n) (b := b) (c := 1) (d := d)) ≃ₗ[F]
      LinearMap.range
        (T37TypedBlockP2.t37TotalBlockCross
          (n := n) (b := b) (d := d)) :=
  BWSymmetryInternal.rangeTransportEquiv
    (L := DiamondEvenPLeft n b 1 d)
    (R := DiamondEvenPReachableA n b 1 d)
    (L' := T37LeftP0.T37LeftSourceTarget n b d)
    (R' := T37RightP1.T37RightReachableTarget n b d)
    (diamondEvenPCross
      (n := n) (b := b) (c := 1) (d := d))
    (T37TypedBlockP2.t37TotalBlockCross
      (n := n) (b := b) (d := d))
    (T37LeftP0.t37LeftSourceEquiv hn hb2 hd2)
    (T37RightP1.t37RightReachableEquiv hn hb2 hd2)
    (T37TypedBlockP2.t37PointwisePhaseSquare hn hb2 hd2)

theorem t37TotalBlockCross_rank_addition_first
    {n b d : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (T37TypedBlockP2.t37TotalBlockCross
            (n := n) (b := b) (d := d))) =
      Module.finrank F
          (LinearMap.range (diamondEEOECross (n := n))) +
        (Module.finrank F
            (LinearMap.range
              (T37TypedBlockP2.t37YTailCross
                (n := n) (b := b))) +
          (Module.finrank F
              (LinearMap.range
                (T37TypedBlockP2.t37WTailCross
                  (n := n) (d := d))) +
            Module.finrank F
              (LinearMap.range
                (T37TypedBlockP2.t37YWTailCross
                  (n := n) (b := b) (d := d))))) := by
  unfold T37TypedBlockP2.t37TotalBlockCross
  rw [finrank_range_diamondCrossProd
    (U₁ := DiamondEEOELeftSource n)
    (U₂ :=
      DiamondEvenAxisValueTailZero n b
          (EEOEInternal.RBlockLeft n) ×
        (DiamondEvenAxisValueTailZero n d
            (EEOEInternal.PBlockLeft n) ×
          T37LeftP0.T37MixedLeftZero n b d))
    (V₁ := DiamondEEOERightSource n)
    (V₂ :=
      DiamondEvenAxisValueTailZero n b (T37YRightBase n) ×
        (DiamondEvenAxisValueTailZero n d (T37WRightBase n) ×
          DiamondMixedTailZero n b d
            (T37RightP1.T37JKernel n)))
    (diamondEEOECross (n := n))
    (T37TypedBlockP2.t37TailBlockCross
      (n := n) (b := b) (d := d))]
  unfold T37TypedBlockP2.t37TailBlockCross
  rw [finrank_range_diamondCrossProd
    (U₁ := DiamondEvenAxisValueTailZero n b
      (EEOEInternal.RBlockLeft n))
    (U₂ :=
      DiamondEvenAxisValueTailZero n d
          (EEOEInternal.PBlockLeft n) ×
        T37LeftP0.T37MixedLeftZero n b d)
    (V₁ := DiamondEvenAxisValueTailZero n b (T37YRightBase n))
    (V₂ :=
      DiamondEvenAxisValueTailZero n d (T37WRightBase n) ×
        DiamondMixedTailZero n b d
          (T37RightP1.T37JKernel n))
    (T37TypedBlockP2.t37YTailCross (n := n) (b := b))
    (T37TypedBlockP2.t37WTailAndMixedCross
      (n := n) (b := b) (d := d))]
  unfold T37TypedBlockP2.t37WTailAndMixedCross
  rw [finrank_range_diamondCrossProd
    (U₁ := DiamondEvenAxisValueTailZero n d
      (EEOEInternal.PBlockLeft n))
    (U₂ := T37LeftP0.T37MixedLeftZero n b d)
    (V₁ := DiamondEvenAxisValueTailZero n d (T37WRightBase n))
    (V₂ := DiamondMixedTailZero n b d
      (T37RightP1.T37JKernel n))
    (T37TypedBlockP2.t37WTailCross (n := n) (d := d))
    (T37TypedBlockP2.t37YWTailCross
      (n := n) (b := b) (d := d))]

theorem t37RankYTailCross_eq_zero
    {n b : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (T37TypedBlockP2.t37YTailCross
            (n := n) (b := b))) = 0 := by
  rw [T37TypedBlockP2.t37YTailCross_eq_zero,
    LinearMap.range_zero]
  exact finrank_bot F _

theorem t37RankWTailCross_eq_zero
    {n d : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (T37TypedBlockP2.t37WTailCross
            (n := n) (d := d))) = 0 := by
  rw [T37TypedBlockP2.t37WTailCross_eq_zero,
    LinearMap.range_zero]
  exact finrank_bot F _

theorem t37RankYWTailCross_eq_zero
    {n b d : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (T37TypedBlockP2.t37YWTailCross
            (n := n) (b := b) (d := d))) = 0 := by
  rw [T37TypedBlockP2.t37YWTailCross_eq_zero,
    LinearMap.range_zero]
  exact finrank_bot F _

theorem t37TotalBlockCross_rank_eq_scalar
    {n b d : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (T37TypedBlockP2.t37TotalBlockCross
            (n := n) (b := b) (d := d))) =
      Module.finrank F
        (LinearMap.range (diamondEEOECross (n := n))) := by
  rw [t37TotalBlockCross_rank_addition_first,
    t37RankYTailCross_eq_zero,
    t37RankWTailCross_eq_zero,
    t37RankYWTailCross_eq_zero]
  simp

theorem t37TotalBlockCross_rank
    {n b d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (_hb2 : 2 ≤ b) (_hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (T37TypedBlockP2.t37TotalBlockCross
            (n := n) (b := b) (d := d))) =
      2 * (n - 1) ^ 2 := by
  rw [t37TotalBlockCross_rank_eq_scalar]
  exact rank_diamondEvenP_cross_EEOE_scalar hn2 hn

theorem t37LiteralCross_rank
    {n b d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := b) (c := 1) (d := d))) =
      2 * (n - 1) ^ 2 := by
  calc
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := b) (c := 1) (d := d))) =
        Module.finrank F
          (LinearMap.range
            (T37TypedBlockP2.t37TotalBlockCross
              (n := n) (b := b) (d := d))) :=
      LinearEquiv.finrank_eq
        (t37RangeTransport hn hb2 hd2)
    _ = 2 * (n - 1) ^ 2 :=
      t37TotalBlockCross_rank
        hn2 hn hb2 hd2

end T37RangeRankP3

end

end Core4loop.SquareDiagonal.EvenP
