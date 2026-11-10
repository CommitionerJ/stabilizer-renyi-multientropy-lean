import Core4loop.SquareDiagonal.EvenP.TotalEEOE.PhaseCoordinate

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
-- The frozen typed four-block alignment uses one file-wide elaboration budget.
set_option linter.style.setOption false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 12000000

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace T37TypedBlockP2

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

noncomputable def t37YTailCross
    {n b : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n b
        (EEOEInternal.RBlockLeft n) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n b (T37YRightBase n)) :=
  diamondTailAmplify (t37YBaseCross (n := n))

noncomputable def t37WTailCross
    {n d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n d
        (EEOEInternal.PBlockLeft n) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n d (T37WRightBase n)) :=
  diamondTailAmplify (t37WBaseCross (n := n))

noncomputable def t37YWTailCross
    {n b d : Nat} [NeZero n] :
    T37LeftP0.T37MixedLeftZero n b d →ₗ[F]
      Module.Dual F
        (DiamondMixedTailZero n b d
          (T37RightP1.T37JKernel n)) :=
  diamondMixedTailAmplify (t37MixedBaseCross (n := n))

theorem t37YTailCross_eq_zero
    {n b : Nat} [NeZero n] :
    t37YTailCross (n := n) (b := b) = 0 := by
  rw [t37YTailCross, t37YBaseCross_eq_zero]
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  simp

theorem t37WTailCross_eq_zero
    {n d : Nat} [NeZero n] :
    t37WTailCross (n := n) (d := d) = 0 := by
  rw [t37WTailCross, t37WBaseCross_eq_zero]
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  simp

theorem t37YWTailCross_eq_zero
    {n b d : Nat} [NeZero n] :
    t37YWTailCross (n := n) (b := b) (d := d) = 0 := by
  rw [t37YWTailCross, t37MixedBaseCross_eq_zero]
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  simp [diamondMixedTailAmplify]

noncomputable def t37WTailAndMixedCross
    {n b d : Nat} [NeZero n] :
    (DiamondEvenAxisValueTailZero n d
        (EEOEInternal.PBlockLeft n) ×
      T37LeftP0.T37MixedLeftZero n b d) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n d (T37WRightBase n) ×
          DiamondMixedTailZero n b d
            (T37RightP1.T37JKernel n)) :=
  diamondCrossProd
    (U₁ := DiamondEvenAxisValueTailZero n d
      (EEOEInternal.PBlockLeft n))
    (U₂ := T37LeftP0.T37MixedLeftZero n b d)
    (V₁ := DiamondEvenAxisValueTailZero n d (T37WRightBase n))
    (V₂ := DiamondMixedTailZero n b d
      (T37RightP1.T37JKernel n))
    (t37WTailCross (n := n) (d := d))
    (t37YWTailCross (n := n) (b := b) (d := d))

noncomputable def t37TailBlockCross
    {n b d : Nat} [NeZero n] :
    (DiamondEvenAxisValueTailZero n b
        (EEOEInternal.RBlockLeft n) ×
      (DiamondEvenAxisValueTailZero n d
          (EEOEInternal.PBlockLeft n) ×
        T37LeftP0.T37MixedLeftZero n b d)) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n b (T37YRightBase n) ×
          (DiamondEvenAxisValueTailZero n d (T37WRightBase n) ×
            DiamondMixedTailZero n b d
              (T37RightP1.T37JKernel n))) :=
  diamondCrossProd
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
    (t37YTailCross (n := n) (b := b))
    (t37WTailAndMixedCross (n := n) (b := b) (d := d))

noncomputable def t37TotalBlockCross
    {n b d : Nat} [NeZero n] :
    T37LeftP0.T37LeftSourceTarget n b d →ₗ[F]
      Module.Dual F
        (T37RightP1.T37RightReachableTarget n b d) :=
  diamondCrossProd
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
    (t37TailBlockCross (n := n) (b := b) (d := d))

theorem t37TotalBlockCross_apply_eq_scalar
    {n b d : Nat} [NeZero n]
    (l : T37LeftP0.T37LeftSourceTarget n b d)
    (A : T37RightP1.T37RightReachableTarget n b d) :
    t37TotalBlockCross l A =
      diamondEEOECross l.1 A.1 := by
  unfold t37TotalBlockCross t37TailBlockCross
    t37WTailAndMixedCross diamondCrossProd
  rw [t37YTailCross_eq_zero, t37WTailCross_eq_zero,
    t37YWTailCross_eq_zero]
  simp

theorem t37PointwisePhaseSquare
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b 1 d)
    (A : DiamondEvenPReachableA n b 1 d) :
    t37TotalBlockCross
        (T37LeftP0.t37LeftSourceEquiv hn hb2 hd2 l)
        (T37RightP1.t37RightReachableEquiv hn hb2 hd2 A) =
      diamondEvenPCross l A := by
  rw [t37TotalBlockCross_apply_eq_scalar]
  exact
    (T37PhaseD.dT37LiteralPhase_eq_scalar
      hn hb2 hd2 l A).symm

end T37TypedBlockP2

end

end Core4loop.SquareDiagonal.EvenP
