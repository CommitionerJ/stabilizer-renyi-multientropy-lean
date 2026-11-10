import Core4loop.SquareDiagonal.EvenP.TotalEEEE.PhaseCoordinate

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 4000000
set_option maxSynthPendingDepth 2048

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEEEEBlockP2

/-- Product of bilinear crosses requiring only the structures that
`LinearMap.prodMap` and `Module.dualProdDualEquivDual` actually need. -/
private noncomputable def crossProdMonoid
    {U₁ U₂ V₁ V₂ : Type*}
    [AddCommMonoid U₁] [Module F U₁]
    [AddCommMonoid U₂] [Module F U₂]
    [AddCommMonoid V₁] [Module F V₁]
    [AddCommMonoid V₂] [Module F V₂]
    (f : U₁ →ₗ[F] Module.Dual F V₁)
    (g : U₂ →ₗ[F] Module.Dual F V₂) :
    (U₁ × U₂) →ₗ[F] Module.Dual F (V₁ × V₂) :=
  (Module.dualProdDualEquivDual F V₁ V₂).toLinearMap.comp
    (f.prodMap g)

@[simp] private theorem crossProdMonoid_apply
    {U₁ U₂ V₁ V₂ : Type*}
    [AddCommMonoid U₁] [Module F U₁]
    [AddCommMonoid U₂] [Module F U₂]
    [AddCommMonoid V₁] [Module F V₁]
    [AddCommMonoid V₂] [Module F V₂]
    (f : U₁ →ₗ[F] Module.Dual F V₁)
    (g : U₂ →ₗ[F] Module.Dual F V₂)
    (u : U₁ × U₂) (v : V₁ × V₂) :
    crossProdMonoid f g u v =
      f u.1 v.1 + g u.2 v.2 :=
  rfl

noncomputable def totalEEEEYBaseCross
    {n : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEYLeftBase n →ₗ[F]
      Module.Dual F (TotalEEEERightInternal.YRightBase n) :=
  LinearMap.mk₂ F TotalEEEEPhase.totalEEEEYBasePhase
    (by
      intro x x' q
      simp only [TotalEEEEPhase.totalEEEEYBasePhase,
        Prod.fst_add, Prod.snd_add, Submodule.coe_add,
        map_add, EEOEInternal.cubeDot_add_left]
      abel)
    (by
      intro r x q
      simp only [TotalEEEEPhase.totalEEEEYBasePhase,
        Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
        map_smul, EEOEInternal.cubeDot_smul_left,
        smul_add]
      rw [← smul_add, map_smul,
        EEOEInternal.cubeDot_smul_left])
    (by
      intro x q q'
      simp only [TotalEEEEPhase.totalEEEEYBasePhase,
        Prod.fst_add, Prod.snd_add, Submodule.coe_add,
        EEOEInternal.cubeDot_add_right]
      abel)
    (by
      intro r x q
      simp only [TotalEEEEPhase.totalEEEEYBasePhase,
        Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
        EEOEInternal.cubeDot_smul_right,
        smul_add])

noncomputable def totalEEEEWBaseCross
    {n : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEWLeftBase n →ₗ[F]
      Module.Dual F (TotalEEEERightInternal.WRightBase n) :=
  LinearMap.mk₂ F TotalEEEEPhase.totalEEEEWBasePhase
    (by
      intro x x' q
      simp only [TotalEEEEPhase.totalEEEEWBasePhase,
        Prod.fst_add, Prod.snd_add, Submodule.coe_add,
        map_add, EEOEInternal.cubeDot_add_left]
      abel)
    (by
      intro r x q
      simp only [TotalEEEEPhase.totalEEEEWBasePhase,
        Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
        map_smul, EEOEInternal.cubeDot_smul_left,
        smul_add]
      rw [← smul_add, map_smul,
        EEOEInternal.cubeDot_smul_left])
    (by
      intro x q q'
      simp only [TotalEEEEPhase.totalEEEEWBasePhase,
        Prod.fst_add, Prod.snd_add, Submodule.coe_add,
        EEOEInternal.cubeDot_add_right]
      abel)
    (by
      intro r x q
      simp only [TotalEEEEPhase.totalEEEEWBasePhase,
        Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
        EEOEInternal.cubeDot_smul_right,
        smul_add])

noncomputable def totalEEEEYZBaseCross
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F]
      Module.Dual F (CyclicCube n × CyclicCube n) :=
  LinearMap.mk₂ F TotalEEEEPhase.totalEEEEYZBasePhase
    (by
      intro x x' q
      simp only [TotalEEEEPhase.totalEEEEYZBasePhase,
        map_add, EEOEInternal.cubeDot_add_left])
    (by
      intro r x q
      simp only [TotalEEEEPhase.totalEEEEYZBasePhase,
        map_smul, EEOEInternal.cubeDot_smul_left])
    (by
      intro x q q'
      simp only [TotalEEEEPhase.totalEEEEYZBasePhase,
        Prod.fst_add, EEOEInternal.cubeDot_add_right])
    (by
      intro r x q
      simp only [TotalEEEEPhase.totalEEEEYZBasePhase,
        Prod.smul_fst, EEOEInternal.cubeDot_smul_right])

noncomputable def totalEEEEWZBaseCross
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F]
      Module.Dual F (CyclicCube n × CyclicCube n) :=
  LinearMap.mk₂ F TotalEEEEPhase.totalEEEEWZBasePhase
    (by
      intro x x' q
      simp only [TotalEEEEPhase.totalEEEEWZBasePhase,
        map_add, EEOEInternal.cubeDot_add_left])
    (by
      intro r x q
      simp only [TotalEEEEPhase.totalEEEEWZBasePhase,
        map_smul, EEOEInternal.cubeDot_smul_left])
    (by
      intro x q q'
      simp only [TotalEEEEPhase.totalEEEEWZBasePhase,
        Prod.fst_add, EEOEInternal.cubeDot_add_right])
    (by
      intro r x q
      simp only [TotalEEEEPhase.totalEEEEWZBasePhase,
        Prod.smul_fst, EEOEInternal.cubeDot_smul_right])

private noncomputable def totalEEEEYWBaseCross
    {n : Nat} [NeZero n] :
    (⊥ : Submodule F (CyclicCube n)) →ₗ[F]
      Module.Dual F (TotalEEEERightInternal.YWRightBase n) :=
  0

private noncomputable def totalEEEEYWZBaseCross
    {n : Nat} [NeZero n] :
    (⊥ : Submodule F (CyclicCube n)) →ₗ[F]
      Module.Dual F (CyclicCube n) :=
  0

@[simp] private theorem totalEEEEYBaseCross_apply
    {n : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEYLeftBase n)
    (q : TotalEEEERightInternal.YRightBase n) :
    totalEEEEYBaseCross x q =
      TotalEEEEPhase.totalEEEEYBasePhase x q :=
  rfl

@[simp] private theorem totalEEEEWBaseCross_apply
    {n : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEWLeftBase n)
    (q : TotalEEEERightInternal.WRightBase n) :
    totalEEEEWBaseCross x q =
      TotalEEEEPhase.totalEEEEWBasePhase x q :=
  rfl

@[simp] private theorem totalEEEEYZBaseCross_apply
    {n : Nat} [NeZero n]
    (x : CyclicCube n) (q : CyclicCube n × CyclicCube n) :
    totalEEEEYZBaseCross x q =
      TotalEEEEPhase.totalEEEEYZBasePhase x q :=
  rfl

@[simp] private theorem totalEEEEWZBaseCross_apply
    {n : Nat} [NeZero n]
    (x : CyclicCube n) (q : CyclicCube n × CyclicCube n) :
    totalEEEEWZBaseCross x q =
      TotalEEEEPhase.totalEEEEWZBasePhase x q :=
  rfl

@[simp] private theorem totalEEEEYWBaseCross_apply
    {n : Nat} [NeZero n]
    (x : (⊥ : Submodule F (CyclicCube n)))
    (q : TotalEEEERightInternal.YWRightBase n) :
    totalEEEEYWBaseCross x q =
      TotalEEEEPhase.totalEEEEYWBasePhase x q := by
  rfl

@[simp] private theorem totalEEEEYWZBaseCross_apply
    {n : Nat} [NeZero n]
    (x : (⊥ : Submodule F (CyclicCube n)))
    (q : CyclicCube n) :
    totalEEEEYWZBaseCross x q =
      TotalEEEEPhase.totalEEEEYWZBasePhase x q := by
  rfl

private noncomputable def totalEEEEYTailCross
    {n b : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEYTailLeft n b →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n b
          (TotalEEEERightInternal.YRightBase n)) :=
  diamondTailAmplify (totalEEEEYBaseCross (n := n))

private noncomputable def totalEEEEWTailCross
    {n d : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEWTailLeft n d →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n d
          (TotalEEEERightInternal.WRightBase n)) :=
  diamondTailAmplify (totalEEEEWBaseCross (n := n))

private noncomputable def totalEEEEZTailCross
    {n c : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEZTailLeft n c →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n c
          (DiamondEEOERightAmbient n)) :=
  diamondTailAmplify (diamondTailAllEvenZCross (n := n))

private noncomputable def totalEEEEYZTailCross
    {n b c : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEYZTailLeft n b c →ₗ[F]
      Module.Dual F
        (DiamondMixedTailZero n b c
          (CyclicCube n × CyclicCube n)) :=
  diamondMixedTailAmplify (totalEEEEYZBaseCross (n := n))

private noncomputable def totalEEEEWZTailCross
    {n c d : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEWZTailLeft n c d →ₗ[F]
      Module.Dual F
        (DiamondMixedTailZero n c d
          (CyclicCube n × CyclicCube n)) :=
  diamondMixedTailAmplify (totalEEEEWZBaseCross (n := n))

private noncomputable def totalEEEEYWTailCross
    {n b d : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEYWLeftZero n b d →ₗ[F]
      Module.Dual F
        (DiamondMixedTailZero n b d
          (TotalEEEERightInternal.YWRightBase n)) :=
  diamondMixedTailAmplify (totalEEEEYWBaseCross (n := n))

private noncomputable def totalEEEEYWZTailCross
    {n b c d : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n b
          (DiamondEvenAxisValueTailZero n c
            (DiamondEvenAxisValueTailZero n d
              (CyclicCube n)))) :=
  diamondTailAmplify
    (n := n) (k := b)
    (diamondTailAmplify
      (n := n) (k := c)
      (diamondTailAmplify
        (n := n) (k := d)
        (totalEEEEYWZBaseCross (n := n))))

@[simp] private theorem totalEEEEYTailCross_apply
    {n b : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEYTailLeft n b)
    (q : DiamondEvenAxisValueTailZero n b
      (TotalEEEERightInternal.YRightBase n)) :
    totalEEEEYTailCross x q =
      ∑ yt : DiamondEvenAxisTailIndex n b,
        TotalEEEEPhase.totalEEEEYBasePhase
          (x.1 yt) (q.1 yt) :=
  rfl

@[simp] private theorem totalEEEEWTailCross_apply
    {n d : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEWTailLeft n d)
    (q : DiamondEvenAxisValueTailZero n d
      (TotalEEEERightInternal.WRightBase n)) :
    totalEEEEWTailCross x q =
      ∑ wt : DiamondEvenAxisTailIndex n d,
        TotalEEEEPhase.totalEEEEWBasePhase
          (x.1 wt) (q.1 wt) :=
  rfl

@[simp] private theorem totalEEEEZTailCross_apply
    {n c : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEZTailLeft n c)
    (q : DiamondEvenAxisValueTailZero n c
      (DiamondEEOERightAmbient n)) :
    totalEEEEZTailCross x q =
      ∑ zt : DiamondEvenAxisTailIndex n c,
        diamondTailAllEvenZCross (x.1 zt) (q.1 zt) :=
  rfl

@[simp] private theorem totalEEEEYZTailCross_apply
    {n b c : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEYZTailLeft n b c)
    (q : DiamondMixedTailZero n b c
      (CyclicCube n × CyclicCube n)) :
    totalEEEEYZTailCross x q =
      ∑ yt : DiamondEvenAxisTailIndex n b,
        ∑ zt : DiamondEvenAxisTailIndex n c,
          TotalEEEEPhase.totalEEEEYZBasePhase
            ((x.1 yt).1 zt) ((q.1 yt).1 zt) :=
  rfl

@[simp] private theorem totalEEEEWZTailCross_apply
    {n c d : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEWZTailLeft n c d)
    (q : DiamondMixedTailZero n c d
      (CyclicCube n × CyclicCube n)) :
    totalEEEEWZTailCross x q =
      ∑ zt : DiamondEvenAxisTailIndex n c,
        ∑ wt : DiamondEvenAxisTailIndex n d,
          TotalEEEEPhase.totalEEEEWZBasePhase
            ((x.1 zt).1 wt) ((q.1 zt).1 wt) :=
  rfl

@[simp] private theorem totalEEEEYWTailCross_apply
    {n b d : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEYWLeftZero n b d)
    (q : DiamondMixedTailZero n b d
      (TotalEEEERightInternal.YWRightBase n)) :
    totalEEEEYWTailCross x q =
      ∑ yt : DiamondEvenAxisTailIndex n b,
        ∑ wt : DiamondEvenAxisTailIndex n d,
          TotalEEEEPhase.totalEEEEYWBasePhase
            ((x.1 yt).1 wt) ((q.1 yt).1 wt) :=
  rfl

@[simp] private theorem totalEEEEYWZTailCross_apply
    {n b c d : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d)
    (q : DiamondEvenAxisValueTailZero n b
      (DiamondEvenAxisValueTailZero n c
        (DiamondEvenAxisValueTailZero n d (CyclicCube n)))) :
    totalEEEEYWZTailCross x q =
      ∑ yt : DiamondEvenAxisTailIndex n b,
        ∑ zt : DiamondEvenAxisTailIndex n c,
          ∑ wt : DiamondEvenAxisTailIndex n d,
            TotalEEEEPhase.totalEEEEYWZBasePhase
              (((x.1 yt).1 zt).1 wt)
              (((q.1 yt).1 zt).1 wt) :=
  rfl

private noncomputable def totalEEEEYWAndYWZCross
    {n b c d : Nat} [NeZero n] :
    (TotalEEEEInternal.TotalEEEEYWLeftZero n b d ×
      TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d) →ₗ[F]
      Module.Dual F
        (DiamondMixedTailZero n b d
            (TotalEEEERightInternal.YWRightBase n) ×
          DiamondEvenAxisValueTailZero n b
            (DiamondEvenAxisValueTailZero n c
              (DiamondEvenAxisValueTailZero n d
                (CyclicCube n)))) :=
  crossProdMonoid
    (totalEEEEYWTailCross (n := n) (b := b) (d := d))
    (totalEEEEYWZTailCross (n := n) (b := b) (c := c) (d := d))

private noncomputable def totalEEEEWZAndRestCross
    {n b c d : Nat} [NeZero n] :
    (TotalEEEEInternal.TotalEEEEWZTailLeft n c d ×
      (TotalEEEEInternal.TotalEEEEYWLeftZero n b d ×
        TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d)) →ₗ[F]
      Module.Dual F
        (DiamondMixedTailZero n c d
            (CyclicCube n × CyclicCube n) ×
          (DiamondMixedTailZero n b d
              (TotalEEEERightInternal.YWRightBase n) ×
            DiamondEvenAxisValueTailZero n b
              (DiamondEvenAxisValueTailZero n c
                (DiamondEvenAxisValueTailZero n d
                  (CyclicCube n))))) :=
  crossProdMonoid
    (totalEEEEWZTailCross (n := n) (c := c) (d := d))
    (totalEEEEYWAndYWZCross (n := n) (b := b) (c := c) (d := d))

private noncomputable def totalEEEEYZAndRestCross
    {n b c d : Nat} [NeZero n] :
    (TotalEEEEInternal.TotalEEEEYZTailLeft n b c ×
      (TotalEEEEInternal.TotalEEEEWZTailLeft n c d ×
        (TotalEEEEInternal.TotalEEEEYWLeftZero n b d ×
          TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d))) →ₗ[F]
      Module.Dual F
        (DiamondMixedTailZero n b c
            (CyclicCube n × CyclicCube n) ×
          (DiamondMixedTailZero n c d
              (CyclicCube n × CyclicCube n) ×
            (DiamondMixedTailZero n b d
                (TotalEEEERightInternal.YWRightBase n) ×
              DiamondEvenAxisValueTailZero n b
                (DiamondEvenAxisValueTailZero n c
                  (DiamondEvenAxisValueTailZero n d
                    (CyclicCube n)))))) :=
  crossProdMonoid
    (totalEEEEYZTailCross (n := n) (b := b) (c := c))
    (totalEEEEWZAndRestCross (n := n) (b := b) (c := c) (d := d))

private noncomputable def totalEEEEZAndRestCross
    {n b c d : Nat} [NeZero n] :
    (TotalEEEEInternal.TotalEEEEZTailLeft n c ×
      (TotalEEEEInternal.TotalEEEEYZTailLeft n b c ×
        (TotalEEEEInternal.TotalEEEEWZTailLeft n c d ×
          (TotalEEEEInternal.TotalEEEEYWLeftZero n b d ×
            TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d)))) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n c
            (DiamondEEOERightAmbient n) ×
          (DiamondMixedTailZero n b c
              (CyclicCube n × CyclicCube n) ×
            (DiamondMixedTailZero n c d
                (CyclicCube n × CyclicCube n) ×
              (DiamondMixedTailZero n b d
                  (TotalEEEERightInternal.YWRightBase n) ×
                DiamondEvenAxisValueTailZero n b
                  (DiamondEvenAxisValueTailZero n c
                    (DiamondEvenAxisValueTailZero n d
                      (CyclicCube n))))))) :=
  crossProdMonoid
    (totalEEEEZTailCross (n := n) (c := c))
    (totalEEEEYZAndRestCross (n := n) (b := b) (c := c) (d := d))

private noncomputable def totalEEEEWAndRestCross
    {n b c d : Nat} [NeZero n] :
    (TotalEEEEInternal.TotalEEEEWTailLeft n d ×
      (TotalEEEEInternal.TotalEEEEZTailLeft n c ×
        (TotalEEEEInternal.TotalEEEEYZTailLeft n b c ×
          (TotalEEEEInternal.TotalEEEEWZTailLeft n c d ×
            (TotalEEEEInternal.TotalEEEEYWLeftZero n b d ×
              TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d))))) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n d
            (TotalEEEERightInternal.WRightBase n) ×
          (DiamondEvenAxisValueTailZero n c
              (DiamondEEOERightAmbient n) ×
            (DiamondMixedTailZero n b c
                (CyclicCube n × CyclicCube n) ×
              (DiamondMixedTailZero n c d
                  (CyclicCube n × CyclicCube n) ×
                (DiamondMixedTailZero n b d
                    (TotalEEEERightInternal.YWRightBase n) ×
                  DiamondEvenAxisValueTailZero n b
                    (DiamondEvenAxisValueTailZero n c
                      (DiamondEvenAxisValueTailZero n d
                        (CyclicCube n)))))))) :=
  crossProdMonoid
    (totalEEEEWTailCross (n := n) (d := d))
    (totalEEEEZAndRestCross (n := n) (b := b) (c := c) (d := d))

private noncomputable def totalEEEEYAndRestCross
    {n b c d : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEELeftSourceTailTarget n b c d →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n b
            (TotalEEEERightInternal.YRightBase n) ×
          (DiamondEvenAxisValueTailZero n d
              (TotalEEEERightInternal.WRightBase n) ×
            (DiamondEvenAxisValueTailZero n c
                (DiamondEEOERightAmbient n) ×
              (DiamondMixedTailZero n b c
                  (CyclicCube n × CyclicCube n) ×
                (DiamondMixedTailZero n c d
                    (CyclicCube n × CyclicCube n) ×
                  (DiamondMixedTailZero n b d
                      (TotalEEEERightInternal.YWRightBase n) ×
                    DiamondEvenAxisValueTailZero n b
                      (DiamondEvenAxisValueTailZero n c
                        (DiamondEvenAxisValueTailZero n d
                          (CyclicCube n))))))))) :=
  crossProdMonoid
    (totalEEEEYTailCross (n := n) (b := b))
    (totalEEEEWAndRestCross (n := n) (b := b) (c := c) (d := d))

/-- Frozen eight-block cross in the exact source/reachable-target association. -/
noncomputable def diamondEEEETotalBlockCross
    {n b c d : Nat} [NeZero n] :
    TotalEEEELeftSourceTarget n b c d →ₗ[F]
      Module.Dual F (TotalEEEERightReachableTarget n b c d) :=
  crossProdMonoid
    (diamondEEEECross (n := n))
    (totalEEEEYAndRestCross (n := n) (b := b) (c := c) (d := d))

/-- The frozen block cross is pointwise the eight-sector coordinate phase. -/
theorem diamondEEEETotalBlockCross_apply
    {n b c d : Nat} [NeZero n]
    (l : TotalEEEELeftSourceTarget n b c d)
    (q : TotalEEEERightReachableTarget n b c d) :
    diamondEEEETotalBlockCross l q =
      TotalEEEEPhase.totalEEEECoordinatePhase l q := by
  simp only [diamondEEEETotalBlockCross,
    totalEEEEYAndRestCross, totalEEEEWAndRestCross,
    totalEEEEZAndRestCross, totalEEEEYZAndRestCross,
    totalEEEEWZAndRestCross, totalEEEEYWAndYWZCross,
    crossProdMonoid_apply, totalEEEEYTailCross_apply,
    totalEEEEWTailCross_apply, totalEEEEZTailCross_apply,
    totalEEEEYZTailCross_apply, totalEEEEWZTailCross_apply,
    totalEEEEYWTailCross_apply, totalEEEEYWZTailCross_apply,
    TotalEEEEPhase.totalEEEECoordinatePhase]
  ac_rfl

/-- Literal all-even phase equals the frozen typed block cross. -/
theorem diamondEvenPCross_EEEE_phase
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (A : DiamondEvenPReachableA n b c d) :
    diamondEEEETotalBlockCross
        (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 l)
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      diamondEvenPCross l A := by
  rw [diamondEEEETotalBlockCross_apply]
  exact
    (TotalEEEEPhase.totalEEEELiteralPhaseCoordinateSplit
      hn hb2 hc2 hd2 l A).symm

end TotalEEEEBlockP2

end

end Core4loop.SquareDiagonal.EvenP
