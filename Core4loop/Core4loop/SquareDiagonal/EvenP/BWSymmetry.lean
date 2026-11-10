import Core4loop.SquareDiagonal.PreC.Reduction
import Core4loop.SquareDiagonal.EvenP.EOEE
import Core4loop.SquareDiagonal.EvenP.EEOE

open scoped BigOperators

set_option linter.unnecessarySeqFocus false

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

/-!
The square-diagonal graph is invariant under exchanging the B and W
vertices.  This file records that symmetry twice: first on the literal
strict Pre-C finite-assignment source, and then on the scalar branch
carriers used by the even-P rank calculation.
-/

noncomputable def diamondBWPreCAmbientEquiv
    {n a b c d : Nat} [NeZero n] :
    (AFun4 n b c d × BFun4 n a c d × WFun4 n a b c) ≃ₗ[F]
      (AFun4 n d c b × BFun4 n a c b × WFun4 n a d c) where
  toFun x :=
    (fun w z y => x.1 y z w,
      fun p sw z y => x.2.2 p y z sw,
      fun p w z sy => x.2.1 p sy z w)
  invFun x :=
    (fun y z w => x.1 w z y,
      fun p sy z w => x.2.2 p w z sy,
      fun p y z sw => x.2.1 p sw z y)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def diamondBWCFunEquiv
    {n a b _c d : Nat} [NeZero n] :
    CFun4 n a b d ≃ₗ[F] CFun4 n a d b where
  toFun C := fun p w sz y => C p y sz w
  invFun C := fun p y sz w => C p w sz y
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

namespace BWSymmetryInternal

theorem swapKC
    {n a b c d : Nat} [NeZero n]
    (C : CFun4 n a b d) (w : WVec n d) (z : ZVec n c)
    (y : YVec n b) :
    KCMap (n := n) (a := a) (b := d) (c := c) (d := b)
        (diamondBWCFunEquiv (_c := c) C) w z y =
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
        C y z w := by
  simp [KCMap, diamondBWCFunEquiv, dzC, deltaC, etaC]

theorem swapCompat
    {n a b c d : Nat} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (p : PVec n a) (w : WVec n d) (sz : I n) (y : YVec n b) :
    squareCompat
        (n := n) (a := a) (b := d) (c := c) (d := b)
        ((fun p sw z y => W p y z sw),
          (fun p w z sy => B p sy z w))
        p w sz y =
      squareCompat
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (B, W) p y sz w := by
  change
    squareCompatFun
        (fun p sw z y => W p y z sw)
        (fun p w z sy => B p sy z w)
        p w sz y =
      squareCompatFun B W p y sz w
  unfold squareCompatFun
  simp only [betaB, gammaB, xiW, zetaW]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro z hz <;>
    split_ifs <;>
    ring

theorem phaseCore
    {n a b c d : Nat} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) :
    coeffApplyA
        (KBMap (n := n) (a := a) (b := d) (c := c) (d := b)
            (diamondBWPreCAmbientEquiv (A, B, W)).2.1 +
          KWMap (n := n) (a := a) (b := d) (c := c) (d := b)
            (diamondBWPreCAmbientEquiv (A, B, W)).2.2)
        (diamondBWPreCAmbientEquiv (A, B, W)).1 =
      coeffApplyA
        (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B +
          KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W)
        A := by
  classical
  rw [coeffApplyA_eq_sum, coeffApplyA_eq_sum]
  simp only [diamondBWPreCAmbientEquiv, LinearEquiv.coe_mk,
    KBMap, KWMap, dyB, betaB, gammaB, dwW, xiW, zetaW,
    Pi.add_apply]
  calc
    (∑ w : WVec n d, ∑ z : ZVec n c, ∑ y : YVec n b,
        A y z w *
          ((∑ p : PVec n a,
              (W p y z (vecSum w) + W p y z (vecSum w + 1))) +
            ∑ p : PVec n a,
              (B p (vecSum y) z w + B p (vecSum y + 1) z w))) =
      ∑ z : ZVec n c, ∑ w : WVec n d, ∑ y : YVec n b,
        A y z w *
          ((∑ p : PVec n a,
              (W p y z (vecSum w) + W p y z (vecSum w + 1))) +
            ∑ p : PVec n a,
              (B p (vecSum y) z w + B p (vecSum y + 1) z w)) :=
        Finset.sum_comm
    _ =
      ∑ z : ZVec n c, ∑ y : YVec n b, ∑ w : WVec n d,
        A y z w *
          ((∑ p : PVec n a,
              (W p y z (vecSum w) + W p y z (vecSum w + 1))) +
            ∑ p : PVec n a,
              (B p (vecSum y) z w + B p (vecSum y + 1) z w)) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.sum_comm]
    _ =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        A y z w *
          ((∑ p : PVec n a,
              (W p y z (vecSum w) + W p y z (vecSum w + 1))) +
            ∑ p : PVec n a,
              (B p (vecSum y) z w + B p (vecSum y + 1) z w)) :=
        Finset.sum_comm
    _ =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        A y z w *
          ((∑ p : PVec n a,
              (B p (vecSum y) z w + B p (vecSum y + 1) z w)) +
            ∑ p : PVec n a,
              (W p y z (vecSum w) + W p y z (vecSum w + 1))) := by
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro z _
        apply Finset.sum_congr rfl
        intro w _
        ring

end BWSymmetryInternal

theorem diamondBWSwap_cPhase
    {n a b c d : Nat} [NeZero n]
    (x : AFun4 n b c d × BFun4 n a c d × WFun4 n a b c)
    (C : CFun4 n a b d) :
    diamondCPhaseCoeffClean
        (diamondBWPreCAmbientEquiv x).1
        (diamondBWPreCAmbientEquiv x).2.1
        (diamondBWPreCAmbientEquiv x).2.2
        (diamondBWCFunEquiv (_c := c) C) =
      diamondCPhaseCoeffClean x.1 x.2.1 x.2.2 C := by
  rcases x with ⟨A, B, W⟩
  classical
  unfold diamondCPhaseCoeffClean coeffApplyA coeffApply
  simp only [aFun4Equiv, cFun4Equiv, LinearEquiv.coe_mk,
    Equiv.coe_fn_mk, diamondBWPreCAmbientEquiv, diamondBWCFunEquiv]
  change
    (∑ x : WVec n d × ZVec n c × YVec n b,
        A x.2.2 x.2.1 x.1 *
          KCMap (n := n) (a := a) (b := d) (c := c) (d := b)
            (diamondBWCFunEquiv (_c := c) C) x.1 x.2.1 x.2.2) +
        ∑ x : PVec n a × WVec n d × I n × YVec n b,
          C x.1 x.2.2.2 x.2.2.1 x.2.1 *
            squareCompat
              (n := n) (a := a) (b := d) (c := c) (d := b)
              ((fun p sw z y => W p y z sw),
                (fun p w z sy => B p sy z w))
              x.1 x.2.1 x.2.2.1 x.2.2.2 =
      (∑ x : YVec n b × ZVec n c × WVec n d,
        A x.1 x.2.1 x.2.2 *
          KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
            C x.1 x.2.1 x.2.2) +
        ∑ x : PVec n a × YVec n b × I n × WVec n d,
          C x.1 x.2.1 x.2.2.1 x.2.2.2 *
            squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (B, W) x.1 x.2.1 x.2.2.1 x.2.2.2
  simp_rw [BWSymmetryInternal.swapKC,
    BWSymmetryInternal.swapCompat]
  calc
    (∑ x : WVec n d × ZVec n c × YVec n b,
        A x.2.2 x.2.1 x.1 *
          KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
            C x.2.2 x.2.1 x.1) +
        ∑ x : PVec n a × WVec n d × I n × YVec n b,
          C x.1 x.2.2.2 x.2.2.1 x.2.1 *
            squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (B, W) x.1 x.2.2.2 x.2.2.1 x.2.1 =
      _ := by
        simp only [Fintype.sum_prod_type]
        apply congrArg₂ (· + ·)
        · calc
            (∑ w, ∑ z, ∑ y,
                A y z w *
                  KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
                    C y z w) =
                ∑ z, ∑ w, ∑ y,
                  A y z w *
                    KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
                      C y z w := Finset.sum_comm
            _ = ∑ z, ∑ y, ∑ w,
                  A y z w *
                    KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
                      C y z w := by
                    apply Finset.sum_congr rfl
                    intro z _
                    rw [Finset.sum_comm]
            _ = ∑ y, ∑ z, ∑ w,
                  A y z w *
                    KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
                      C y z w := Finset.sum_comm
        · apply Finset.sum_congr rfl
          intro p _
          calc
            (∑ w, ∑ sz, ∑ y,
                C p y sz w *
                  squareCompat
                    (n := n) (a := a) (b := b) (c := c) (d := d)
                    (B, W) p y sz w) =
                ∑ sz, ∑ w, ∑ y,
                  C p y sz w *
                    squareCompat
                      (n := n) (a := a) (b := b) (c := c) (d := d)
                      (B, W) p y sz w := Finset.sum_comm
            _ = ∑ sz, ∑ y, ∑ w,
                  C p y sz w *
                    squareCompat
                      (n := n) (a := a) (b := b) (c := c) (d := d)
                      (B, W) p y sz w := by
                    apply Finset.sum_congr rfl
                    intro sz _
                    rw [Finset.sum_comm]
            _ = ∑ y, ∑ sz, ∑ w,
                  C p y sz w *
                    squareCompat
                      (n := n) (a := a) (b := b) (c := c) (d := d)
                      (B, W) p y sz w := Finset.sum_comm

theorem diamondBWSwap_source
    {n a b c d : Nat} [NeZero n]
    (x : AFun4 n b c d × BFun4 n a c d × WFun4 n a b c) :
    x ∈ DiamondPreCSource n a b c d ↔
      diamondBWPreCAmbientEquiv x ∈
        DiamondPreCSource n a d c b := by
  simp only [DiamondPreCSource, LinearMap.mem_ker]
  constructor
  · intro hx
    apply LinearMap.ext
    intro C'
    let C :=
      (diamondBWCFunEquiv
        (n := n) (a := a) (b := b) (_c := c) (d := d)).symm C'
    have hC :
        diamondBWCFunEquiv
            (n := n) (a := a) (b := b) (_c := c) (d := d) C = C' :=
      LinearEquiv.apply_symm_apply _ C'
    change
      diamondCPhaseCoeffClean
          (diamondBWPreCAmbientEquiv x).1
          (diamondBWPreCAmbientEquiv x).2.1
          (diamondBWPreCAmbientEquiv x).2.2 C' = 0
    rw [← hC, diamondBWSwap_cPhase]
    exact LinearMap.congr_fun hx C
  · intro hx
    apply LinearMap.ext
    intro C
    have h := LinearMap.congr_fun hx
      (diamondBWCFunEquiv
        (n := n) (a := a) (b := b) (_c := c) (d := d) C)
    change
      diamondCPhaseCoeffClean x.1 x.2.1 x.2.2 C = 0
    rw [← diamondBWSwap_cPhase x C]
    exact h

noncomputable def diamondBWSwapEquiv
    {n a b c d : Nat} [NeZero n] :
    DiamondPreCSource n a b c d ≃ₗ[F]
      DiamondPreCSource n a d c b where
  toFun x :=
    ⟨diamondBWPreCAmbientEquiv x.1,
      (diamondBWSwap_source x.1).mp x.2⟩
  invFun x :=
    ⟨(diamondBWPreCAmbientEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d)).symm x.1,
      (diamondBWSwap_source
        ((diamondBWPreCAmbientEquiv
          (n := n) (a := a) (b := b) (c := c) (d := d)).symm x.1)).mpr
        x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ x.1
  right_inv x := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ x.1
  map_add' x y := by
    apply Subtype.ext
    exact (diamondBWPreCAmbientEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (diamondBWPreCAmbientEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1

theorem diamondBWSwap_phase
    {n a b c d : Nat} [NeZero n]
    (x : DiamondPreCSource n a b c d) :
    diamondPreCQ (diamondBWSwapEquiv x) = diamondPreCQ x := by
  rcases x with ⟨⟨A, B, W⟩, hx⟩
  exact BWSymmetryInternal.phaseCore A B W

/-! Literal scalar mirror carriers. -/

abbrev DiamondEOOELeftAmbient (n : Nat) :=
  (CyclicCube n × CyclicCube n) × CyclicCube n

abbrev DiamondEOOERightAmbient (n : Nat) :=
  CyclicCube n × CyclicCube n

noncomputable def diamondEOOELeftConstraintMap
    {n : Nat} [NeZero n] :
    DiamondEOOELeftAmbient n →ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toFun l :=
    (cubeDiffP l.1.1,
      cubeDiffP l.1.2 + cubeDiffR l.2)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp [mul_add]

noncomputable abbrev DiamondEOOELeftSource
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEOOELeftConstraintMap (n := n))

noncomputable def diamondEOOECoeffMap
    {n : Nat} [NeZero n] :
    DiamondEOOELeftAmbient n →ₗ[F] DiamondEOOERightAmbient n where
  toFun l :=
    (cubeDiffI (l.1.1 + l.1.2) + cubeDiffK l.2,
      cubeDiffI l.1.1)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp <;> ring

noncomputable def DiamondEOOERightSource
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEOOERightAmbient n) :=
  ((LinearMap.range (cubeDiffP (n := n))).comap
      (cubeDiffJInv (n := n))).prod
    ((LinearMap.range
      (LinearMap.coprod (cubeDiffP (n := n))
        (cubeDiffR (n := n)))).comap
      (cubeDiffJInv (n := n)))

abbrev DiamondEEOOLeftAmbient (n : Nat) :=
  CyclicCube n × (CyclicCube n × CyclicCube n)

abbrev DiamondEEOORightAmbient (n : Nat) :=
  CyclicCube n × CyclicCube n

noncomputable def diamondEEOOLeftConstraintMap
    {n : Nat} [NeZero n] :
    DiamondEEOOLeftAmbient n →ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toFun l :=
    (cubeDiffR l.2.1,
      cubeDiffP l.1 + cubeDiffR l.2.2)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp [mul_add]

noncomputable abbrev DiamondEEOOLeftSource
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEEOOLeftConstraintMap (n := n))

noncomputable def diamondEEOOCoeffMap
    {n : Nat} [NeZero n] :
    DiamondEEOOLeftAmbient n →ₗ[F] DiamondEEOORightAmbient n where
  toFun l :=
    (cubeDiffI l.1 + cubeDiffK (l.2.1 + l.2.2),
      cubeDiffK l.2.1)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp <;> ring

noncomputable def DiamondEEOORightSource
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEEOORightAmbient n) :=
  ((LinearMap.range (cubeDiffR (n := n))).comap
      (cubeDiffJInv (n := n))).prod
    ((LinearMap.range
      (LinearMap.coprod (cubeDiffP (n := n))
        (cubeDiffR (n := n)))).comap
      (cubeDiffJInv (n := n)))

abbrev DiamondEEEOLeftAmbient (n : Nat) :=
  (CyclicCube n × CyclicCube n) ×
    ((CyclicCube n × CyclicCube n) ×
      (CyclicCube n × CyclicCube n))

noncomputable def diamondEEEOLeftConstraintMap
    {n : Nat} [NeZero n] :
    DiamondEEEOLeftAmbient n →ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toFun l :=
    (cubeDiffR l.2.1.1,
      cubeDiffP l.1.1 + cubeDiffR l.2.2.1)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp [mul_add]

noncomputable abbrev DiamondEEEOLeftSource
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEEEOLeftConstraintMap (n := n))

noncomputable def diamondEEEOCoeffMap
    {n : Nat} [NeZero n] :
    DiamondEEEOLeftAmbient n →ₗ[F]
      DiamondEOEERightAmbient n where
  toFun l :=
    ((cubeDiffI (l.1.1 + l.1.2) +
        cubeDiffK (l.2.1.1 + l.2.1.2 + l.2.2.1 + l.2.2.2),
      cubeDiffI l.1.1 +
        cubeDiffK (l.2.1.1 + l.2.2.1)),
     (cubeDiffK (l.2.1.1 + l.2.1.2),
      cubeDiffK l.2.1.1))
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp <;> ring

noncomputable def DiamondEEEORightSource
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEOEERightAmbient n) :=
  (((LinearMap.range (cubeDiffR (n := n))).comap
      (cubeDiffJInv (n := n))).prod ⊤).prod
    (((LinearMap.range
      (LinearMap.coprod (cubeDiffP (n := n))
        (cubeDiffR (n := n)))).comap
      (cubeDiffJInv (n := n))).prod ⊤)

namespace BWSymmetryInternal

noncomputable def restrictDual
    {V : Type} [AddCommGroup V] [Module F V]
    (S : Submodule F V) :
    Module.Dual F V →ₗ[F] Module.Dual F S where
  toFun phi := phi.comp S.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pairPhase
    {n : Nat} [NeZero n]
    (R A : CyclicCube n × CyclicCube n) : F :=
  cubeDot R.1 A.1 + cubeDot R.2 A.2

noncomputable def pairPairing
    {n : Nat} [NeZero n] :
    (CyclicCube n × CyclicCube n) →ₗ[F]
      Module.Dual F (CyclicCube n × CyclicCube n) :=
  LinearMap.mk₂ F pairPhase
    (by
      intro x y A
      simp only [pairPhase, Prod.fst_add, Prod.snd_add,
        EEOEInternal.cubeDot_add_left]
      abel)
    (by
      intro r x A
      simp only [pairPhase, Prod.smul_fst, Prod.smul_snd,
        EEOEInternal.cubeDot_smul_left, smul_eq_mul]
      ring)
    (by
      intro R x y
      simp only [pairPhase, Prod.fst_add, Prod.snd_add,
        EEOEInternal.cubeDot_add_right]
      abel)
    (by
      intro r R x
      simp only [pairPhase, Prod.smul_fst, Prod.smul_snd,
        EEOEInternal.cubeDot_smul_right, smul_eq_mul]
      ring)

end BWSymmetryInternal

noncomputable def diamondEOOECross
    {n : Nat} [NeZero n] :
    DiamondEOOELeftSource n →ₗ[F]
      Module.Dual F (DiamondEOOERightSource n) :=
  (BWSymmetryInternal.restrictDual (DiamondEOOERightSource n)).comp
    (BWSymmetryInternal.pairPairing.comp
      (diamondEOOECoeffMap.comp
        (DiamondEOOELeftSource n).subtype))

noncomputable def diamondEEOOCross
    {n : Nat} [NeZero n] :
    DiamondEEOOLeftSource n →ₗ[F]
      Module.Dual F (DiamondEEOORightSource n) :=
  (BWSymmetryInternal.restrictDual (DiamondEEOORightSource n)).comp
    (BWSymmetryInternal.pairPairing.comp
      (diamondEEOOCoeffMap.comp
        (DiamondEEOOLeftSource n).subtype))

noncomputable def diamondEEEOCross
    {n : Nat} [NeZero n] :
    DiamondEEEOLeftSource n →ₗ[F]
      Module.Dual F (DiamondEEEORightSource n) :=
  EEOEInternal.ambientPairing.compl₁₂
    (diamondEEEOCoeffMap.comp
      (DiamondEEEOLeftSource n).subtype)
    (DiamondEEEORightSource n).subtype

namespace BWSymmetryInternal

abbrev T {n : Nat} [NeZero n] :=
  EEOEInternal.swapIK (n := n)

theorem swapIK_cubeDiffI
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    T (cubeDiffI f) = cubeDiffK (T f) := by
  apply (T (n := n)).injective
  rw [EEOEInternal.swapIK_swapIK,
    EEOEInternal.swapIK_cubeDiffK,
    EEOEInternal.swapIK_swapIK]

theorem swapIK_rangeP_to_rangeR
    {n : Nat} [NeZero n] {A : CyclicCube n}
    (hA : cubeDiffJInv A ∈ LinearMap.range (cubeDiffP (n := n))) :
    cubeDiffJInv (T A) ∈ LinearMap.range (cubeDiffR (n := n)) := by
  rcases hA with ⟨X, hX⟩
  refine ⟨T X, ?_⟩
  rw [← EEOEInternal.swapIK_cubeDiffP,
    ← EEOEInternal.swapIK_cubeDiffJInv, hX]

theorem swapIK_rangeR_to_rangeP
    {n : Nat} [NeZero n] {A : CyclicCube n}
    (hA : cubeDiffJInv A ∈ LinearMap.range (cubeDiffR (n := n))) :
    cubeDiffJInv (T A) ∈ LinearMap.range (cubeDiffP (n := n)) := by
  rcases hA with ⟨X, hX⟩
  refine ⟨T X, ?_⟩
  rw [← EEOEInternal.swapIK_cubeDiffR,
    ← EEOEInternal.swapIK_cubeDiffJInv, hX]

theorem swapIK_coprod_mem
    {n : Nat} [NeZero n] {A : CyclicCube n}
    (hA : cubeDiffJInv A ∈
      LinearMap.range
        (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n)))) :
    cubeDiffJInv (T A) ∈
      LinearMap.range
        (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n))) := by
  rcases hA with ⟨X, hX⟩
  change cubeDiffP X.1 + cubeDiffR X.2 = cubeDiffJInv A at hX
  refine ⟨(T X.2, T X.1), ?_⟩
  change
    cubeDiffP (T X.2) + cubeDiffR (T X.1) =
      cubeDiffJInv (T A)
  rw [← EEOEInternal.swapIK_cubeDiffR,
    ← EEOEInternal.swapIK_cubeDiffP,
    ← EEOEInternal.swapIK_cubeDiffJInv,
    ← map_add, add_comm]
  exact congrArg T hX

noncomputable def eooeEEOOAmbientEquiv
    {n : Nat} [NeZero n] :
    DiamondEOOELeftAmbient n ≃ₗ[F] DiamondEEOOLeftAmbient n where
  toFun l := (T l.2, (T l.1.1, T l.1.2))
  invFun l := ((T l.2.1, T l.2.2), T l.1)
  left_inv l := by
    rcases l with ⟨⟨B0, B1⟩, W0⟩
    simp only [EEOEInternal.swapIK_swapIK]
  right_inv l := by
    rcases l with ⟨B0, W0, W1⟩
    simp only [EEOEInternal.swapIK_swapIK]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem eooeEEOO_constraint
    {n : Nat} [NeZero n] (l : DiamondEOOELeftAmbient n) :
    diamondEEOOLeftConstraintMap (eooeEEOOAmbientEquiv l) =
      (T (diamondEOOELeftConstraintMap l).1,
        T (diamondEOOELeftConstraintMap l).2) := by
  rcases l with ⟨⟨B0, B1⟩, W0⟩
  apply Prod.ext
  · exact (EEOEInternal.swapIK_cubeDiffP B0).symm
  · change
      cubeDiffP (T W0) + cubeDiffR (T B1) =
        T (cubeDiffP B1 + cubeDiffR W0)
    rw [← EEOEInternal.swapIK_cubeDiffR,
      ← EEOEInternal.swapIK_cubeDiffP, map_add, add_comm]

theorem eooeEEOO_coeff
    {n : Nat} [NeZero n] (l : DiamondEOOELeftAmbient n) :
    diamondEEOOCoeffMap (eooeEEOOAmbientEquiv l) =
      (T (diamondEOOECoeffMap l).1,
        T (diamondEOOECoeffMap l).2) := by
  rcases l with ⟨⟨B0, B1⟩, W0⟩
  apply Prod.ext
  · change
      cubeDiffI (T W0) + cubeDiffK (T B0 + T B1) =
        T (cubeDiffI (B0 + B1) + cubeDiffK W0)
    simp only [map_add]
    rw [← EEOEInternal.swapIK_cubeDiffK W0,
      ← swapIK_cubeDiffI B0, ← swapIK_cubeDiffI B1]
    abel
  · change cubeDiffK (T B0) = T (cubeDiffI B0)
    exact (swapIK_cubeDiffI B0).symm

noncomputable def eooeEEOORightAmbientEquiv
    {n : Nat} [NeZero n] :
    DiamondEOOERightAmbient n ≃ₗ[F] DiamondEEOORightAmbient n where
  toFun A := (T A.1, T A.2)
  invFun A := (T A.1, T A.2)
  left_inv A := by
    rcases A with ⟨A0, A1⟩
    simp only [EEOEInternal.swapIK_swapIK]
  right_inv A := by
    rcases A with ⟨A0, A1⟩
    simp only [EEOEInternal.swapIK_swapIK]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def eoeeEEEOAmbientEquiv
    {n : Nat} [NeZero n] :
    DiamondEOEELeftAmbient n ≃ₗ[F] DiamondEEEOLeftAmbient n where
  toFun l :=
    ((T l.2.1, T l.2.2),
      ((T l.1.1.1, T l.1.2.1),
        (T l.1.1.2, T l.1.2.2)))
  invFun l :=
    (((T l.2.1.1, T l.2.2.1),
      (T l.2.1.2, T l.2.2.2)),
      (T l.1.1, T l.1.2))
  left_inv l := by
    rcases l with ⟨⟨⟨B00, B01⟩, B10, B11⟩, W0, W1⟩
    simp only [EEOEInternal.swapIK_swapIK]
  right_inv l := by
    rcases l with ⟨⟨B0, B1⟩, ⟨⟨W00, W01⟩, W10, W11⟩⟩
    simp only [EEOEInternal.swapIK_swapIK]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem eoeeEEEO_constraint
    {n : Nat} [NeZero n] (l : DiamondEOEELeftAmbient n) :
    diamondEEEOLeftConstraintMap (eoeeEEEOAmbientEquiv l) =
      (T (diamondEOEELeftConstraintMap l).1,
        T (diamondEOEELeftConstraintMap l).2) := by
  rcases l with ⟨⟨⟨B00, B01⟩, B10, B11⟩, W0, W1⟩
  apply Prod.ext
  · exact (EEOEInternal.swapIK_cubeDiffP B00).symm
  · change
      cubeDiffP (T W0) + cubeDiffR (T B01) =
        T (cubeDiffP B01 + cubeDiffR W0)
    rw [← EEOEInternal.swapIK_cubeDiffR,
      ← EEOEInternal.swapIK_cubeDiffP, map_add, add_comm]

theorem eoeeEEEO_coeff
    {n : Nat} [NeZero n] (l : DiamondEOEELeftAmbient n) :
    diamondEEEOCoeffMap (eoeeEEEOAmbientEquiv l) =
      ((T (diamondEOEECoeffMap l).1.1,
          T (diamondEOEECoeffMap l).2.1),
        (T (diamondEOEECoeffMap l).1.2,
          T (diamondEOEECoeffMap l).2.2)) := by
  rcases l with ⟨⟨⟨B00, B01⟩, B10, B11⟩, W0, W1⟩
  apply Prod.ext
  · apply Prod.ext
    · change
        cubeDiffI (T W0 + T W1) +
            cubeDiffK (T B00 + T B10 + T B01 + T B11) =
          T (cubeDiffI (B00 + B01 + B10 + B11) +
            cubeDiffK (W0 + W1))
      simp only [map_add]
      rw [← EEOEInternal.swapIK_cubeDiffK W0,
        ← EEOEInternal.swapIK_cubeDiffK W1,
        ← swapIK_cubeDiffI B00, ← swapIK_cubeDiffI B01,
        ← swapIK_cubeDiffI B10, ← swapIK_cubeDiffI B11]
      abel
    · change
        cubeDiffI (T W0) + cubeDiffK (T B00 + T B01) =
          T (cubeDiffI (B00 + B01) + cubeDiffK W0)
      simp only [map_add]
      rw [← EEOEInternal.swapIK_cubeDiffK W0,
        ← swapIK_cubeDiffI B00, ← swapIK_cubeDiffI B01]
      abel
  · apply Prod.ext
    · change
        cubeDiffK (T B00 + T B10) =
          T (cubeDiffI (B00 + B10))
      simp only [map_add]
      rw [← swapIK_cubeDiffI B00, ← swapIK_cubeDiffI B10]
    · change cubeDiffK (T B00) = T (cubeDiffI B00)
      exact (swapIK_cubeDiffI B00).symm

noncomputable def eoeeEEEORightAmbientEquiv
    {n : Nat} [NeZero n] :
    DiamondEOEERightAmbient n ≃ₗ[F] DiamondEOEERightAmbient n where
  toFun A :=
    ((T A.1.1, T A.2.1),
      (T A.1.2, T A.2.2))
  invFun A :=
    ((T A.1.1, T A.2.1),
      (T A.1.2, T A.2.2))
  left_inv A := by
    rcases A with ⟨⟨A00, A01⟩, A10, A11⟩
    simp only [EEOEInternal.swapIK_swapIK]
  right_inv A := by
    rcases A with ⟨⟨A00, A01⟩, A10, A11⟩
    simp only [EEOEInternal.swapIK_swapIK]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end BWSymmetryInternal

noncomputable def diamondEOOE_EEOO_leftEquiv
    {n : Nat} [NeZero n] :
    DiamondEOOELeftSource n ≃ₗ[F] DiamondEEOOLeftSource n where
  toFun l :=
    ⟨BWSymmetryInternal.eooeEEOOAmbientEquiv l.1, by
      apply LinearMap.mem_ker.mpr
      rw [BWSymmetryInternal.eooeEEOO_constraint,
        LinearMap.mem_ker.mp l.2]
      rfl⟩
  invFun l :=
    ⟨BWSymmetryInternal.eooeEEOOAmbientEquiv.symm l.1, by
      apply LinearMap.mem_ker.mpr
      have hl := LinearMap.mem_ker.mp l.2
      have hs := BWSymmetryInternal.eooeEEOO_constraint
        (BWSymmetryInternal.eooeEEOOAmbientEquiv.symm l.1)
      rw [LinearEquiv.apply_symm_apply, hl] at hs
      have hpair := hs.symm
      apply Prod.ext
      · apply (BWSymmetryInternal.T (n := n)).injective
        simpa only [map_zero, EEOEInternal.swapIK_swapIK] using
          congrArg Prod.fst hpair
      · apply (BWSymmetryInternal.T (n := n)).injective
        simpa only [map_zero, EEOEInternal.swapIK_swapIK] using
          congrArg Prod.snd hpair⟩
  left_inv l := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ l.1
  right_inv l := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ l.1
  map_add' l m := by
    apply Subtype.ext
    rfl
  map_smul' r l := by
    apply Subtype.ext
    rfl

noncomputable def diamondEOOE_EEOO_rightEquiv
    {n : Nat} [NeZero n] :
    DiamondEOOERightSource n ≃ₗ[F] DiamondEEOORightSource n where
  toFun A :=
    ⟨BWSymmetryInternal.eooeEEOORightAmbientEquiv A.1,
      ⟨BWSymmetryInternal.swapIK_rangeP_to_rangeR A.2.1,
        BWSymmetryInternal.swapIK_coprod_mem A.2.2⟩⟩
  invFun A :=
    ⟨BWSymmetryInternal.eooeEEOORightAmbientEquiv.symm A.1,
      ⟨BWSymmetryInternal.swapIK_rangeR_to_rangeP A.2.1,
        BWSymmetryInternal.swapIK_coprod_mem A.2.2⟩⟩
  left_inv A := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ A.1
  right_inv A := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ A.1
  map_add' A C := by
    apply Subtype.ext
    rfl
  map_smul' r A := by
    apply Subtype.ext
    rfl

noncomputable def diamondEOEE_EEEO_leftEquiv
    {n : Nat} [NeZero n] :
    DiamondEOEELeftSource n ≃ₗ[F] DiamondEEEOLeftSource n where
  toFun l :=
    ⟨BWSymmetryInternal.eoeeEEEOAmbientEquiv l.1, by
      apply LinearMap.mem_ker.mpr
      rw [BWSymmetryInternal.eoeeEEEO_constraint,
        LinearMap.mem_ker.mp l.2]
      rfl⟩
  invFun l :=
    ⟨BWSymmetryInternal.eoeeEEEOAmbientEquiv.symm l.1, by
      apply LinearMap.mem_ker.mpr
      have hl := LinearMap.mem_ker.mp l.2
      have hs := BWSymmetryInternal.eoeeEEEO_constraint
        (BWSymmetryInternal.eoeeEEEOAmbientEquiv.symm l.1)
      rw [LinearEquiv.apply_symm_apply, hl] at hs
      have hpair := hs.symm
      apply Prod.ext
      · apply (BWSymmetryInternal.T (n := n)).injective
        simpa only [map_zero, EEOEInternal.swapIK_swapIK] using
          congrArg Prod.fst hpair
      · apply (BWSymmetryInternal.T (n := n)).injective
        simpa only [map_zero, EEOEInternal.swapIK_swapIK] using
          congrArg Prod.snd hpair⟩
  left_inv l := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ l.1
  right_inv l := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ l.1
  map_add' l m := by
    apply Subtype.ext
    rfl
  map_smul' r l := by
    apply Subtype.ext
    rfl

noncomputable def diamondEOEE_EEEO_rightEquiv
    {n : Nat} [NeZero n] :
    DiamondEOEERightSource n ≃ₗ[F] DiamondEEEORightSource n where
  toFun A :=
    ⟨BWSymmetryInternal.eoeeEEEORightAmbientEquiv A.1,
      ⟨⟨BWSymmetryInternal.swapIK_rangeP_to_rangeR A.2.1, trivial⟩,
        ⟨BWSymmetryInternal.swapIK_coprod_mem A.2.2, trivial⟩⟩⟩
  invFun A :=
    ⟨BWSymmetryInternal.eoeeEEEORightAmbientEquiv.symm A.1,
      ⟨BWSymmetryInternal.swapIK_rangeR_to_rangeP A.2.1.1,
        BWSymmetryInternal.swapIK_coprod_mem A.2.2.1⟩⟩
  left_inv A := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ A.1
  right_inv A := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ A.1
  map_add' A C := by
    apply Subtype.ext
    rfl
  map_smul' r A := by
    apply Subtype.ext
    rfl

theorem diamondEOOE_EEOO_phase
    {n : Nat} [NeZero n]
    (l : DiamondEOOELeftSource n) (A : DiamondEOOERightSource n) :
    diamondEEOOCross (n := n)
        (diamondEOOE_EEOO_leftEquiv (n := n) l)
        (diamondEOOE_EEOO_rightEquiv (n := n) A) =
      diamondEOOECross (n := n) l A := by
  change
    BWSymmetryInternal.pairPhase
        (diamondEEOOCoeffMap
          (BWSymmetryInternal.eooeEEOOAmbientEquiv l.1))
        (BWSymmetryInternal.eooeEEOORightAmbientEquiv A.1) =
      BWSymmetryInternal.pairPhase
        (diamondEOOECoeffMap l.1) A.1
  rw [BWSymmetryInternal.eooeEEOO_coeff]
  simp only [BWSymmetryInternal.pairPhase,
    BWSymmetryInternal.T,
    BWSymmetryInternal.eooeEEOORightAmbientEquiv,
    LinearEquiv.coe_mk]
  change
    cubeDot (EEOEInternal.swapIK (diamondEOOECoeffMap l.1).1)
        (EEOEInternal.swapIK A.1.1) +
      cubeDot (EEOEInternal.swapIK (diamondEOOECoeffMap l.1).2)
        (EEOEInternal.swapIK A.1.2) =
      cubeDot (diamondEOOECoeffMap l.1).1 A.1.1 +
        cubeDot (diamondEOOECoeffMap l.1).2 A.1.2
  rw [EEOEInternal.cubeDot_swap_both,
    EEOEInternal.cubeDot_swap_both]

set_option synthInstance.maxHeartbeats 200000 in
-- Expanding the imported EOEE dual pairing needs a larger synthesis budget.
theorem diamondEOEE_EEEO_phase
    {n : Nat} [NeZero n]
    (l : DiamondEOEELeftSource n) (A : DiamondEOEERightSource n) :
    diamondEEEOCross (n := n)
        (diamondEOEE_EEEO_leftEquiv (n := n) l)
        (diamondEOEE_EEEO_rightEquiv (n := n) A) =
      diamondEOEECross (n := n) l A := by
  change
    EEOEInternal.ambientPhase
        (diamondEEEOCoeffMap
          (BWSymmetryInternal.eoeeEEEOAmbientEquiv l.1))
        (BWSymmetryInternal.eoeeEEEORightAmbientEquiv A.1) =
      cubeDot (diamondEOEECoeffMap l.1).1.1 A.1.1.1 +
        cubeDot (diamondEOEECoeffMap l.1).1.2 A.1.1.2 +
        cubeDot (diamondEOEECoeffMap l.1).2.1 A.1.2.1 +
        cubeDot (diamondEOEECoeffMap l.1).2.2 A.1.2.2
  rw [BWSymmetryInternal.eoeeEEEO_coeff]
  simp only [EEOEInternal.ambientPhase,
    BWSymmetryInternal.T,
    BWSymmetryInternal.eoeeEEEORightAmbientEquiv,
    LinearEquiv.coe_mk]
  change
    cubeDot (EEOEInternal.swapIK (diamondEOEECoeffMap l.1).1.1)
          (EEOEInternal.swapIK A.1.1.1) +
        cubeDot (EEOEInternal.swapIK (diamondEOEECoeffMap l.1).2.1)
          (EEOEInternal.swapIK A.1.2.1) +
      cubeDot (EEOEInternal.swapIK (diamondEOEECoeffMap l.1).1.2)
          (EEOEInternal.swapIK A.1.1.2) +
        cubeDot (EEOEInternal.swapIK (diamondEOEECoeffMap l.1).2.2)
          (EEOEInternal.swapIK A.1.2.2) =
      cubeDot (diamondEOEECoeffMap l.1).1.1 A.1.1.1 +
        cubeDot (diamondEOEECoeffMap l.1).1.2 A.1.1.2 +
        cubeDot (diamondEOEECoeffMap l.1).2.1 A.1.2.1 +
        cubeDot (diamondEOEECoeffMap l.1).2.2 A.1.2.2
  rw [EEOEInternal.cubeDot_swap_both,
    EEOEInternal.cubeDot_swap_both,
    EEOEInternal.cubeDot_swap_both,
    EEOEInternal.cubeDot_swap_both]
  abel

namespace BWSymmetryInternal

section RangeTransport

variable {L R L' R' : Type}
variable [AddCommGroup L] [Module F L]
variable [AddCommGroup R] [Module F R]
variable [AddCommGroup L'] [Module F L']
variable [AddCommGroup R'] [Module F R']

noncomputable def dualTransport
    (eR : R ≃ₗ[F] R') :
    Module.Dual F R ≃ₗ[F] Module.Dual F R' where
  toFun phi := phi.comp eR.symm.toLinearMap
  invFun phi := phi.comp eR.toLinearMap
  left_inv phi := by
    apply LinearMap.ext
    intro r
    simp
  right_inv phi := by
    apply LinearMap.ext
    intro r
    simp
  map_add' phi psi := by
    apply LinearMap.ext
    intro r
    rfl
  map_smul' s phi := by
    apply LinearMap.ext
    intro r
    rfl

theorem cross_comm
    (f : L →ₗ[F] Module.Dual F R)
    (g : L' →ₗ[F] Module.Dual F R')
    (eL : L ≃ₗ[F] L') (eR : R ≃ₗ[F] R')
    (h : ∀ l r, g (eL l) (eR r) = f l r)
    (l : L) :
    g (eL l) = dualTransport eR (f l) := by
  apply LinearMap.ext
  intro r'
  let r := eR.symm r'
  have hr := h l r
  simpa [dualTransport, r] using hr

noncomputable def rangeTransportEquiv
    (f : L →ₗ[F] Module.Dual F R)
    (g : L' →ₗ[F] Module.Dual F R')
    (eL : L ≃ₗ[F] L') (eR : R ≃ₗ[F] R')
    (h : ∀ l r, g (eL l) (eR r) = f l r) :
    LinearMap.range f ≃ₗ[F] LinearMap.range g where
  toFun y :=
    ⟨dualTransport eR y.1, by
      rcases y.2 with ⟨l, hl⟩
      refine ⟨eL l, ?_⟩
      rw [← hl]
      exact cross_comm f g eL eR h l⟩
  invFun y :=
    ⟨(dualTransport eR).symm y.1, by
      rcases y.2 with ⟨l', hl⟩
      refine ⟨eL.symm l', ?_⟩
      apply (dualTransport eR).injective
      rw [LinearEquiv.apply_symm_apply]
      rw [← hl]
      exact (cross_comm f g eL eR h (eL.symm l')).symm.trans
        (congrArg g (eL.apply_symm_apply l'))⟩
  left_inv y := by
    apply Subtype.ext
    exact (dualTransport eR).symm_apply_apply y.1
  right_inv y := by
    apply Subtype.ext
    exact (dualTransport eR).apply_symm_apply y.1
  map_add' y z := by
    apply Subtype.ext
    exact map_add (dualTransport eR) y.1 z.1
  map_smul' s y := by
    apply Subtype.ext
    exact map_smul (dualTransport eR) s y.1

theorem rankTransport
    (f : L →ₗ[F] Module.Dual F R)
    (g : L' →ₗ[F] Module.Dual F R')
    (eL : L ≃ₗ[F] L') (eR : R ≃ₗ[F] R')
    (h : ∀ l r, g (eL l) (eR r) = f l r) :
    Module.finrank F (LinearMap.range g) =
      Module.finrank F (LinearMap.range f) :=
  (LinearEquiv.finrank_eq
    (rangeTransportEquiv f g eL eR h)).symm

end RangeTransport

end BWSymmetryInternal

theorem rank_EEOO_eq_EOOE
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondEEOOCross (n := n))) =
      Module.finrank F
        (LinearMap.range (diamondEOOECross (n := n))) :=
  BWSymmetryInternal.rankTransport
    (diamondEOOECross (n := n))
    (diamondEEOOCross (n := n))
    (diamondEOOE_EEOO_leftEquiv (n := n))
    (diamondEOOE_EEOO_rightEquiv (n := n))
    (diamondEOOE_EEOO_phase (n := n))

theorem rank_EEEO_eq_EOEE
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondEEEOCross (n := n))) =
      Module.finrank F
        (LinearMap.range (diamondEOEECross (n := n))) :=
  BWSymmetryInternal.rankTransport
    (diamondEOEECross (n := n))
    (diamondEEEOCross (n := n))
    (diamondEOEE_EEEO_leftEquiv (n := n))
    (diamondEOEE_EEEO_rightEquiv (n := n))
    (diamondEOEE_EEEO_phase (n := n))

end

end Core4loop.SquareDiagonal.EvenP
