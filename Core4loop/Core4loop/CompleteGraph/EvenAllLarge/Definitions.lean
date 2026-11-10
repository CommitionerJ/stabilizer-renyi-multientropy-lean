import Core4loop.CompleteGraph.EvenP.Model

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

private theorem k4BaseKKT_F_eq_zero_or_one (x : F) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem k4EvenPBaseRightMap_apply
    {n b c d : Nat} [NeZero n]
    (r : AFun4 n b c d × K4EvenPSlice n b c d) :
    k4EvenPBaseRightMap
        (n := n) (b := b) (c := c) (d := d) r =
      diamondEvenPAConstraint
          (n := n) (a := 1) (b := b) (c := c) (d := d) r.1 +
        squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d) r.2 := rfl

/-! ## Literal root and ambient Base cross -/

def k4EvenPBaseRootScalar
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d)
    (A : AFun4 n b c d) : F :=
  coeffApplyA
    (KBMap
        (n := n) (a := 1) (b := b) (c := c) (d := d) sigma.1.1 +
      KWMap
        (n := n) (a := 1) (b := b) (c := c) (d := d) sigma.1.2)
    A

noncomputable def k4EvenPBaseRoot
    {n b c d : Nat} [NeZero n] :
    K4EvenPLeft n b c d →ₗ[F]
      Module.Dual F (AFun4 n b c d) :=
  LinearMap.mk₂ F k4EvenPBaseRootScalar
    (by
      intro x y A
      simp only [k4EvenPBaseRootScalar, Submodule.coe_add,
        Prod.fst_add, Prod.snd_add, map_add]
      simp only [coeffApplyA_eq_sum, Pi.add_apply, mul_add,
        Finset.sum_add_distrib]
      abel)
    (by
      intro r x A
      rcases k4BaseKKT_F_eq_zero_or_one r with rfl | rfl
      · simp [k4EvenPBaseRootScalar, coeffApplyA_eq_sum]
      · simp)
    (by
      intro sigma A A'
      simp only [k4EvenPBaseRootScalar, coeffApplyA_eq_sum,
        Pi.add_apply, add_mul, Finset.sum_add_distrib]
      )
    (by
      intro r sigma A
      rcases k4BaseKKT_F_eq_zero_or_one r with rfl | rfl
      · simp [k4EvenPBaseRootScalar, coeffApplyA_eq_sum]
      · simp)

private noncomputable def dualProdMerge
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] :
    (Module.Dual F U × Module.Dual F V) →ₗ[F]
      Module.Dual F (U × V) where
  toFun z := LinearMap.coprod z.1 z.2
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp
    abel
  map_smul' r x := by
    apply LinearMap.ext
    intro z
    simp
    ring

def k4EvenPBaseAmbientCrossScalar
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d)
    (r : AFun4 n b c d × K4EvenPSlice n b c d) : F :=
  k4EvenPBaseRoot sigma r.1 +
    k4EvenPGPolarAmbient sigma.1 r.2

noncomputable def k4EvenPBaseAmbientCross
    {n b c d : Nat} [NeZero n] :
    K4EvenPLeft n b c d →ₗ[F]
      Module.Dual F
        (AFun4 n b c d × K4EvenPSlice n b c d) :=
  dualProdMerge.comp
    (LinearMap.prod k4EvenPBaseRoot
      (k4EvenPGPolarAmbient.comp
        (K4EvenPLeft n b c d).subtype))

theorem k4EvenPBaseAmbientCross_apply
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d)
    (r : AFun4 n b c d × K4EvenPSlice n b c d) :
    k4EvenPBaseAmbientCross sigma r =
      k4EvenPBaseRoot sigma r.1 +
        k4EvenPGPolarAmbient sigma.1 r.2 := rfl

theorem k4EvenPBaseCross_eq_ambient_restrict
    {n b c d : Nat} [NeZero n] :
    k4EvenPBaseCross (n := n) (b := b) (c := c) (d := d) =
      (LinearMap.dualMap
          (K4EvenPBaseRight n b c d).subtype).comp
        k4EvenPBaseAmbientCross := by
  apply LinearMap.ext
  intro sigma
  apply LinearMap.ext
  intro r
  rfl

/-! ## The two literal K4 multiplier equations -/

set_option maxHeartbeats 2000000 in
-- The two nested finite-dual components require a larger elaboration budget.
noncomputable def k4EvenPBaseMultiplierConstraintMap
    {n b c d : Nat} [NeZero n] :
    (K4EvenPLeft n b c d ×
        Module.Dual F (CFun4 n 1 b d)) →ₗ[F]
      (Module.Dual F (AFun4 n b c d) ×
        Module.Dual F (K4EvenPSlice n b c d)) where
  toFun z :=
    ((diamondEvenPAConstraint
          (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap z.2 -
        k4EvenPBaseRoot z.1,
      (squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap z.2 -
        k4EvenPGPolarAmbient z.1.1)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp [smul_sub]

theorem k4EvenPBaseMultiplierConstraintMap_apply
    {n b c d : Nat} [NeZero n]
    (z : K4EvenPLeft n b c d ×
      Module.Dual F (CFun4 n 1 b d)) :
    k4EvenPBaseMultiplierConstraintMap z =
      ((diamondEvenPAConstraint
            (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap z.2 -
          k4EvenPBaseRoot z.1,
        (squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap z.2 -
          k4EvenPGPolarAmbient z.1.1) := rfl

noncomputable abbrev K4EvenPBaseMultiplierSolution
    (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (k4EvenPBaseMultiplierConstraintMap
      (n := n) (b := b) (c := c) (d := d))

theorem k4EvenPBaseMultiplierSolution_mem_iff
    {n b c d : Nat} [NeZero n]
    (z : K4EvenPLeft n b c d ×
      Module.Dual F (CFun4 n 1 b d)) :
    z ∈ K4EvenPBaseMultiplierSolution n b c d ↔
      squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d) z.1.1 = 0 ∧
      (diamondEvenPAConstraint
          (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap z.2 =
        k4EvenPBaseRoot z.1 ∧
      (squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap z.2 =
        k4EvenPGPolarAmbient z.1.1 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact ⟨LinearMap.mem_ker.mp z.1.2,
      sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  · rintro ⟨_hSigma, hD, hS⟩
    apply Prod.ext
    · exact sub_eq_zero.mpr hD
    · exact sub_eq_zero.mpr hS

noncomputable def k4EvenPBaseProjection
    {n b c d : Nat} [NeZero n] :
    K4EvenPBaseMultiplierSolution n b c d →ₗ[F]
      K4EvenPLeft n b c d :=
  (LinearMap.fst F
      (K4EvenPLeft n b c d)
      (Module.Dual F (CFun4 n 1 b d))).comp
    (K4EvenPBaseMultiplierSolution n b c d).subtype

set_option synthInstance.maxHeartbeats 2000000 in
-- The nested multiplier-solution kernel requires a larger instance budget.
noncomputable abbrev K4EvenPBaseGauge
    (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (k4EvenPBaseProjection (n := n) (b := b) (c := c) (d := d))

theorem ker_k4EvenPBaseProjection_eq_gauge
    {n b c d : Nat} [NeZero n] :
    LinearMap.ker
        (k4EvenPBaseProjection
          (n := n) (b := b) (c := c) (d := d)) =
      K4EvenPBaseGauge n b c d := rfl

/-! ## The literal joint D/S dual gauge carrier -/

noncomputable def k4EvenPBaseGaugeConstraintMap
    {n b c d : Nat} [NeZero n] :
    Module.Dual F (CFun4 n 1 b d) →ₗ[F]
      (Module.Dual F (AFun4 n b c d) ×
        Module.Dual F (K4EvenPSlice n b c d)) :=
  LinearMap.prod
    (diamondEvenPAConstraint
      (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap
    (squareCompat
      (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap

noncomputable abbrev K4EvenPBaseGaugeLambda
    (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (k4EvenPBaseGaugeConstraintMap
      (n := n) (b := b) (c := c) (d := d))

theorem k4EvenPBaseGaugeLambda_mem_iff
    {n b c d : Nat} [NeZero n]
    (lambda : Module.Dual F (CFun4 n 1 b d)) :
    lambda ∈ K4EvenPBaseGaugeLambda n b c d ↔
      (diamondEvenPAConstraint
          (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap lambda = 0 ∧
      (squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap lambda = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨hD, hS⟩
    exact Prod.ext hD hS

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
