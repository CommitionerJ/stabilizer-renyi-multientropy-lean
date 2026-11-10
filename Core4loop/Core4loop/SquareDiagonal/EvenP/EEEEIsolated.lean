import Core4loop.SquareDiagonal.EvenP.EOEEWBlock

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

noncomputable abbrev DiamondEEEEIsolatedWLeft (n : Nat) [NeZero n] :=
  EEOEInternal.PBlockLeft n × EEOEInternal.PBlockLeft n

noncomputable abbrev DiamondEEEEIsolatedWRight (n : Nat) [NeZero n] :=
  CyclicCube n × CyclicCube n

/-- First isolated-W component, in the literal `B_Sigma` slot. -/
noncomputable def diamondEEEEIsolatedWComponentSigma
    {n : Nat} [NeZero n] :
    EEOEInternal.PBlockLeft n →ₗ[F] Module.Dual F (CyclicCube n) :=
  diamondEOEEWKerPFreeBlock

/-- Second isolated-W component, in the sheared `B_K` slot. -/
noncomputable def diamondEEEEIsolatedWComponentK
    {n : Nat} [NeZero n] :
    EEOEInternal.PBlockLeft n →ₗ[F] Module.Dual F (CyclicCube n) :=
  diamondEOEEWKerPFreeBlock

/-- Natural EEEE isolated-W coefficient in order `(A_0,A_1)`. -/
noncomputable def diamondEEEEIsolatedWNaturalCoeff
    {n : Nat} [NeZero n] :
    DiamondEEEEIsolatedWLeft n →ₗ[F] (CyclicCube n × CyclicCube n) where
  toFun x :=
    (cubeDiffI (x.1.1 + x.2.1), cubeDiffI x.1.1)
  map_add' x y := by
    apply Prod.ext <;> simp
    abel
  map_smul' r x := by
    apply Prod.ext <;> simp

/-- Raw natural phase
`<I(B_Sigma+B_K),A_0> + <I B_Sigma,A_1>`. -/
noncomputable def diamondEEEEIsolatedWCross
    {n : Nat} [NeZero n] :
    DiamondEEEEIsolatedWLeft n →ₗ[F] Module.Dual F (DiamondEEEEIsolatedWRight n) :=
  BWSymmetryInternal.pairPairing.comp diamondEEEEIsolatedWNaturalCoeff

@[simp] private theorem diamondEEEEIsolatedWCross_apply
    {n : Nat} [NeZero n] (x : DiamondEEEEIsolatedWLeft n) (y : DiamondEEEEIsolatedWRight n) :
    diamondEEEEIsolatedWCross x y =
      cubeDot (cubeDiffI (x.1.1 + x.2.1)) y.1 +
        cubeDot (cubeDiffI x.1.1) y.2 :=
  rfl

private theorem add_self_zero
    {V : Type*} [AddCommGroup V] [Module F V] (x : V) :
    x + x = 0 :=
  (add_eq_zero_iff_eq_of_F_module x x).2 rfl

/-- Exact requested shear, preserving the component order:
`(B_Sigma,B_K) |-> (B_Sigma,B_K+B_Sigma)`. -/
noncomputable def diamondEEEEIsolatedWLeftShear
    {n : Nat} [NeZero n] :
    DiamondEEEEIsolatedWLeft n ≃ₗ[F] DiamondEEEEIsolatedWLeft n where
  toFun x := (x.1, x.2 + x.1)
  invFun x := (x.1, x.2 + x.1)
  left_inv x := by
    apply Prod.ext
    · rfl
    · change x.2 + x.1 + x.1 = x.2
      rw [add_assoc, add_self_zero, add_zero]
  right_inv x := by
    apply Prod.ext
    · rfl
    · change x.2 + x.1 + x.1 = x.2
      rw [add_assoc, add_self_zero, add_zero]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · change (x.2 + y.2) + (x.1 + y.1) =
        (x.2 + x.1) + (y.2 + y.1)
      abel
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · change r • x.2 + r • x.1 = r • (x.2 + x.1)
      rw [smul_add]

@[simp] private theorem diamondEEEEIsolatedWLeftShear_apply
    {n : Nat} [NeZero n] (x : DiamondEEEEIsolatedWLeft n) :
    diamondEEEEIsolatedWLeftShear x = (x.1, x.2 + x.1) :=
  rfl

@[simp] private theorem diamondEEEEIsolatedWLeftShear_symm_apply
    {n : Nat} [NeZero n] (x : DiamondEEEEIsolatedWLeft n) :
    (diamondEEEEIsolatedWLeftShear (n := n)).symm x = (x.1, x.2 + x.1) :=
  rfl

/-- The right-coordinate order change `(A_0,A_1) |-> (A_1,A_0)`.
This is not part of the left shear and is kept explicit. -/
noncomputable def diamondEEEEIsolatedWRightSwap
    {n : Nat} [NeZero n] :
    DiamondEEEEIsolatedWRight n ≃ₗ[F] DiamondEEEEIsolatedWRight n where
  toFun y := (y.2, y.1)
  invFun y := (y.2, y.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] private theorem diamondEEEEIsolatedWRightSwap_apply
    {n : Nat} [NeZero n] (y : DiamondEEEEIsolatedWRight n) :
    diamondEEEEIsolatedWRightSwap y = (y.2, y.1) :=
  rfl

/-- Honest direct sum of the two rank-`n(n-1)` components. -/
noncomputable def diamondEEEEIsolatedWDirectCross
    {n : Nat} [NeZero n] :
    DiamondEEEEIsolatedWLeft n →ₗ[F] Module.Dual F (DiamondEEEEIsolatedWRight n) :=
  diamondCrossProd diamondEEEEIsolatedWComponentSigma diamondEEEEIsolatedWComponentK

theorem diamondEEEEIsolatedW_phase_direct_sum
    {n : Nat} [NeZero n] (x : DiamondEEEEIsolatedWLeft n) (y : DiamondEEEEIsolatedWRight n) :
    diamondEEEEIsolatedWDirectCross
        (diamondEEEEIsolatedWLeftShear x)
        (diamondEEEEIsolatedWRightSwap y) =
      diamondEEEEIsolatedWCross x y := by
  change
    cubeDot (cubeDiffI x.1.1) y.2 +
        cubeDot (cubeDiffI (x.2.1 + x.1.1)) y.1 =
      cubeDot (cubeDiffI (x.1.1 + x.2.1)) y.1 +
        cubeDot (cubeDiffI x.1.1) y.2
  rw [add_comm x.2.1 x.1.1]
  abel

noncomputable def diamondEEEEIsolatedW_rangeEquiv
    {n : Nat} [NeZero n] :
    LinearMap.range (diamondEEEEIsolatedWCross (n := n)) ≃ₗ[F]
      LinearMap.range (diamondEEEEIsolatedWDirectCross (n := n)) :=
  BWSymmetryInternal.rangeTransportEquiv
    diamondEEEEIsolatedWCross diamondEEEEIsolatedWDirectCross
    diamondEEEEIsolatedWLeftShear diamondEEEEIsolatedWRightSwap
    (diamondEEEEIsolatedW_phase_direct_sum (n := n))

theorem rank_diamondEEEEIsolatedWComponentSigma
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.range (diamondEEEEIsolatedWComponentSigma (n := n))) =
      n * (n - 1) :=
  rank_diamondEOEEWKerPFreeBlock

theorem rank_diamondEEEEIsolatedWComponentK
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.range (diamondEEEEIsolatedWComponentK (n := n))) =
      n * (n - 1) :=
  rank_diamondEOEEWKerPFreeBlock

theorem rank_diamondEEEEIsolatedWCross
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.range (diamondEEEEIsolatedWCross (n := n))) =
      2 * n * (n - 1) := by
  calc
    Module.finrank F (LinearMap.range (diamondEEEEIsolatedWCross (n := n))) =
        Module.finrank F (LinearMap.range (diamondEEEEIsolatedWDirectCross (n := n))) :=
      LinearEquiv.finrank_eq diamondEEEEIsolatedW_rangeEquiv
    _ =
        Module.finrank F (LinearMap.range (diamondEEEEIsolatedWComponentSigma (n := n))) +
          Module.finrank F (LinearMap.range (diamondEEEEIsolatedWComponentK (n := n))) :=
      finrank_range_diamondCrossProd
        diamondEEEEIsolatedWComponentSigma
        diamondEEEEIsolatedWComponentK
    _ = 2 * n * (n - 1) := by
      rw [rank_diamondEEEEIsolatedWComponentSigma, rank_diamondEEEEIsolatedWComponentK]
      ring

/-! The isolated-Y carrier is obtained only through a typed i/k, B/W
transport square. -/

noncomputable abbrev DiamondEEEEIsolatedYLeft (n : Nat) [NeZero n] :=
  EEOEInternal.RBlockLeft n × EEOEInternal.RBlockLeft n

noncomputable abbrev DiamondEEEEIsolatedYRight (n : Nat) [NeZero n] :=
  CyclicCube n × CyclicCube n

private noncomputable def diamondEEEEIsolatedYNaturalCoeff
    {n : Nat} [NeZero n] :
    DiamondEEEEIsolatedYLeft n →ₗ[F] (CyclicCube n × CyclicCube n) where
  toFun x :=
    (cubeDiffK (x.1.1 + x.2.1), cubeDiffK x.1.1)
  map_add' x y := by
    apply Prod.ext <;> simp
    abel
  map_smul' r x := by
    apply Prod.ext <;> simp

noncomputable def diamondEEEEIsolatedYCross
    {n : Nat} [NeZero n] :
    DiamondEEEEIsolatedYLeft n →ₗ[F] Module.Dual F (DiamondEEEEIsolatedYRight n) :=
  BWSymmetryInternal.pairPairing.comp diamondEEEEIsolatedYNaturalCoeff

@[simp] private theorem diamondEEEEIsolatedYCross_apply
    {n : Nat} [NeZero n] (x : DiamondEEEEIsolatedYLeft n) (y : DiamondEEEEIsolatedYRight n) :
    diamondEEEEIsolatedYCross x y =
      cubeDot (cubeDiffK (x.1.1 + x.2.1)) y.1 +
        cubeDot (cubeDiffK x.1.1) y.2 :=
  rfl

/-- Typed source-side B/W transport. -/
noncomputable def diamondEEEEIsolatedYToWLeft
    {n : Nat} [NeZero n] :
    DiamondEEEEIsolatedYLeft n ≃ₗ[F] DiamondEEEEIsolatedWLeft n :=
  (EEOEInternal.rLeftEquivP (n := n)).prodCongr
    (EEOEInternal.rLeftEquivP (n := n))

/-- Typed right-coordinate i/k transport. -/
noncomputable def diamondEEEEIsolatedYToWRight
    {n : Nat} [NeZero n] :
    DiamondEEEEIsolatedYRight n ≃ₗ[F] DiamondEEEEIsolatedWRight n :=
  (EEOEInternal.swapIK (n := n)).prodCongr
    (EEOEInternal.swapIK (n := n))

/-- The required typed B/W phase square.  Y is not inferred from an
untyped rank equality. -/
theorem diamondEEEEIsolatedY_to_W_phase
    {n : Nat} [NeZero n] (x : DiamondEEEEIsolatedYLeft n) (y : DiamondEEEEIsolatedYRight n) :
    diamondEEEEIsolatedWCross (diamondEEEEIsolatedYToWLeft x) (diamondEEEEIsolatedYToWRight y) =
      diamondEEEEIsolatedYCross x y := by
  change
    cubeDot
        (cubeDiffI
          (EEOEInternal.swapIK x.1.1 +
            EEOEInternal.swapIK x.2.1))
        (EEOEInternal.swapIK y.1) +
      cubeDot (cubeDiffI (EEOEInternal.swapIK x.1.1))
        (EEOEInternal.swapIK y.2) =
    cubeDot (cubeDiffK (x.1.1 + x.2.1)) y.1 +
      cubeDot (cubeDiffK x.1.1) y.2
  rw [← map_add]
  rw [← EEOEInternal.swapIK_cubeDiffK (x.1.1 + x.2.1)]
  rw [← EEOEInternal.swapIK_cubeDiffK x.1.1]
  rw [EEOEInternal.cubeDot_swap_both,
    EEOEInternal.cubeDot_swap_both]

noncomputable def diamondEEEEIsolatedY_rangeEquiv
    {n : Nat} [NeZero n] :
    LinearMap.range (diamondEEEEIsolatedYCross (n := n)) ≃ₗ[F]
      LinearMap.range (diamondEEEEIsolatedWCross (n := n)) :=
  BWSymmetryInternal.rangeTransportEquiv
    diamondEEEEIsolatedYCross diamondEEEEIsolatedWCross
    diamondEEEEIsolatedYToWLeft diamondEEEEIsolatedYToWRight
    (diamondEEEEIsolatedY_to_W_phase (n := n))

theorem rank_diamondEEEEIsolatedYCross
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.range (diamondEEEEIsolatedYCross (n := n))) =
      2 * n * (n - 1) := by
  calc
    Module.finrank F (LinearMap.range (diamondEEEEIsolatedYCross (n := n))) =
        Module.finrank F (LinearMap.range (diamondEEEEIsolatedWCross (n := n))) :=
      LinearEquiv.finrank_eq diamondEEEEIsolatedY_rangeEquiv
    _ = 2 * n * (n - 1) := rank_diamondEEEEIsolatedWCross

/-! Boundary check.  At `n=2`, the local base rank is `4`; it is not
silently collapsed by any reference or gauge quotient.  A later tail
multiplicity can still be zero when a positive even block has size two. -/

example :
    Module.finrank F
        (LinearMap.range (diamondEEEEIsolatedWCross (n := 2))) = 4 := by
  rw [rank_diamondEEEEIsolatedWCross]

example :
    Module.finrank F
        (LinearMap.range (diamondEEEEIsolatedYCross (n := 2))) = 4 := by
  rw [rank_diamondEEEEIsolatedYCross]

end

end Core4loop.SquareDiagonal.EvenP
