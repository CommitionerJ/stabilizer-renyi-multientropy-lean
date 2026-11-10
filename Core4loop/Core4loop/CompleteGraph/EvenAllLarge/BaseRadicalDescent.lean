import Core4loop.CompleteGraph.EvenAllLarge.AggregateRank
import Core4loop.SquareDiagonal.EvenP.TotalEEEE.RightReachable

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

/-! The canonical exact sequence for the literal K4 Base-right kernel. -/

noncomputable def k4BaseRightToDiamondReachable
    {n b c d : Nat} [NeZero n] :
    K4EvenPBaseRight n b c d →ₗ[F]
      DiamondEvenPReachableA n b c d where
  toFun r :=
    ⟨r.1.1, by
      change diamondEvenPAConstraint r.1.1 ∈
        LinearMap.range
          (squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d))
      refine ⟨r.1.2, ?_⟩
      have hr := LinearMap.mem_ker.mp r.2
      rw [k4EvenPBaseRightMap_apply] at hr
      exact ((add_eq_zero_iff_eq_of_F_module _ _).mp hr).symm⟩
  map_add' r s := by
    apply Subtype.ext
    rfl
  map_smul' a r := by
    apply Subtype.ext
    rfl

theorem k4BaseRightToDiamondReachable_surjective
    {n b c d : Nat} [NeZero n] :
    Function.Surjective
      (k4BaseRightToDiamondReachable
        (n := n) (b := b) (c := c) (d := d)) := by
  intro A
  rcases A.2 with ⟨K, hK⟩
  let r : K4EvenPBaseRight n b c d :=
    ⟨(A.1, K), by
      apply LinearMap.mem_ker.mpr
      rw [k4EvenPBaseRightMap_apply, hK]
      change
        diamondEvenPAConstraint
              (n := n) (a := 1) (b := b) (c := c) (d := d) A.1 +
            diamondEvenPAConstraint
              (n := n) (a := 1) (b := b) (c := c) (d := d) A.1 = 0
      funext p y s w
      exact F_add_self _⟩
  exact ⟨r, by
    apply Subtype.ext
    rfl⟩

noncomputable def k4BaseRightKernelRead
    {n b c d : Nat} [NeZero n] :
    LinearMap.ker
        (k4BaseRightToDiamondReachable
          (n := n) (b := b) (c := c) (d := d)) →ₗ[F]
      K4EvenPLeft n b c d where
  toFun z :=
    ⟨z.1.1.2, by
      apply LinearMap.mem_ker.mpr
      have hA : z.1.1.1 = 0 := by
        have hz := LinearMap.mem_ker.mp z.2
        exact congrArg Subtype.val hz
      have hr := LinearMap.mem_ker.mp z.1.2
      rw [k4EvenPBaseRightMap_apply] at hr
      simpa [hA] using hr⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' a x := by
    apply Subtype.ext
    rfl

noncomputable def k4BaseRightKernelBuild
    {n b c d : Nat} [NeZero n] :
    K4EvenPLeft n b c d →ₗ[F]
      LinearMap.ker
        (k4BaseRightToDiamondReachable
          (n := n) (b := b) (c := c) (d := d)) where
  toFun K :=
    ⟨⟨((0 : AFun4 n b c d), K.1), by
        apply LinearMap.mem_ker.mpr
        rw [k4EvenPBaseRightMap_apply]
        simp [LinearMap.mem_ker.mp K.2]⟩,
      by
        apply LinearMap.mem_ker.mpr
        apply Subtype.ext
        rfl⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp] theorem k4BaseRightKernelRead_build
    {n b c d : Nat} [NeZero n]
    (K : K4EvenPLeft n b c d) :
    k4BaseRightKernelRead
        (k4BaseRightKernelBuild K) = K := by
  apply Subtype.ext
  simp [k4BaseRightKernelRead, k4BaseRightKernelBuild]

@[simp] theorem k4BaseRightKernelBuild_read
    {n b c d : Nat} [NeZero n]
    (z : LinearMap.ker
      (k4BaseRightToDiamondReachable
        (n := n) (b := b) (c := c) (d := d))) :
    k4BaseRightKernelBuild
        (k4BaseRightKernelRead z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have hz := LinearMap.mem_ker.mp z.2
    exact congrArg Subtype.val hz |>.symm
  · simp [k4BaseRightKernelRead, k4BaseRightKernelBuild]

noncomputable def k4BaseRightKernelEquivLeft
    {n b c d : Nat} [NeZero n] :
    LinearMap.ker
        (k4BaseRightToDiamondReachable
          (n := n) (b := b) (c := c) (d := d)) ≃ₗ[F]
      K4EvenPLeft n b c d where
  toLinearMap := k4BaseRightKernelRead
  invFun := k4BaseRightKernelBuild
  left_inv := k4BaseRightKernelBuild_read
  right_inv := k4BaseRightKernelRead_build

theorem k4BaseCross_on_rightKernel
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d)
    (K : K4EvenPLeft n b c d) :
    k4EvenPBaseCross sigma (k4BaseRightKernelBuild K).1 =
      k4EvenPGPolar sigma K := by
  change
    coeffApplyA
          (KBMap sigma.1.1 + KWMap sigma.1.2)
          (0 : AFun4 n b c d) +
        k4EvenPSlicePolar sigma.1 K.1 =
      k4EvenPSlicePolar sigma.1 K.1
  rw [coeffApplyA_eq_sum]
  simp

noncomputable abbrev K4GPolarKernel
    (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (k4EvenPGPolar (n := n) (b := b) (c := c) (d := d))

private theorem k4BaseCross_annihilates_rightKernel
    {n b c d : Nat} [NeZero n]
    (sigma : K4GPolarKernel n b c d) :
    LinearMap.ker
        (k4BaseRightToDiamondReachable
          (n := n) (b := b) (c := c) (d := d)) ≤
      LinearMap.ker (k4EvenPBaseCross sigma.1) := by
  intro r hr
  let z : LinearMap.ker
      (k4BaseRightToDiamondReachable
        (n := n) (b := b) (c := c) (d := d)) := ⟨r, hr⟩
  have hz := congrArg Subtype.val (k4BaseRightKernelBuild_read z)
  change (k4BaseRightKernelBuild (k4BaseRightKernelRead z)).1 = r at hz
  apply LinearMap.mem_ker.mpr
  rw [← hz]
  rw [k4BaseCross_on_rightKernel]
  rw [LinearMap.mem_ker.mp sigma.2]
  rfl

set_option maxHeartbeats 2000000 in
-- Quotient-lift linearity unfolds both the lifted functional and the quotient equivalence.
set_option synthInstance.maxHeartbeats 2000000 in
-- The quotient carrier exposes a deeply nested finite-dimensional module instance.
noncomputable def k4BaseDescendedCross
    {n b c d : Nat} [NeZero n] :
    K4GPolarKernel n b c d →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) where
  toFun sigma :=
    let p := k4BaseRightToDiamondReachable
      (n := n) (b := b) (c := c) (d := d)
    ((LinearMap.ker p).liftQ
        (k4EvenPBaseCross sigma.1)
        (k4BaseCross_annihilates_rightKernel sigma)).comp
      (p.quotKerEquivOfSurjective
        k4BaseRightToDiamondReachable_surjective).symm.toLinearMap
  map_add' sigma tau := by
    apply LinearMap.ext
    intro A
    let p := k4BaseRightToDiamondReachable
      (n := n) (b := b) (c := c) (d := d)
    let q := (p.quotKerEquivOfSurjective
      k4BaseRightToDiamondReachable_surjective).symm A
    change
      (LinearMap.ker p).liftQ
          (k4EvenPBaseCross (sigma + tau).1)
          (k4BaseCross_annihilates_rightKernel (sigma + tau)) q =
        (LinearMap.ker p).liftQ
            (k4EvenPBaseCross sigma.1)
            (k4BaseCross_annihilates_rightKernel sigma) q +
          (LinearMap.ker p).liftQ
            (k4EvenPBaseCross tau.1)
            (k4BaseCross_annihilates_rightKernel tau) q
    refine Quotient.inductionOn q ?_
    intro r
    change
      k4EvenPBaseCross (sigma + tau).1 r =
        k4EvenPBaseCross sigma.1 r + k4EvenPBaseCross tau.1 r
    simp
  map_smul' a sigma := by
    apply LinearMap.ext
    intro A
    let p := k4BaseRightToDiamondReachable
      (n := n) (b := b) (c := c) (d := d)
    let q := (p.quotKerEquivOfSurjective
      k4BaseRightToDiamondReachable_surjective).symm A
    change
      (LinearMap.ker p).liftQ
          (k4EvenPBaseCross (a • sigma).1)
          (k4BaseCross_annihilates_rightKernel (a • sigma)) q =
        a •
          (LinearMap.ker p).liftQ
            (k4EvenPBaseCross sigma.1)
            (k4BaseCross_annihilates_rightKernel sigma) q
    refine Quotient.inductionOn q ?_
    intro r
    change
      k4EvenPBaseCross (a • sigma).1 r =
        a • k4EvenPBaseCross sigma.1 r
    simp

theorem k4BaseDescendedCross_projection
    {n b c d : Nat} [NeZero n]
    (sigma : K4GPolarKernel n b c d)
    (r : K4EvenPBaseRight n b c d) :
    k4BaseDescendedCross sigma
        (k4BaseRightToDiamondReachable r) =
      k4EvenPBaseCross sigma.1 r := by
  change
    (LinearMap.ker
        (k4BaseRightToDiamondReachable
          (n := n) (b := b) (c := c) (d := d))).liftQ
        (k4EvenPBaseCross sigma.1)
        (k4BaseCross_annihilates_rightKernel sigma)
        (((k4BaseRightToDiamondReachable
              (n := n) (b := b) (c := c) (d := d)).quotKerEquivOfSurjective
            k4BaseRightToDiamondReachable_surjective).symm
          (k4BaseRightToDiamondReachable r)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

set_option synthInstance.maxHeartbeats 2000000 in
-- The descended kernel type requires unfolding the quotient-lifted linear map.
noncomputable def k4DescendedKernelToBaseKernel
    {n b c d : Nat} [NeZero n] :
    LinearMap.ker
        (k4BaseDescendedCross
          (n := n) (b := b) (c := c) (d := d)) →ₗ[F]
      LinearMap.ker
        (k4EvenPBaseCross
          (n := n) (b := b) (c := c) (d := d)) where
  toFun z :=
    ⟨z.1.1, by
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro r
      have hz := LinearMap.congr_fun (LinearMap.mem_ker.mp z.2)
        (k4BaseRightToDiamondReachable r)
      rw [k4BaseDescendedCross_projection] at hz
      exact hz⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' a x := by
    apply Subtype.ext
    rfl

set_option synthInstance.maxHeartbeats 2000000 in
-- The descended kernel type requires unfolding the quotient-lifted linear map.
noncomputable def k4BaseKernelToDescendedKernel
    {n b c d : Nat} [NeZero n] :
    LinearMap.ker
        (k4EvenPBaseCross
          (n := n) (b := b) (c := c) (d := d)) →ₗ[F]
      LinearMap.ker
        (k4BaseDescendedCross
          (n := n) (b := b) (c := c) (d := d)) where
  toFun z := by
    have hg :
        k4EvenPGPolar
            (n := n) (b := b) (c := c) (d := d) z.1 = 0 := by
      apply LinearMap.ext
      intro K
      have hz := LinearMap.congr_fun (LinearMap.mem_ker.mp z.2)
        (k4BaseRightKernelBuild K).1
      rw [k4BaseCross_on_rightKernel] at hz
      exact hz
    let sigma : K4GPolarKernel n b c d :=
      ⟨z.1, LinearMap.mem_ker.mpr hg⟩
    exact
      ⟨sigma, by
        apply LinearMap.mem_ker.mpr
        apply LinearMap.ext
        intro A
        rcases k4BaseRightToDiamondReachable_surjective A with ⟨r, rfl⟩
        rw [k4BaseDescendedCross_projection]
        exact LinearMap.congr_fun (LinearMap.mem_ker.mp z.2) r⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

set_option maxHeartbeats 2000000 in
-- Definitional reduction traverses both explicit kernel maps.
set_option synthInstance.maxHeartbeats 2000000 in
-- The nested kernel subtype needs an enlarged local instance-search budget.
@[simp] theorem k4DescendedKernelToBaseKernel_build
    {n b c d : Nat} [NeZero n]
    (z : LinearMap.ker
      (k4EvenPBaseCross
        (n := n) (b := b) (c := c) (d := d))) :
    k4DescendedKernelToBaseKernel
        (k4BaseKernelToDescendedKernel z) = z := by
  apply Subtype.ext
  rfl

set_option maxHeartbeats 2000000 in
-- Definitional reduction traverses both explicit kernel maps.
set_option synthInstance.maxHeartbeats 2000000 in
-- The nested kernel subtype needs an enlarged local instance-search budget.
@[simp] theorem k4BaseKernelToDescendedKernel_read
    {n b c d : Nat} [NeZero n]
    (z : LinearMap.ker
      (k4BaseDescendedCross
        (n := n) (b := b) (c := c) (d := d))) :
    k4BaseKernelToDescendedKernel
        (k4DescendedKernelToBaseKernel z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

set_option synthInstance.maxHeartbeats 2000000 in
-- Packaging the two kernel maps unfolds the quotient-lifted domain type.
noncomputable def k4BaseDescendedKernelEquiv
    {n b c d : Nat} [NeZero n] :
    LinearMap.ker
        (k4BaseDescendedCross
          (n := n) (b := b) (c := c) (d := d)) ≃ₗ[F]
      LinearMap.ker
        (k4EvenPBaseCross
          (n := n) (b := b) (c := c) (d := d)) where
  toLinearMap := k4DescendedKernelToBaseKernel
  invFun := k4BaseKernelToDescendedKernel
  left_inv := k4BaseKernelToDescendedKernel_read
  right_inv := k4DescendedKernelToBaseKernel_build

set_option synthInstance.maxHeartbeats 2000000 in
-- Rank-nullity synthesizes finite-dimensional instances for the descended kernel and range.
theorem finrank_range_k4BaseCross_eq_gPolar_add_descended
    {n b c d : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (k4EvenPBaseCross
            (n := n) (b := b) (c := c) (d := d))) =
      Module.finrank F
          (LinearMap.range
            (k4EvenPGPolar
              (n := n) (b := b) (c := c) (d := d))) +
        Module.finrank F
          (LinearMap.range
            (k4BaseDescendedCross
              (n := n) (b := b) (c := c) (d := d))) := by
  have hbase := LinearMap.finrank_range_add_finrank_ker
    (k4EvenPBaseCross (n := n) (b := b) (c := c) (d := d))
  have hg := LinearMap.finrank_range_add_finrank_ker
    (k4EvenPGPolar (n := n) (b := b) (c := c) (d := d))
  have hdesc := LinearMap.finrank_range_add_finrank_ker
    (k4BaseDescendedCross
      (n := n) (b := b) (c := c) (d := d))
  change
    Module.finrank F
          (LinearMap.range
            (k4BaseDescendedCross
              (n := n) (b := b) (c := c) (d := d))) +
        Module.finrank F
          (LinearMap.ker
            (k4BaseDescendedCross
              (n := n) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.ker
          (k4EvenPGPolar
            (n := n) (b := b) (c := c) (d := d))
          )
    at hdesc
  have hker := LinearEquiv.finrank_eq
    (k4BaseDescendedKernelEquiv
      (n := n) (b := b) (c := c) (d := d))
  have hdom :
      Module.finrank F (K4GPolarKernel n b c d) =
        Module.finrank F
          (LinearMap.ker
            (k4EvenPGPolar
              (n := n) (b := b) (c := c) (d := d))) := rfl
  omega

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
