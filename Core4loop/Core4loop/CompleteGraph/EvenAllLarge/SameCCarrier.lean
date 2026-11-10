import Core4loop.CompleteGraph.EvenAllLarge.SameCScope

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

/-!
The coefficient form of the actual multiplier carrier.  This is a kernel,
not merely a set-valued wrapper, so it carries the exact linear structure
needed by rank-nullity.
-/

noncomputable def k4BaseSameCAmbientEquiv
    {n b c d : Nat} [NeZero n] :
    (K4EvenPLeft n b c d × Module.Dual F (CFun4 n 1 b d)) ≃ₗ[F]
      (K4EvenPLeft n b c d × CFun4 n 1 b d) :=
  (LinearEquiv.refl F (K4EvenPLeft n b c d)).prodCongr
    (k4BaseCFunDotEquiv (n := n) (b := b) (d := d)).symm

@[simp] theorem k4BaseSameCAmbientEquiv_apply
    {n b c d : Nat} [NeZero n]
    (z : K4EvenPLeft n b c d × Module.Dual F (CFun4 n 1 b d)) :
    k4BaseSameCAmbientEquiv z = (z.1, k4BaseLambdaRead z.2) := rfl

@[simp] theorem k4BaseSameCAmbientEquiv_symm_apply
    {n b c d : Nat} [NeZero n]
    (z : K4EvenPLeft n b c d × CFun4 n 1 b d) :
    (k4BaseSameCAmbientEquiv (n := n) (b := b) (c := c) (d := d)).symm z =
      (z.1, k4BaseCFunDotDual z.2) := rfl

noncomputable def k4BaseSameCConstraintMap
    {n b c d : Nat} [NeZero n] :
    (K4EvenPLeft n b c d × CFun4 n 1 b d) →ₗ[F]
      (Module.Dual F (AFun4 n b c d) ×
        Module.Dual F (K4EvenPSlice n b c d)) :=
  (k4EvenPBaseMultiplierConstraintMap
      (n := n) (b := b) (c := c) (d := d)).comp
    (k4BaseSameCAmbientEquiv
      (n := n) (b := b) (c := c) (d := d)).symm.toLinearMap

noncomputable abbrev K4BaseSameCCarrier
    (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (k4BaseSameCConstraintMap (n := n) (b := b) (c := c) (d := d))

theorem k4BaseSameCCarrier_mem_iff
    {n b c d : Nat} [NeZero n]
    (z : K4EvenPLeft n b c d × CFun4 n 1 b d) :
    z ∈ K4BaseSameCCarrier n b c d ↔ K4BaseSameCIndexed z.1 z.2 := by
  change
    (z.1, k4BaseCFunDotDual z.2) ∈
        K4EvenPBaseMultiplierSolution n b c d ↔ _
  rw [k4Base_multiplier_same_coefficient_iff]
  exact k4Base_sameCFunctional_iff_sameCIndexed z.1 z.2

/-! Explicit coefficient read/build equivalence for the full solution pair. -/

noncomputable def k4BaseMultiplierToSameC
    {n b c d : Nat} [NeZero n] :
    K4EvenPBaseMultiplierSolution n b c d →ₗ[F]
      K4BaseSameCCarrier n b c d :=
  LinearMap.codRestrict (K4BaseSameCCarrier n b c d)
    ((k4BaseSameCAmbientEquiv
      (n := n) (b := b) (c := c) (d := d)).toLinearMap.comp
      (K4EvenPBaseMultiplierSolution n b c d).subtype)
    (by
      intro z
      change
        (k4BaseSameCAmbientEquiv
          (n := n) (b := b) (c := c) (d := d)) z.1 ∈ _
      change
        k4EvenPBaseMultiplierConstraintMap
          ((k4BaseSameCAmbientEquiv
            (n := n) (b := b) (c := c) (d := d)).symm
            ((k4BaseSameCAmbientEquiv
              (n := n) (b := b) (c := c) (d := d)) z.1)) = 0
      rw [LinearEquiv.symm_apply_apply]
      exact LinearMap.mem_ker.mp z.2)

noncomputable def k4BaseSameCToMultiplier
    {n b c d : Nat} [NeZero n] :
    K4BaseSameCCarrier n b c d →ₗ[F]
      K4EvenPBaseMultiplierSolution n b c d :=
  LinearMap.codRestrict (K4EvenPBaseMultiplierSolution n b c d)
    ((k4BaseSameCAmbientEquiv
      (n := n) (b := b) (c := c) (d := d)).symm.toLinearMap.comp
      (K4BaseSameCCarrier n b c d).subtype)
    (by
      intro z
      change
        k4EvenPBaseMultiplierConstraintMap
          ((k4BaseSameCAmbientEquiv
            (n := n) (b := b) (c := c) (d := d)).symm z.1) = 0
      exact LinearMap.mem_ker.mp z.2)

@[simp] theorem k4BaseMultiplierToSameC_apply
    {n b c d : Nat} [NeZero n]
    (z : K4EvenPBaseMultiplierSolution n b c d) :
    (k4BaseMultiplierToSameC z).1 =
      (z.1.1, k4BaseLambdaRead z.1.2) := rfl

@[simp] theorem k4BaseSameCToMultiplier_apply
    {n b c d : Nat} [NeZero n]
    (z : K4BaseSameCCarrier n b c d) :
    (k4BaseSameCToMultiplier z).1 =
      (z.1.1, k4BaseCFunDotDual z.1.2) := rfl

@[simp] theorem k4BaseSameCToMultiplier_read
    {n b c d : Nat} [NeZero n]
    (z : K4EvenPBaseMultiplierSolution n b c d) :
    k4BaseSameCToMultiplier (k4BaseMultiplierToSameC z) = z := by
  apply Subtype.ext
  exact LinearEquiv.symm_apply_apply
    (k4BaseSameCAmbientEquiv
      (n := n) (b := b) (c := c) (d := d)) z.1

@[simp] theorem k4BaseMultiplierToSameC_build
    {n b c d : Nat} [NeZero n]
    (z : K4BaseSameCCarrier n b c d) :
    k4BaseMultiplierToSameC (k4BaseSameCToMultiplier z) = z := by
  apply Subtype.ext
  exact LinearEquiv.apply_symm_apply
    (k4BaseSameCAmbientEquiv
      (n := n) (b := b) (c := c) (d := d)) z.1

noncomputable def k4BaseMultiplierSameCEquiv
    {n b c d : Nat} [NeZero n] :
    K4EvenPBaseMultiplierSolution n b c d ≃ₗ[F]
      K4BaseSameCCarrier n b c d where
  toLinearMap := k4BaseMultiplierToSameC
  invFun := k4BaseSameCToMultiplier
  left_inv := k4BaseSameCToMultiplier_read
  right_inv := k4BaseMultiplierToSameC_build

/-! The exact base of the same-C carrier. -/

noncomputable abbrev K4BaseCrossKernel
    (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (k4EvenPBaseCross (n := n) (b := b) (c := c) (d := d))

noncomputable def k4BaseSameCBaseProjection
    {n b c d : Nat} [NeZero n] :
    K4BaseSameCCarrier n b c d →ₗ[F] K4BaseCrossKernel n b c d where
  toFun z :=
    ⟨z.1.1,
      (k4Base_exists_sameCIndexed_iff_mem_ker_baseCross z.1.1).mp
        ⟨z.1.2, (k4BaseSameCCarrier_mem_iff z.1).mp z.2⟩⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

theorem k4BaseSameCBaseProjection_surjective
    {n b c d : Nat} [NeZero n] :
    Function.Surjective
      (k4BaseSameCBaseProjection
        (n := n) (b := b) (c := c) (d := d)) := by
  intro sigma
  rcases
      (k4Base_exists_sameCIndexed_iff_mem_ker_baseCross sigma.1).mpr sigma.2
    with ⟨C, hC⟩
  refine ⟨⟨(sigma.1, C), (k4BaseSameCCarrier_mem_iff _).mpr hC⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem range_k4BaseSameCBaseProjection_eq_top
    {n b c d : Nat} [NeZero n] :
    LinearMap.range
        (k4BaseSameCBaseProjection
          (n := n) (b := b) (c := c) (d := d)) = ⊤ :=
  LinearMap.range_eq_top.mpr k4BaseSameCBaseProjection_surjective

/-! The joint homogeneous D/S coefficient gauge. -/

noncomputable def k4BaseSameCZeroBase
    {n b c d : Nat} [NeZero n] :
    CFun4 n 1 b d →ₗ[F]
      (K4EvenPLeft n b c d × CFun4 n 1 b d) :=
  LinearMap.inr F (K4EvenPLeft n b c d) (CFun4 n 1 b d)

noncomputable def k4BaseSameCHomogeneousConstraintMap
    {n b c d : Nat} [NeZero n] :
    CFun4 n 1 b d →ₗ[F]
      (Module.Dual F (AFun4 n b c d) ×
        Module.Dual F (K4EvenPSlice n b c d)) :=
  (k4BaseSameCConstraintMap
      (n := n) (b := b) (c := c) (d := d)).comp
    (k4BaseSameCZeroBase (n := n) (b := b) (c := c) (d := d))

noncomputable abbrev K4BaseSameCHomogeneousGauge
    (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (k4BaseSameCHomogeneousConstraintMap
      (n := n) (b := b) (c := c) (d := d))

theorem k4BaseSameCHomogeneousGauge_mem_iff
    {n b c d : Nat} [NeZero n]
    (C : CFun4 n 1 b d) :
    C ∈ K4BaseSameCHomogeneousGauge n b c d ↔
      K4BaseSameCIndexed (0 : K4EvenPLeft n b c d) C := by
  change (0, C) ∈ K4BaseSameCCarrier n b c d ↔ _
  exact k4BaseSameCCarrier_mem_iff (0, C)

noncomputable def k4BaseSameCHomogeneousToGaugeLambda
    {n b c d : Nat} [NeZero n] :
    K4BaseSameCHomogeneousGauge n b c d →ₗ[F]
      K4EvenPBaseGaugeLambda n b c d :=
  LinearMap.codRestrict (K4EvenPBaseGaugeLambda n b c d)
    ((k4BaseCFunDotDual (n := n) (b := b) (d := d)).comp
      (K4BaseSameCHomogeneousGauge n b c d).subtype)
    (by
      intro C
      apply (k4EvenPBaseGaugeLambda_mem_iff (k4BaseCFunDotDual C.1)).mpr
      have hfunctional :
          K4BaseSameCFunctional (0 : K4EvenPLeft n b c d) C.1 :=
        (k4Base_sameCFunctional_iff_sameCIndexed (0 : K4EvenPLeft n b c d) C.1).mpr
          ((k4BaseSameCHomogeneousGauge_mem_iff C.1).mp C.2)
      exact ⟨
        by simpa using
          ((k4Base_ddual_iff_DA (0 : K4EvenPLeft n b c d) C.1).mpr
            hfunctional.1),
        by simpa using
          ((k4Base_sdual_iff_SB_and_SW (0 : K4EvenPLeft n b c d) C.1).mpr
            hfunctional.2)⟩)

noncomputable def k4BaseGaugeLambdaToSameCHomogeneous
    {n b c d : Nat} [NeZero n] :
    K4EvenPBaseGaugeLambda n b c d →ₗ[F]
      K4BaseSameCHomogeneousGauge n b c d :=
  LinearMap.codRestrict (K4BaseSameCHomogeneousGauge n b c d)
    ((k4BaseLambdaRead (n := n) (b := b) (d := d)).comp
      (K4EvenPBaseGaugeLambda n b c d).subtype)
    (by
      intro lambda
      apply (k4BaseSameCHomogeneousGauge_mem_iff _).mpr
      apply (k4Base_sameCFunctional_iff_sameCIndexed
        (0 : K4EvenPLeft n b c d) (k4BaseLambdaRead lambda.1)).mp
      have h := (k4EvenPBaseGaugeLambda_mem_iff lambda.1).mp lambda.2
      refine ⟨?_, ?_⟩
      · apply (k4Base_ddual_iff_DA
          (0 : K4EvenPLeft n b c d) (k4BaseLambdaRead lambda.1)).mp
        simpa using h.1
      · apply (k4Base_sdual_iff_SB_and_SW
          (0 : K4EvenPLeft n b c d) (k4BaseLambdaRead lambda.1)).mp
        simpa using h.2)

@[simp] theorem k4BaseGaugeLambdaToSameCHomogeneous_to
    {n b c d : Nat} [NeZero n]
    (lambda : K4EvenPBaseGaugeLambda n b c d) :
    k4BaseSameCHomogeneousToGaugeLambda
        (k4BaseGaugeLambdaToSameCHomogeneous lambda) = lambda := by
  apply Subtype.ext
  exact k4BaseLambdaBuild_read lambda.1

@[simp] theorem k4BaseSameCHomogeneousToGaugeLambda_from
    {n b c d : Nat} [NeZero n]
    (C : K4BaseSameCHomogeneousGauge n b c d) :
    k4BaseGaugeLambdaToSameCHomogeneous
        (k4BaseSameCHomogeneousToGaugeLambda C) = C := by
  apply Subtype.ext
  exact k4BaseLambdaRead_build C.1

noncomputable def k4BaseSameCHomogeneousGaugeEquiv
    {n b c d : Nat} [NeZero n] :
    K4BaseSameCHomogeneousGauge n b c d ≃ₗ[F]
      K4EvenPBaseGaugeLambda n b c d where
  toLinearMap := k4BaseSameCHomogeneousToGaugeLambda
  invFun := k4BaseGaugeLambdaToSameCHomogeneous
  left_inv := k4BaseSameCHomogeneousToGaugeLambda_from
  right_inv := k4BaseGaugeLambdaToSameCHomogeneous_to

/-! The kernel of the base projection is exactly the homogeneous gauge. -/

set_option synthInstance.maxHeartbeats 2000000 in
-- Deep subtype-kernel instance synthesis.
noncomputable def k4BaseSameCProjectionGaugeRead
    {n b c d : Nat} [NeZero n] :
    LinearMap.ker
        (k4BaseSameCBaseProjection
          (n := n) (b := b) (c := c) (d := d)) →ₗ[F]
      K4BaseSameCHomogeneousGauge n b c d where
  toFun z :=
    ⟨z.1.1.2, by
      apply (k4BaseSameCHomogeneousGauge_mem_iff z.1.1.2).mpr
      have hbase := LinearMap.mem_ker.mp z.2
      change (⟨z.1.1.1, _⟩ : K4BaseCrossKernel n b c d) = 0 at hbase
      have hsigma : z.1.1.1 = 0 := congrArg Subtype.val hbase
      have hz := (k4BaseSameCCarrier_mem_iff z.1.1).mp z.1.2
      simpa [hsigma] using hz⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

set_option synthInstance.maxHeartbeats 2000000 in
-- Deep subtype-kernel instance synthesis.
noncomputable def k4BaseSameCProjectionGaugeBuild
    {n b c d : Nat} [NeZero n] :
    K4BaseSameCHomogeneousGauge n b c d →ₗ[F]
      LinearMap.ker
        (k4BaseSameCBaseProjection
          (n := n) (b := b) (c := c) (d := d)) where
  toFun C :=
    ⟨⟨((0 : K4EvenPLeft n b c d), C.1),
        (k4BaseSameCCarrier_mem_iff _).mpr
          ((k4BaseSameCHomogeneousGauge_mem_iff C.1).mp C.2)⟩,
      by
        apply LinearMap.mem_ker.mpr
        apply Subtype.ext
        rfl⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

set_option synthInstance.maxHeartbeats 2000000 in
-- Deep subtype-kernel instance synthesis.
@[simp] theorem k4BaseSameCProjectionGaugeRead_build
    {n b c d : Nat} [NeZero n]
    (C : K4BaseSameCHomogeneousGauge n b c d) :
    k4BaseSameCProjectionGaugeRead
        (k4BaseSameCProjectionGaugeBuild C) = C := by
  apply Subtype.ext
  simp [k4BaseSameCProjectionGaugeRead,
    k4BaseSameCProjectionGaugeBuild]

set_option synthInstance.maxHeartbeats 2000000 in
-- Deep subtype-kernel instance synthesis.
@[simp] theorem k4BaseSameCProjectionGaugeBuild_read
    {n b c d : Nat} [NeZero n]
    (z : LinearMap.ker
      (k4BaseSameCBaseProjection
        (n := n) (b := b) (c := c) (d := d))) :
    k4BaseSameCProjectionGaugeBuild
        (k4BaseSameCProjectionGaugeRead z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have hbase := LinearMap.mem_ker.mp z.2
    change (⟨z.1.1.1, _⟩ : K4BaseCrossKernel n b c d) = 0 at hbase
    simpa [k4BaseSameCProjectionGaugeRead,
      k4BaseSameCProjectionGaugeBuild] using
      (congrArg Subtype.val hbase).symm
  · simp [k4BaseSameCProjectionGaugeRead,
      k4BaseSameCProjectionGaugeBuild]

set_option synthInstance.maxHeartbeats 2000000 in
-- Deep subtype-kernel instance synthesis.
noncomputable def k4BaseSameCProjectionGaugeEquiv
    {n b c d : Nat} [NeZero n] :
    LinearMap.ker
        (k4BaseSameCBaseProjection
          (n := n) (b := b) (c := c) (d := d)) ≃ₗ[F]
      K4BaseSameCHomogeneousGauge n b c d where
  toLinearMap := k4BaseSameCProjectionGaugeRead
  invFun := k4BaseSameCProjectionGaugeBuild
  left_inv := k4BaseSameCProjectionGaugeBuild_read
  right_inv := k4BaseSameCProjectionGaugeRead_build

/-!
Affine-fiber law: two witnesses over the same base differ by exactly the
joint homogeneous gauge, and every homogeneous gauge translates a witness
inside its fiber.  This is the canonical factorization available without a
chosen section of the surjective base projection.
-/

theorem k4BaseSameC_difference_mem_homogeneous
    {n b c d : Nat} [NeZero n]
    (x y : K4BaseSameCCarrier n b c d)
    (hbase : x.1.1 = y.1.1) :
    x.1.2 - y.1.2 ∈ K4BaseSameCHomogeneousGauge n b c d := by
  apply (k4BaseSameCHomogeneousGauge_mem_iff _).mpr
  have hxy : x.1 - y.1 ∈ K4BaseSameCCarrier n b c d :=
    Submodule.sub_mem _ x.2 y.2
  have hz := (k4BaseSameCCarrier_mem_iff (x.1 - y.1)).mp hxy
  have hsigma : x.1.1 - y.1.1 = 0 := sub_eq_zero.mpr hbase
  simpa [hsigma] using hz

set_option synthInstance.maxHeartbeats 2000000 in
-- Deep subtype-kernel instance synthesis.
@[simp] theorem k4BaseSameCProjectionGaugeBuild_value
    {n b c d : Nat} [NeZero n]
    (g : K4BaseSameCHomogeneousGauge n b c d) :
    (k4BaseSameCProjectionGaugeBuild g).1.1 =
      ((0 : K4EvenPLeft n b c d), g.1) := by
  simp [k4BaseSameCProjectionGaugeBuild]

set_option synthInstance.maxHeartbeats 2000000 in
-- Deep subtype-kernel instance synthesis.
theorem k4BaseSameC_translate_homogeneous_base
    {n b c d : Nat} [NeZero n]
    (x : K4BaseSameCCarrier n b c d)
    (g : K4BaseSameCHomogeneousGauge n b c d) :
    k4BaseSameCBaseProjection
        (x + (k4BaseSameCProjectionGaugeBuild g).1) =
      k4BaseSameCBaseProjection x := by
  rw [map_add]
  have hg := LinearMap.mem_ker.mp
    (k4BaseSameCProjectionGaugeBuild g).2
  rw [hg, add_zero]

set_option synthInstance.maxHeartbeats 2000000 in
-- Deep subtype-kernel instance synthesis.
theorem finrank_k4BaseMultiplierSolution_eq_sameCCarrier
    {n b c d : Nat} [NeZero n] :
    Module.finrank F (K4EvenPBaseMultiplierSolution n b c d) =
      Module.finrank F (K4BaseSameCCarrier n b c d) :=
  LinearEquiv.finrank_eq k4BaseMultiplierSameCEquiv

set_option synthInstance.maxHeartbeats 2000000 in
-- Deep subtype-kernel instance synthesis.
theorem finrank_k4BaseSameCCarrier_eq_base_add_projectionKernel
    {n b c d : Nat} [NeZero n] :
    Module.finrank F (K4BaseSameCCarrier n b c d) =
      Module.finrank F (K4BaseCrossKernel n b c d) +
        Module.finrank F
          (LinearMap.ker
            (k4BaseSameCBaseProjection
              (n := n) (b := b) (c := c) (d := d))) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (k4BaseSameCBaseProjection
      (n := n) (b := b) (c := c) (d := d))
  have hrange :
      Module.finrank F
          (LinearMap.range
            (k4BaseSameCBaseProjection
              (n := n) (b := b) (c := c) (d := d))) =
        Module.finrank F (K4BaseCrossKernel n b c d) :=
    LinearEquiv.finrank_eq
      (LinearEquiv.ofTop _ range_k4BaseSameCBaseProjection_eq_top)
  rw [hrange] at h
  change
    Module.finrank F (K4BaseCrossKernel n b c d) +
        Module.finrank F
          (LinearMap.ker
            (k4BaseSameCBaseProjection
              (n := n) (b := b) (c := c) (d := d))) =
      Module.finrank F (K4BaseSameCCarrier n b c d) at h
  exact h.symm

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
