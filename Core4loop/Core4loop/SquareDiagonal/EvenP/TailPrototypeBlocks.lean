import Core4loop.SquareDiagonal.EvenP.TailPairing
import Core4loop.SquareDiagonal.EvenP.BranchRanks

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

@[simp] private theorem add_add_self_right (x y : F) :
    x + (y + x) = y := by
  rw [add_comm y x, ← add_assoc, F_add_self, zero_add]

@[simp] private theorem add_self_middle (x y : F) :
    x + y + x = y := by
  rw [add_assoc, add_add_self_right]

private noncomputable def cubeDotPostcompRangeEquiv
    {n : Nat} [NeZero n]
    {U : Type*} [AddCommGroup U] [Module F U]
    (f : U →ₗ[F] CyclicCube n) :
    LinearMap.range (EEOEInternal.cubeDotDual.comp f) ≃ₗ[F]
      LinearMap.range f := by
  let E := EEOEInternal.cubeDotEquiv (n := n)
  have hmap :
      (LinearMap.range f).map E.toLinearMap =
        LinearMap.range (EEOEInternal.cubeDotDual.comp f) := by
    simpa only [E] using
      (LinearMap.range_comp f E.toLinearMap).symm
  exact
    (E.ofSubmodules
      (LinearMap.range f)
      (LinearMap.range (EEOEInternal.cubeDotDual.comp f))
      hmap).symm

private theorem finrank_cyclicCube
    {n : Nat} [NeZero n] :
    Module.finrank F (CyclicCube n) = n ^ 3 := by
  simp [CyclicCube, Module.finrank_pi_fintype, I, ZMod.card,
    pow_succ, mul_assoc]

private theorem finrank_cubeOrbitZero
    {n : Nat} [NeZero n] :
    Module.finrank F (CubeOrbitZero n) =
      n ^ 2 * (n - 1) := by
  have hmatrix :
      Module.finrank F (MatrixProfile n) = n ^ 2 := by
    simp [MatrixProfile, Module.finrank_pi_fintype, I, ZMod.card]
    ring
  change
    Module.finrank F (ZeroSumProfileM n (MatrixProfile n)) =
      n ^ 2 * (n - 1)
  rw [finrank_ZeroSumProfileM, hmatrix]
  ring

noncomputable def diamondTailSingleICross
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) :=
  EEOEInternal.cubeDotDual.comp cubeDiffI

noncomputable def diamondTailSingleKCross
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) :=
  EEOEInternal.cubeDotDual.comp cubeDiffK

theorem rank_diamondTailSingleICross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondTailSingleICross (n := n))) =
      n ^ 2 * (n - 1) := by
  calc
    Module.finrank F
        (LinearMap.range (diamondTailSingleICross (n := n))) =
        Module.finrank F
          (LinearMap.range (cubeDiffI (n := n))) :=
      LinearEquiv.finrank_eq
        (cubeDotPostcompRangeEquiv (cubeDiffI (n := n)))
    _ = Module.finrank F (CubeOrbitZero n) := by
      rw [cubeDiff_range_eq_orbitZero]
    _ = n ^ 2 * (n - 1) := finrank_cubeOrbitZero

private theorem diamondTailSingleIK_phase
    {n : Nat} [NeZero n]
    (x y : CyclicCube n) :
    diamondTailSingleICross (EEOEInternal.swapIK x)
        (EEOEInternal.swapIK y) =
      diamondTailSingleKCross x y := by
  change
    cubeDot (cubeDiffI (EEOEInternal.swapIK x))
        (EEOEInternal.swapIK y) =
      cubeDot (cubeDiffK x) y
  rw [← EEOEInternal.swapIK_cubeDiffK,
    EEOEInternal.cubeDot_swap_both]

theorem rank_diamondTailSingleKCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondTailSingleKCross (n := n))) =
      n ^ 2 * (n - 1) := by
  have htransport :=
    BWSymmetryInternal.rankTransport
      (diamondTailSingleKCross (n := n))
      (diamondTailSingleICross (n := n))
      (EEOEInternal.swapIK (n := n))
      (EEOEInternal.swapIK (n := n))
      (diamondTailSingleIK_phase (n := n))
  exact htransport.symm.trans rank_diamondTailSingleICross

noncomputable def diamondTailFreeStarCross
    {n : Nat} [NeZero n] :
    DiamondEOOOLeftAmbient n →ₗ[F]
      Module.Dual F (CyclicCube n) :=
  EEOEInternal.cubeDotDual.comp diamondEOOOCoeffMap

theorem diamondTailFreeStarCoeff_eq_cubeStarIK
    {n : Nat} [NeZero n] :
    diamondEOOOCoeffMap (n := n) = cubeStarIK :=
  rfl

theorem rank_diamondTailFreeStarCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondTailFreeStarCross (n := n))) =
      n * (n - 1) * (n + 1) := by
  have hrange :
      Module.finrank F
          (LinearMap.range
            (diamondTailFreeStarCross (n := n))) =
        Module.finrank F
          (LinearMap.range (cubeStarIK (n := n))) := by
    exact
      LinearEquiv.finrank_eq
        (cubeDotPostcompRangeEquiv
          (diamondEOOOCoeffMap (n := n)))
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (cubeStarIK (n := n))
  rw [finrank_ker_cubeStarIK, Module.finrank_prod,
    finrank_cyclicCube] at hnull
  have hsum :
      Module.finrank F
          (LinearMap.range (cubeStarIK (n := n))) +
          (n ^ 3 + n) =
        2 * n ^ 3 := by
    calc
      Module.finrank F
            (LinearMap.range (cubeStarIK (n := n))) +
            (n ^ 3 + n) =
          n ^ 3 + n ^ 3 := hnull
      _ = 2 * n ^ 3 := by ring
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_eq_add_one, Nat.succ_sub_one] at hrange hsum ⊢
  have hpoly :
      (m + 1) * m * (m + 1 + 1) +
          ((m + 1) ^ 3 + (m + 1)) =
        2 * (m + 1) ^ 3 := by
    ring
  omega

noncomputable def diamondTailOneEvenZCross
    {n : Nat} [NeZero n] :
    DiamondEOOELeftAmbient n →ₗ[F]
      Module.Dual F (DiamondEOOERightAmbient n) :=
  BWSymmetryInternal.pairPairing.comp diamondEOOECoeffMap

set_option synthInstance.maxHeartbeats 100000 in
-- Cache the generic finite range instance before numeral specialization.
private noncomputable instance
    {n : Nat} [NeZero n] :
    Module.Free F
      (LinearMap.range (diamondTailOneEvenZCross (n := n))) :=
  inferInstance

noncomputable def diamondTailOneEvenZShear
    {n : Nat} [NeZero n] :
    DiamondEOOELeftAmbient n ≃ₗ[F]
      (DiamondEOOOLeftAmbient n × CyclicCube n) where
  toFun x := ((x.1.1 + x.1.2, x.2), x.1.1)
  invFun x := ((x.2, x.1.1 + x.2), x.1.2)
  left_inv x := by
    ext <;> simp
  right_inv x := by
    ext <;> simp
  map_add' x y := by
    ext <;> simp
    all_goals abel
  map_smul' r x := by
    ext <;> simp

theorem diamondTailOneEvenZCoeff_shear
    {n : Nat} [NeZero n]
    (x : DiamondEOOOLeftAmbient n × CyclicCube n) :
    diamondEOOECoeffMap
        ((diamondTailOneEvenZShear (n := n)).symm x) =
      (cubeStarIK x.1, cubeDiffI x.2) := by
  ext <;>
    simp [diamondTailOneEvenZShear, diamondEOOECoeffMap,
      cubeStarIK]

private noncomputable def diamondTailOneEvenZBlockCoeff
    {n : Nat} [NeZero n] :
    (DiamondEOOOLeftAmbient n × CyclicCube n) →ₗ[F]
      DiamondEOOERightAmbient n :=
  (cubeStarIK (n := n)).prodMap (cubeDiffI (n := n))

private noncomputable def diamondTailOneEvenZBlockCross
    {n : Nat} [NeZero n] :
    (DiamondEOOOLeftAmbient n × CyclicCube n) →ₗ[F]
      Module.Dual F (DiamondEOOERightAmbient n) :=
  BWSymmetryInternal.pairPairing.comp
    diamondTailOneEvenZBlockCoeff

private theorem diamondTailOneEvenZBlockCross_eq_prod
    {n : Nat} [NeZero n] :
    diamondTailOneEvenZBlockCross (n := n) =
      diamondCrossProd
        (diamondTailFreeStarCross (n := n))
        (diamondTailSingleICross (n := n)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

private theorem diamondTailOneEvenZ_cross_shear
    {n : Nat} [NeZero n]
    (x : DiamondEOOELeftAmbient n)
    (y : DiamondEOOERightAmbient n) :
    diamondTailOneEvenZBlockCross
        (diamondTailOneEvenZShear x) y =
      diamondTailOneEvenZCross x y := by
  rfl

theorem rank_diamondTailOneEvenZCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondTailOneEvenZCross (n := n))) =
      n * (n - 1) * (2 * n + 1) := by
  have htransport :=
    BWSymmetryInternal.rankTransport
      (diamondTailOneEvenZCross (n := n))
      (diamondTailOneEvenZBlockCross (n := n))
      (diamondTailOneEvenZShear (n := n))
      (LinearEquiv.refl F (DiamondEOOERightAmbient n))
      (diamondTailOneEvenZ_cross_shear (n := n))
  have hprod :
      Module.finrank F
          (LinearMap.range
            (diamondTailOneEvenZBlockCross (n := n))) =
        n * (n - 1) * (n + 1) +
          n ^ 2 * (n - 1) := by
    rw [diamondTailOneEvenZBlockCross_eq_prod,
      finrank_range_diamondCrossProd,
      rank_diamondTailFreeStarCross,
      rank_diamondTailSingleICross]
  calc
    Module.finrank F
        (LinearMap.range
          (diamondTailOneEvenZCross (n := n))) =
        Module.finrank F
          (LinearMap.range
            (diamondTailOneEvenZBlockCross (n := n))) :=
      htransport.symm
    _ = n * (n - 1) * (n + 1) +
          n ^ 2 * (n - 1) := hprod
    _ = n * (n - 1) * (2 * n + 1) := by
      ring

noncomputable def diamondTailAllEvenZCross
    {n : Nat} [NeZero n] :
    DiamondEEOELeftAmbient n →ₗ[F]
      Module.Dual F (DiamondEEOERightAmbient n) :=
  EEOEInternal.ambientPairing.comp diamondEEOECoeffMap

set_option synthInstance.maxHeartbeats 100000 in
-- Cache the generic finite range instance before numeral specialization.
private noncomputable instance
    {n : Nat} [NeZero n] :
    Module.Free F
      (LinearMap.range (diamondTailAllEvenZCross (n := n))) :=
  inferInstance

noncomputable def diamondTailAllEvenZShear
    {n : Nat} [NeZero n] :
    DiamondEEOELeftAmbient n ≃ₗ[F]
      (DiamondEOOOLeftAmbient n ×
        (CyclicCube n × CyclicCube n)) where
  toFun x :=
    ((x.1.1 + x.1.2, x.2.1 + x.2.2), (x.1.1, x.2.1))
  invFun x :=
    ((x.2.1, x.1.1 + x.2.1),
      (x.2.2, x.1.2 + x.2.2))
  left_inv x := by
    ext <;> simp
  right_inv x := by
    ext <;> simp
  map_add' x y := by
    ext <;> simp
    all_goals abel
  map_smul' r x := by
    ext <;> simp

theorem diamondTailAllEvenZCoeff_shear
    {n : Nat} [NeZero n]
    (x : DiamondEOOOLeftAmbient n ×
      (CyclicCube n × CyclicCube n)) :
    diamondEEOECoeffMap
        ((diamondTailAllEvenZShear (n := n)).symm x) =
      ((cubeStarIK x.1, cubeDiffI x.2.1),
        (cubeDiffK x.2.2, 0)) := by
  ext <;>
    simp [diamondTailAllEvenZShear, diamondEEOECoeffMap,
      cubeStarIK]

private noncomputable def diamondTailAllEvenZAssoc
    {n : Nat} [NeZero n] :
    (DiamondEOOOLeftAmbient n ×
        (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      ((DiamondEOOOLeftAmbient n × CyclicCube n) ×
        CyclicCube n) where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun x := (x.1.1, (x.1.2, x.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def diamondTailKZeroCoeff
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] (CyclicCube n × CyclicCube n) :=
  (cubeDiffK (n := n)).prod
    (0 : CyclicCube n →ₗ[F] CyclicCube n)

private noncomputable def diamondTailKZeroCross
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F]
      Module.Dual F (CyclicCube n × CyclicCube n) :=
  (Module.dualProdDualEquivDual F
      (CyclicCube n) (CyclicCube n)).toLinearMap.comp
    ((diamondTailSingleKCross (n := n)).prod
      (0 : CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n)))

private theorem diamondTailKZeroCross_ker
    {n : Nat} [NeZero n] :
    LinearMap.ker (diamondTailKZeroCross (n := n)) =
      LinearMap.ker (diamondTailSingleKCross (n := n)) := by
  apply le_antisymm
  · intro x hx
    apply LinearMap.mem_ker.mpr
    have hz := LinearMap.mem_ker.mp hx
    change
      (Module.dualProdDualEquivDual F
          (CyclicCube n) (CyclicCube n))
          (diamondTailSingleKCross x, 0) = 0 at hz
    have hpair :
        (diamondTailSingleKCross x,
            (0 : Module.Dual F (CyclicCube n))) = 0 :=
      (Module.dualProdDualEquivDual F
        (CyclicCube n) (CyclicCube n)).injective
        (hz.trans
          (map_zero
            (Module.dualProdDualEquivDual F
              (CyclicCube n) (CyclicCube n))).symm)
    exact congrArg Prod.fst hpair
  · intro x hx
    apply LinearMap.mem_ker.mpr
    have hz := LinearMap.mem_ker.mp hx
    change
      (Module.dualProdDualEquivDual F
          (CyclicCube n) (CyclicCube n))
          (diamondTailSingleKCross x, 0) = 0
    rw [hz]
    apply LinearMap.ext
    intro y
    rfl

private theorem rank_diamondTailKZeroCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondTailKZeroCross (n := n))) =
      n ^ 2 * (n - 1) := by
  have hzero :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondTailKZeroCross (n := n))
  have hsingle :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondTailSingleKCross (n := n))
  rw [diamondTailKZeroCross_ker] at hzero
  have heq :
      Module.finrank F
          (LinearMap.range
            (diamondTailKZeroCross (n := n))) =
        Module.finrank F
          (LinearMap.range
            (diamondTailSingleKCross (n := n))) := by
    omega
  exact heq.trans rank_diamondTailSingleKCross

private noncomputable def diamondTailAllEvenZBlockCoeff
    {n : Nat} [NeZero n] :
    ((DiamondEOOOLeftAmbient n × CyclicCube n) ×
        CyclicCube n) →ₗ[F]
      DiamondEEOERightAmbient n :=
  ((cubeStarIK (n := n)).prodMap (cubeDiffI (n := n))).prodMap
    diamondTailKZeroCoeff

private noncomputable def diamondTailAllEvenZBlockCross
    {n : Nat} [NeZero n] :
    ((DiamondEOOOLeftAmbient n × CyclicCube n) ×
        CyclicCube n) →ₗ[F]
      Module.Dual F (DiamondEEOERightAmbient n) :=
  EEOEInternal.ambientPairing.comp
    diamondTailAllEvenZBlockCoeff

private theorem diamondTailAllEvenZBlockCross_eq_prod
    {n : Nat} [NeZero n] :
    diamondTailAllEvenZBlockCross (n := n) =
      diamondCrossProd
        (diamondCrossProd
          (diamondTailFreeStarCross (n := n))
          (diamondTailSingleICross (n := n)))
        (diamondTailKZeroCross (n := n)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp [diamondTailAllEvenZBlockCross,
    diamondTailAllEvenZBlockCoeff, diamondTailKZeroCoeff,
    diamondTailKZeroCross, diamondCrossProd,
    diamondTailFreeStarCross, diamondTailSingleICross,
    diamondTailSingleKCross, diamondEOOOCoeffMap,
    cubeStarIK, EEOEInternal.ambientPairing,
    EEOEInternal.ambientPhase,
    EEOEInternal.cubeDotDual, cubeDot]

private noncomputable def diamondTailAllEvenZBlockShear
    {n : Nat} [NeZero n] :
    DiamondEEOELeftAmbient n ≃ₗ[F]
      ((DiamondEOOOLeftAmbient n × CyclicCube n) ×
        CyclicCube n) :=
  (diamondTailAllEvenZShear (n := n)).trans
    (diamondTailAllEvenZAssoc (n := n))

private theorem diamondTailAllEvenZ_cross_shear
    {n : Nat} [NeZero n]
    (x : DiamondEEOELeftAmbient n)
    (y : DiamondEEOERightAmbient n) :
    diamondTailAllEvenZBlockCross
        (diamondTailAllEvenZBlockShear x) y =
      diamondTailAllEvenZCross x y := by
  rfl

theorem rank_diamondTailAllEvenZCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondTailAllEvenZCross (n := n))) =
      (n - 1) * (3 * n ^ 2 + n) := by
  have htransport :=
    BWSymmetryInternal.rankTransport
      (diamondTailAllEvenZCross (n := n))
      (diamondTailAllEvenZBlockCross (n := n))
      (diamondTailAllEvenZBlockShear (n := n))
      (LinearEquiv.refl F (DiamondEEOERightAmbient n))
      (diamondTailAllEvenZ_cross_shear (n := n))
  have hprod :
      Module.finrank F
          (LinearMap.range
            (diamondTailAllEvenZBlockCross (n := n))) =
        (n * (n - 1) * (n + 1) +
            n ^ 2 * (n - 1)) +
          n ^ 2 * (n - 1) := by
    rw [diamondTailAllEvenZBlockCross_eq_prod,
      finrank_range_diamondCrossProd,
      finrank_range_diamondCrossProd,
      rank_diamondTailFreeStarCross,
      rank_diamondTailSingleICross,
      rank_diamondTailKZeroCross]
  calc
    Module.finrank F
        (LinearMap.range
          (diamondTailAllEvenZCross (n := n))) =
        Module.finrank F
          (LinearMap.range
            (diamondTailAllEvenZBlockCross (n := n))) :=
      htransport.symm
    _ = (n * (n - 1) * (n + 1) +
            n ^ 2 * (n - 1)) +
          n ^ 2 * (n - 1) := hprod
    _ = (n - 1) * (3 * n ^ 2 + n) := by
      ring

noncomputable abbrev diamondTailMixedYZCross
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) :=
  diamondTailSingleKCross

noncomputable abbrev diamondTailMixedWZCross
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) :=
  diamondTailSingleICross

theorem rank_diamondTailMixedYZCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondTailMixedYZCross (n := n))) =
      n ^ 2 * (n - 1) :=
  rank_diamondTailSingleKCross

theorem rank_diamondTailMixedWZCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondTailMixedWZCross (n := n))) =
      n ^ 2 * (n - 1) :=
  rank_diamondTailSingleICross

end

end Core4loop.SquareDiagonal.EvenP
