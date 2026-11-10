import Core4loop.CompleteGraph.EvenAllLarge.PureZ.Phase

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PureZ

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEERankInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

attribute [local instance] Fintype.ofFinite

private noncomputable def matrixTranspose
    {n : Nat} [NeZero n] :
    MatrixProfile n ≃ₗ[F] MatrixProfile n where
  toFun M := fun j k => M k j
  invFun M := fun j k => M k j
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def matrixCycleDiff
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] MatrixProfile n :=
  matrixTranspose.symm.toLinearMap.comp
    ((cycDiff (n := n) (Profile n)).comp
      matrixTranspose.toLinearMap)

theorem matrixCycleDiff_apply
    {n : Nat} [NeZero n]
    (M : MatrixProfile n) (j k : I n) :
    matrixCycleDiff M j k = M j k + M j (k + 1) := by
  rfl

private noncomputable def matrixCycleDiffPre
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] MatrixProfile n :=
  (cycDiff (n := n) (Profile n)).comp
    matrixTranspose.toLinearMap

private theorem range_matrixCycleDiffPre
    {n : Nat} [NeZero n] :
    LinearMap.range (matrixCycleDiffPre (n := n)) =
      LinearMap.range (cycDiff (n := n) (Profile n)) := by
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr
      (matrixTranspose (n := n)).surjective)

noncomputable def matrixCycleDiffRangeEquiv
    {n : Nat} [NeZero n] :
    LinearMap.range (cycDiff (n := n) (Profile n)) ≃ₗ[F]
      LinearMap.range (matrixCycleDiff (n := n)) :=
  (LinearEquiv.ofEq _ _ (range_matrixCycleDiffPre (n := n)).symm).trans
    (rangeCompEquivOfInjective
      (matrixCycleDiffPre (n := n))
      (matrixTranspose (n := n)).symm.toLinearMap
      (matrixTranspose (n := n)).symm.injective)

private noncomputable def matrixDiagonalEmbed
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] CyclicCube n where
  toFun M := fun i j k => M j (k + i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem matrixDiagonalEmbed_injective
    {n : Nat} [NeZero n] :
    Function.Injective (matrixDiagonalEmbed (n := n)) := by
  intro M N h
  funext j k
  have h0 := congrFun (congrFun (congrFun h 0) j) k
  simpa [matrixDiagonalEmbed] using h0

noncomputable def kappaMatrixCoeff
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] CyclicCube n :=
  matrixDiagonalEmbed.comp matrixCycleDiff

theorem kappaMatrixCoeff_apply
    {n : Nat} [NeZero n]
    (M : MatrixProfile n) (i j k : I n) :
    kappaMatrixCoeff M i j k =
      M j (k + i) + M j (k + i + 1) := by
  rfl

theorem cubeDiffI_kappaKernelBuild
    {n : Nat} [NeZero n] (M : MatrixProfile n) :
    cubeDiffI (k4KappaKernelBuild M).1 = kappaMatrixCoeff M := by
  funext i j k
  rw [EEOEInternal.cubeDiffI_apply]
  change M j (k + i) + M j (k + (i + 1)) =
    M j (k + i) + M j (k + i + 1)
  congr 2
  abel

theorem cubeDiffK_kappaFlipKernelBuild
    {n : Nat} [NeZero n] (M : MatrixProfile n) :
    cubeDiffK (k4KappaFlipKernelBuild M).1 = kappaMatrixCoeff M := by
  funext i j k
  rw [EEOEInternal.cubeDiffK_apply]
  change M j (k + i) + M j ((k + 1) + i) =
    M j (k + i) + M j (k + i + 1)
  congr 2
  abel

noncomputable def kappaMatrixCoeffRangeEquiv
    {n : Nat} [NeZero n] :
    LinearMap.range (matrixCycleDiff (n := n)) ≃ₗ[F]
      LinearMap.range (kappaMatrixCoeff (n := n)) :=
  rangeCompEquivOfInjective
    (matrixCycleDiff (n := n))
    (matrixDiagonalEmbed (n := n))
    matrixDiagonalEmbed_injective

noncomputable def kappaMatrixCross
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] Module.Dual F (CyclicCube n) :=
  EEOEInternal.cubeDotDual.comp kappaMatrixCoeff

noncomputable def kappaMatrixCrossRangeEquivCoeff
    {n : Nat} [NeZero n] :
    LinearMap.range (kappaMatrixCoeff (n := n)) ≃ₗ[F]
      LinearMap.range (kappaMatrixCross (n := n)) :=
  rangeCompEquivOfInjective
    (kappaMatrixCoeff (n := n))
    EEOEInternal.cubeDotDual
    EEOEInternal.cubeDotDual_injective

noncomputable abbrev FactorSource
    (n : Nat) [NeZero n] :=
  (CyclicCube n × CyclicCube n) ×
    (MatrixProfile n × MatrixProfile n)

private noncomputable def aggregateKernelRead
    {n : Nat} [NeZero n] :
    K4AggregateEEEEZKernel n →ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toFun x := (x.1.1.2, x.1.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def aggregateKernelBuild
    {n : Nat} [NeZero n] :
    (CyclicCube n × CyclicCube n) →ₗ[F]
      K4AggregateEEEEZKernel n where
  toFun x := ⟨((0, x.1), (0, x.2)), by rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem aggregateKernelRead_build
    {n : Nat} [NeZero n]
    (x : CyclicCube n × CyclicCube n) :
    aggregateKernelRead (aggregateKernelBuild x) = x := by
  rfl

private theorem aggregateKernelBuild_read
    {n : Nat} [NeZero n]
    (x : K4AggregateEEEEZKernel n) :
    aggregateKernelBuild (aggregateKernelRead x) = x := by
  apply Subtype.ext
  have h := LinearMap.mem_ker.mp x.2
  change (x.1.1.1, x.1.2.1) = 0 at h
  change ((0, x.1.1.2), (0, x.1.2.2)) = x.1
  have hB : x.1.1.1 = 0 := congrArg Prod.fst h
  have hW : x.1.2.1 = 0 := congrArg Prod.snd h
  apply Prod.ext
  · apply Prod.ext
    · exact hB.symm
    · rfl
  · apply Prod.ext
    · exact hW.symm
    · rfl

private noncomputable def aggregateKernelEquiv
    {n : Nat} [NeZero n] :
    K4AggregateEEEEZKernel n ≃ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toLinearMap := aggregateKernelRead
  invFun := aggregateKernelBuild
  left_inv := aggregateKernelBuild_read
  right_inv := aggregateKernelRead_build

private noncomputable def bBuildCube
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] CyclicCube n :=
  (LinearMap.ker (k4CubeKappaLinear (n := n))).subtype.comp
    k4KappaKernelBuild

private noncomputable def wBuildCube
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] CyclicCube n :=
  (LinearMap.ker (k4CubeKappaLinear (n := n)).flip).subtype.comp
    k4KappaFlipKernelBuild

private noncomputable def sourceCoordinateEquiv
    {n : Nat} [NeZero n] :
    LocalSource n ≃ₗ[F] FactorSource n :=
  (aggregateKernelEquiv (n := n)).prodCongr
    (LinearEquiv.refl F (MatrixProfile n × MatrixProfile n))

private noncomputable def factorShear
    {n : Nat} [NeZero n] :
    FactorSource n ≃ₗ[F] FactorSource n where
  toFun x :=
    ((bBuildCube x.2.1 + x.1.1,
      wBuildCube x.2.2 + x.1.2), x.2)
  invFun x :=
    ((bBuildCube x.2.1 + x.1.1,
      wBuildCube x.2.2 + x.1.2), x.2)
  left_inv x := by
    ext <;> dsimp
    all_goals rw [← add_assoc, F_add_self, zero_add]
  right_inv x := by
    ext <;> dsimp
    all_goals rw [← add_assoc, F_add_self, zero_add]
  map_add' x y := by
    ext <;> dsimp <;>
      simp only [map_add, Pi.add_apply] <;> abel
  map_smul' r x := by
    ext <;> dsimp <;>
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_add]

noncomputable def sourceShear
    {n : Nat} [NeZero n] :
    LocalSource n ≃ₗ[F] FactorSource n :=
  (sourceCoordinateEquiv (n := n)).trans
    (factorShear (n := n))

theorem sourceShear_apply
    {n : Nat} [NeZero n] (x : LocalSource n) :
    sourceShear x =
      ((((k4KappaKernelBuild x.2.1).1 + x.1.1.1.2),
        ((k4KappaFlipKernelBuild x.2.2).1 + x.1.1.2.2)),
        x.2) := by
  rfl

noncomputable abbrev ActiveRight
    (n : Nat) [NeZero n] :=
  CyclicCube n × (CyclicCube n × CyclicCube n)

noncomputable def activeRightRead
    {n : Nat} [NeZero n] :
    DiamondEEOERightAmbient n →ₗ[F] ActiveRight n where
  toFun q := (q.1.1, (q.1.2, q.2.1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def activeRightSection
    {n : Nat} [NeZero n] :
    ActiveRight n →ₗ[F] DiamondEEOERightAmbient n where
  toFun q := ((q.1, q.2.1), (q.2.2, 0))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem activeRightRead_rightSection
    {n : Nat} [NeZero n] (q : ActiveRight n) :
    activeRightRead (activeRightSection q) = q := by
  rfl

theorem activeRightRead_surjective
    {n : Nat} [NeZero n] :
    Function.Surjective (activeRightRead (n := n)) := by
  intro q
  exact ⟨activeRightSection q, activeRightRead_rightSection q⟩

noncomputable def factorCross
    {n : Nat} [NeZero n] :
    FactorSource n →ₗ[F] Module.Dual F (ActiveRight n) :=
  diamondCrossProd
    (diamondTailFreeStarCross (n := n))
    (diamondCrossProd
      (kappaMatrixCross (n := n))
      (kappaMatrixCross (n := n)))

noncomputable def factorCrossRangeEquiv
    {n : Nat} [NeZero n] :
    LinearMap.range (factorCross (n := n)) ≃ₗ[F]
      (LinearMap.range (diamondTailFreeStarCross (n := n)) ×
        (LinearMap.range (kappaMatrixCross (n := n)) ×
          LinearMap.range (kappaMatrixCross (n := n)))) :=
  (diamondCrossProdRangeEquiv
      (diamondTailFreeStarCross (n := n))
      (diamondCrossProd
        (kappaMatrixCross (n := n))
        (kappaMatrixCross (n := n)))).trans
    ((LinearEquiv.refl F
        (LinearMap.range (diamondTailFreeStarCross (n := n)))).prodCongr
      (diamondCrossProdRangeEquiv
        (kappaMatrixCross (n := n))
        (kappaMatrixCross (n := n))))

theorem factorCross_shear
    {n : Nat} [NeZero n]
    (x : LocalSource n) (q : DiamondEEOERightAmbient n) :
    factorCross (sourceShear x) (activeRightRead q) =
      localCross x q := by
  rw [localCross_apply]
  change
    cubeDot (cubeStarIK (sourceShear x).1)
          (activeRightRead q).1 +
        (cubeDot (kappaMatrixCoeff (sourceShear x).2.1)
            (activeRightRead q).2.1 +
          cubeDot (kappaMatrixCoeff (sourceShear x).2.2)
            (activeRightRead q).2.2) = _
  simp only [sourceShear_apply, activeRightRead,
    cubeStarIK, LinearMap.coprod_apply, map_add,
    EEOEInternal.cubeDot_add_left,
    cubeDiffI_kappaKernelBuild, cubeDiffK_kappaFlipKernelBuild]
  abel

theorem localCross_eq_activeRight_dual_factorCross
    {n : Nat} [NeZero n] :
    localCross (n := n) =
      (activeRightRead (n := n)).dualMap.comp
        ((factorCross (n := n)).comp
          (sourceShear (n := n)).toLinearMap) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro q
  exact (factorCross_shear x q).symm

noncomputable def localCrossRangeEquivFactorCross
    {n : Nat} [NeZero n] :
    LinearMap.range (localCross (n := n)) ≃ₗ[F]
      LinearMap.range (factorCross (n := n)) := by
  let pre := (factorCross (n := n)).comp
    (sourceShear (n := n)).toLinearMap
  have hpre : LinearMap.range pre =
      LinearMap.range (factorCross (n := n)) := by
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr
        (sourceShear (n := n)).surjective)
  let post := (activeRightRead (n := n)).dualMap
  let E := rangeCompEquivOfInjective pre post
    (LinearMap.dualMap_injective_of_surjective
      (activeRightRead_surjective (n := n)))
  have hmap : post.comp pre = localCross (n := n) := by
    exact localCross_eq_activeRight_dual_factorCross.symm
  exact
    (LinearEquiv.ofEq _ _ (congrArg LinearMap.range hmap).symm).trans
      (E.symm.trans (LinearEquiv.ofEq _ _ hpre))

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PureZ
