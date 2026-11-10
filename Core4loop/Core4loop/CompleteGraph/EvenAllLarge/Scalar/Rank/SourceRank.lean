import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Rank.Gauge

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.EEEEInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

private theorem finrank_LinkedSource
    {n : Nat} [NeZero n] :
    Module.finrank F (LinkedSource n) = n ^ 3 + n := by
  change Module.finrank F (EEEEInternal.PRSource n) = n ^ 3 + n
  rw [LinearEquiv.finrank_eq
    (EEEEInternal.prSourceEquivStar (n := n))]
  exact finrank_ker_cubeStarIK

private theorem finrank_CyclicCube
    {n : Nat} [NeZero n] :
    Module.finrank F (CyclicCube n) = n ^ 3 := by
  simp [CyclicCube, Module.finrank_pi_fintype, I, ZMod.card,
    pow_succ, mul_assoc]

theorem finrank_K4AggregateEEEEScalarKernel
    {n : Nat} [NeZero n] :
    Module.finrank F (K4AggregateEEEEScalarKernel n) =
      3 * n ^ 3 + n := by
  rw [LinearEquiv.finrank_eq
    (aggregateCoordinatesEquiv (n := n))]
  simp only [K4ScalarAggregateCoordinates, Module.finrank_prod,
    finrank_LinkedSource, finrank_CyclicCube]
  ring

theorem finrank_K4BaseMixedScalarSector_add
    {n : Nat} [NeZero n] :
    Module.finrank F (K4BaseMixedScalarSector n) + 2 * n ^ 2 =
      5 * n ^ 3 + 5 * n := by
  unfold K4BaseMixedScalarSector K4AggregatePolarScalarCoordinates
  simp only [Module.finrank_prod]
  rw [finrank_K4AggregateEEEEScalarKernel,
    finrank_profile,
    finrank_K4BFreeHeadRadical,
    finrank_K4WFreeHeadRadical]
  have hpow : n ^ 2 ≤ n ^ 3 := by
    nlinarith [NeZero.pos n]
  omega

theorem finrank_K4BaseMixedScalarSector
    {n : Nat} [NeZero n] :
    Module.finrank F (K4BaseMixedScalarSector n) =
      5 * n ^ 3 - 2 * n ^ 2 + 5 * n := by
  have hadd := finrank_K4BaseMixedScalarSector_add (n := n)
  have hpow : n ^ 2 ≤ n ^ 3 := by
    nlinarith [NeZero.pos n]
  omega

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
