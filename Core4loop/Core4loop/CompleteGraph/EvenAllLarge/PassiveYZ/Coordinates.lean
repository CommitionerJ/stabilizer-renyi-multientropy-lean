import Core4loop.CompleteGraph.EvenAllLarge.DescSplitPhase

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveYZ

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEERightInternal

noncomputable section

noncomputable def aggregateSource
    {n b c d : Nat} [NeZero n] :
    TotalEEEEYZTailLeft n b c →ₗ[F]
      K4AggregateKernelEEEESource n b c d where
  toFun yz := (0, (0, (0, (0, (yz, (0, (0, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def leftCoordinate
    {n b c d : Nat} [NeZero n] :
    TotalEEEEYZTailLeft n b c →ₗ[F]
      SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d where
  toFun yz := (0, (0, (0, (0, (yz, (0, (0, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def rightCoordinate
    {n b c d : Nat} [NeZero n] :
    DiamondMixedTailZero n b c (CyclicCube n × CyclicCube n) →ₗ[F]
      TotalEEEERightReachableTarget n b c d where
  toFun q := (0, (0, (0, (0, (q, (0, (0, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem embed_aggregateSource
    {n b c d : Nat} [NeZero n]
    (yz : TotalEEEEYZTailLeft n b c) :
    k4AggregateKernelEEEESourceEmbed
        (n := n) (b := b) (c := c) (d := d)
        (aggregateSource
          (n := n) (b := b) (c := c) (d := d) yz) =
      leftCoordinate
        (n := n) (b := b) (c := c) (d := d) yz := by
  rfl

theorem coordinatePhase
    {n b c d : Nat} [NeZero n]
    (yz : TotalEEEEYZTailLeft n b c)
    (q : DiamondMixedTailZero n b c (CyclicCube n × CyclicCube n)) :
    TotalEEEEPhase.totalEEEECoordinatePhase
        (leftCoordinate
          (n := n) (b := b) (c := c) (d := d) yz)
        (rightCoordinate
          (n := n) (b := b) (c := c) (d := d) q) =
      ∑ yt : DiamondEvenAxisTailIndex n b,
        ∑ zt : DiamondEvenAxisTailIndex n c,
          TotalEEEEPhase.totalEEEEYZBasePhase
            ((yz.1 yt).1 zt) ((q.1 yt).1 zt) := by
  simp only [TotalEEEEPhase.totalEEEECoordinatePhase,
    leftCoordinate, rightCoordinate, LinearMap.coe_mk, AddHom.coe_mk,
    TotalEEEEPhase.totalEEEEYBasePhase,
    TotalEEEEPhase.totalEEEEWBasePhase,
    TotalEEEEPhase.totalEEEEWZBasePhase,
    TotalEEEEPhase.totalEEEEYWBasePhase,
    TotalEEEEPhase.totalEEEEYWZBasePhase, cubeDot,
    map_zero, Finset.sum_const_zero, zero_add, add_zero, zero_mul,
    Prod.fst_zero, Prod.snd_zero, Submodule.coe_zero, Pi.zero_apply]

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveYZ
