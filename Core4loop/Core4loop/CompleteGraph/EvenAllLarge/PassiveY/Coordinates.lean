import Core4loop.CompleteGraph.EvenAllLarge.DescSplitPhase

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveY

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEERightInternal

noncomputable section

noncomputable def aggregateSource
    {n b c d : Nat} [NeZero n] :
    TotalEEEEYTailLeft n b →ₗ[F]
      K4AggregateKernelEEEESource n b c d where
  toFun y := (0, (y, (0, (0, (0, (0, (0, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def leftCoordinate
    {n b c d : Nat} [NeZero n] :
    TotalEEEEYTailLeft n b →ₗ[F]
      SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d where
  toFun y := (0, (y, (0, (0, (0, (0, (0, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def rightCoordinate
    {n b c d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n b (YRightBase n) →ₗ[F]
      TotalEEEERightReachableTarget n b c d where
  toFun q := (0, (q, (0, (0, (0, (0, (0, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem embed_aggregateSource
    {n b c d : Nat} [NeZero n]
    (y : TotalEEEEYTailLeft n b) :
    k4AggregateKernelEEEESourceEmbed
        (n := n) (b := b) (c := c) (d := d)
        (aggregateSource
          (n := n) (b := b) (c := c) (d := d) y) =
      leftCoordinate
        (n := n) (b := b) (c := c) (d := d) y := by
  rfl

theorem coordinatePhase
    {n b c d : Nat} [NeZero n]
    (y : TotalEEEEYTailLeft n b)
    (q : DiamondEvenAxisValueTailZero n b (YRightBase n)) :
    TotalEEEEPhase.totalEEEECoordinatePhase
        (leftCoordinate
          (n := n) (b := b) (c := c) (d := d) y)
        (rightCoordinate
          (n := n) (b := b) (c := c) (d := d) q) =
      ∑ yt : DiamondEvenAxisTailIndex n b,
        TotalEEEEPhase.totalEEEEYBasePhase (y.1 yt) (q.1 yt) := by
  simp only [TotalEEEEPhase.totalEEEECoordinatePhase,
    leftCoordinate, rightCoordinate, LinearMap.coe_mk, AddHom.coe_mk,
    TotalEEEEPhase.totalEEEEWBasePhase,
    TotalEEEEPhase.totalEEEEYZBasePhase,
    TotalEEEEPhase.totalEEEEWZBasePhase,
    TotalEEEEPhase.totalEEEEYWBasePhase,
    TotalEEEEPhase.totalEEEEYWZBasePhase, cubeDot,
    map_zero, Finset.sum_const_zero, zero_add, add_zero, zero_mul,
    Prod.fst_zero, Prod.snd_zero, Submodule.coe_zero, Pi.zero_apply]

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveY
