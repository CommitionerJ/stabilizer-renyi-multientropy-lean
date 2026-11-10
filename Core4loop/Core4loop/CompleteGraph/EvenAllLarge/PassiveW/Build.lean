import Core4loop.CompleteGraph.EvenAllLarge.PassiveW.Coordinates

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveW

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal

noncomputable section

noncomputable def sectorSource
    {n b c d : Nat} [NeZero n] :
    TotalEEEEWTailLeft n d →ₗ[F]
      K4BaseMixedOverlapSectorSource n b c d where
  toFun w := (0, (0, (w, (0, (0, (0, (0, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def aggregateKernel
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEWTailLeft n d →ₗ[F]
      K4AggregateKernel n b c d hn hb2 hc2 hd2 :=
  (k4AggregateKernelEEEEBuild hn hb2 hc2 hd2).comp aggregateSource

noncomputable def mixedOverlap
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEWTailLeft n d →ₗ[F]
      K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 :=
  (LinearMap.inl F
      (K4AggregateKernel n b c d hn hb2 hc2 hd2)
      (K4AggregatePolarCoordinateTarget n c)).comp
    (aggregateKernel hn hb2 hc2 hd2)

theorem sectorBuild_eq_mixedOverlap
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (w : TotalEEEEWTailLeft n d) :
    k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2
        (sectorSource (n := n) (b := b) (c := c) (d := d) w) =
      mixedOverlap hn hb2 hc2 hd2 w := by
  rfl

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveW
