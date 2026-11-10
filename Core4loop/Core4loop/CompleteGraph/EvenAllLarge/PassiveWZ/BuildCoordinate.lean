import Core4loop.CompleteGraph.EvenAllLarge.PassiveWZ.Build

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveWZ

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal

noncomputable section

theorem aggregateKernel_leftCoordinate
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (wz : TotalEEEEWZTailLeft n c d) :
    diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
        (aggregateKernel hn hb2 hc2 hd2 wz).1 =
      leftCoordinate (n := n) (b := b) (c := c) (d := d) wz :=
  (k4AggregateKernelEEEEBuild_coordinates
    hn hb2 hc2 hd2
      (aggregateSource (n := n) (b := b) (c := c) (d := d) wz)).trans
    (embed_aggregateSource (n := n) (b := b) (c := c) (d := d) wz)

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveWZ
