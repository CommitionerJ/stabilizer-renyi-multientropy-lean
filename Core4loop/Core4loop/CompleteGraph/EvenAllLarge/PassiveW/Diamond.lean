import Core4loop.CompleteGraph.EvenAllLarge.PassiveW.BuildCoordinate
import Core4loop.CompleteGraph.EvenAllLarge.PassiveY.GenericTransport

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveW

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEERightInternal

noncomputable section

theorem diamondIntertwine
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (w : TotalEEEEWTailLeft n d)
    (q : DiamondEvenAxisValueTailZero n d (WRightBase n))
    (A : DiamondEvenPReachableA n b c d)
    (hA : diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A =
      rightCoordinate (n := n) (b := b) (c := c) (d := d) q) :
    diamondEvenPCross (aggregateKernel hn hb2 hc2 hd2 w).1 A =
      ∑ wt : DiamondEvenAxisTailIndex n d,
        TotalEEEEPhase.totalEEEEWBasePhase (w.1 wt) (q.1 wt) :=
  @PassiveY.diamondCross_eq_of_coordinates n b c d _
    hn hb2 hc2 hd2
    (aggregateKernel hn hb2 hc2 hd2 w).1
    A
    (leftCoordinate (n := n) (b := b) (c := c) (d := d) w)
    (rightCoordinate (n := n) (b := b) (c := c) (d := d) q)
    (∑ wt : DiamondEvenAxisTailIndex n d,
      TotalEEEEPhase.totalEEEEWBasePhase (w.1 wt) (q.1 wt))
    (aggregateKernel_leftCoordinate hn hb2 hc2 hd2 w)
    hA
    (coordinatePhase (n := n) (b := b) (c := c) (d := d) w q)

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveW
