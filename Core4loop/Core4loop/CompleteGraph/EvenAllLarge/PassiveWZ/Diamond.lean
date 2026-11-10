import Core4loop.CompleteGraph.EvenAllLarge.PassiveWZ.BuildCoordinate
import Core4loop.CompleteGraph.EvenAllLarge.PassiveY.GenericTransport

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveWZ

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal

noncomputable section

theorem diamondIntertwine
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (wz : TotalEEEEWZTailLeft n c d)
    (q : DiamondMixedTailZero n c d (CyclicCube n × CyclicCube n))
    (A : DiamondEvenPReachableA n b c d)
    (hA : diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A =
      rightCoordinate (n := n) (b := b) (c := c) (d := d) q) :
    diamondEvenPCross (aggregateKernel hn hb2 hc2 hd2 wz).1 A =
      ∑ zt : DiamondEvenAxisTailIndex n c,
        ∑ wt : DiamondEvenAxisTailIndex n d,
          TotalEEEEPhase.totalEEEEWZBasePhase
            ((wz.1 zt).1 wt) ((q.1 zt).1 wt) :=
  @PassiveY.diamondCross_eq_of_coordinates n b c d _
    hn hb2 hc2 hd2
    (aggregateKernel hn hb2 hc2 hd2 wz).1
    A
    (leftCoordinate (n := n) (b := b) (c := c) (d := d) wz)
    (rightCoordinate (n := n) (b := b) (c := c) (d := d) q)
    (∑ zt : DiamondEvenAxisTailIndex n c,
      ∑ wt : DiamondEvenAxisTailIndex n d,
        TotalEEEEPhase.totalEEEEWZBasePhase
          ((wz.1 zt).1 wt) ((q.1 zt).1 wt))
    (aggregateKernel_leftCoordinate hn hb2 hc2 hd2 wz)
    hA
    (coordinatePhase (n := n) (b := b) (c := c) (d := d) wz q)

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveWZ
