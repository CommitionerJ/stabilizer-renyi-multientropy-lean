import Core4loop.CompleteGraph.EvenAllLarge.PassiveYZ.BuildCoordinate
import Core4loop.CompleteGraph.EvenAllLarge.PassiveY.GenericTransport

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

noncomputable section

theorem diamondIntertwine
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (yz : TotalEEEEYZTailLeft n b c)
    (q : DiamondMixedTailZero n b c (CyclicCube n × CyclicCube n))
    (A : DiamondEvenPReachableA n b c d)
    (hA : diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A =
      rightCoordinate (n := n) (b := b) (c := c) (d := d) q) :
    diamondEvenPCross (aggregateKernel hn hb2 hc2 hd2 yz).1 A =
      ∑ yt : DiamondEvenAxisTailIndex n b,
        ∑ zt : DiamondEvenAxisTailIndex n c,
          TotalEEEEPhase.totalEEEEYZBasePhase
            ((yz.1 yt).1 zt) ((q.1 yt).1 zt) :=
  @PassiveY.diamondCross_eq_of_coordinates n b c d _
    hn hb2 hc2 hd2
    (aggregateKernel hn hb2 hc2 hd2 yz).1
    A
    (leftCoordinate (n := n) (b := b) (c := c) (d := d) yz)
    (rightCoordinate (n := n) (b := b) (c := c) (d := d) q)
    (∑ yt : DiamondEvenAxisTailIndex n b,
      ∑ zt : DiamondEvenAxisTailIndex n c,
        TotalEEEEPhase.totalEEEEYZBasePhase
          ((yz.1 yt).1 zt) ((q.1 yt).1 zt))
    (aggregateKernel_leftCoordinate hn hb2 hc2 hd2 yz)
    hA
    (coordinatePhase (n := n) (b := b) (c := c) (d := d) yz q)

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveYZ
