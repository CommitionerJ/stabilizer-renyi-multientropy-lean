import Core4loop.CompleteGraph.EvenAllLarge.PassiveYZ.Diamond
import Core4loop.CompleteGraph.EvenAllLarge.PassiveYZ.Added

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveYZ

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal

noncomputable section

theorem fullIntertwine
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (yz : TotalEEEEYZTailLeft n b c)
    (q : DiamondMixedTailZero n b c (CyclicCube n × CyclicCube n))
    (A : DiamondEvenPReachableA n b c d)
    (hA : diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A =
      rightCoordinate (n := n) (b := b) (c := c) (d := d) q) :
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
        (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2
          (sectorSource (n := n) (b := b) (c := c) (d := d) yz))
        A =
      ∑ yt : DiamondEvenAxisTailIndex n b,
        ∑ zt : DiamondEvenAxisTailIndex n c,
          TotalEEEEPhase.totalEEEEYZBasePhase
            ((yz.1 yt).1 zt) ((q.1 yt).1 zt) := by
  rw [sectorBuild_eq_mixedOverlap]
  rw [addedPhaseVanishes]
  exact diamondIntertwine hn hb2 hc2 hd2 yz q A hA

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveYZ
