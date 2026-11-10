import Core4loop.CompleteGraph.EvenAllLarge.PassiveWZ.Diamond
import Core4loop.CompleteGraph.EvenAllLarge.PassiveWZ.Added

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveWZ

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal

noncomputable section

theorem fullIntertwine
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (wz : TotalEEEEWZTailLeft n c d)
    (q : DiamondMixedTailZero n c d (CyclicCube n × CyclicCube n))
    (A : DiamondEvenPReachableA n b c d)
    (hA : diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A =
      rightCoordinate (n := n) (b := b) (c := c) (d := d) q) :
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
        (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2
          (sectorSource (n := n) (b := b) (c := c) (d := d) wz))
        A =
      ∑ zt : DiamondEvenAxisTailIndex n c,
        ∑ wt : DiamondEvenAxisTailIndex n d,
          TotalEEEEPhase.totalEEEEWZBasePhase
            ((wz.1 zt).1 wt) ((q.1 zt).1 wt) := by
  rw [sectorBuild_eq_mixedOverlap]
  rw [addedPhaseVanishes]
  exact diamondIntertwine hn hb2 hc2 hd2 wz q A hA

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveWZ
