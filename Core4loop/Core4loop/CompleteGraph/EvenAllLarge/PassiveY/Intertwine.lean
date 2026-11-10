import Core4loop.CompleteGraph.EvenAllLarge.PassiveY.Diamond
import Core4loop.CompleteGraph.EvenAllLarge.PassiveY.Added

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveY

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEERightInternal

noncomputable section

theorem fullIntertwine
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (y : TotalEEEEYTailLeft n b)
    (q : DiamondEvenAxisValueTailZero n b (YRightBase n))
    (A : DiamondEvenPReachableA n b c d)
    (hA : diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A =
      rightCoordinate (n := n) (b := b) (c := c) (d := d) q) :
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
        (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2
          (sectorSource (n := n) (b := b) (c := c) (d := d) y))
        A =
      ∑ yt : DiamondEvenAxisTailIndex n b,
        TotalEEEEPhase.totalEEEEYBasePhase (y.1 yt) (q.1 yt) := by
  rw [sectorBuild_eq_mixedOverlap]
  rw [addedPhaseVanishes]
  exact diamondIntertwine hn hb2 hc2 hd2 y q A hA

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveY
