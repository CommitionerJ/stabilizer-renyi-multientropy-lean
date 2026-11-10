import Core4loop.CompleteGraph.EvenAllLarge.PassiveW.FullSupport
import Core4loop.SquareDiagonal.EvenP.TotalEEEE.Rank

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

noncomputable section

theorem finrank_range_descendedCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range (descendedCross hn2 hn hb2 hc2 hd2)) =
      (n ^ (d - 1) - 2) * (2 * n * (n - 1)) := by
  rw [descendedCross_eq]
  let E :=
    TotalEEEERankInternal.rangeCompEquivOfInjective
      (tailCross (n := n) (d := d))
      (rightRead hn hb2 hc2 hd2).dualMap
      (LinearMap.dualMap_injective_of_surjective
        (rightRead_surjective hn hb2 hc2 hd2))
  have htail :
      Module.finrank F
          (LinearMap.range (tailCross (n := n) (d := d))) =
        (n ^ (d - 1) - 2) * (2 * n * (n - 1)) := by
    rw [tailCross,
      finrank_range_diamondTailAmplify hn2 hn hd2,
      finrank_diamondEvenAxisTailZero hn2 hn hd2,
      rank_totalEEEEWBaseCross]
  exact (LinearEquiv.finrank_eq E).symm.trans htail


end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveW
