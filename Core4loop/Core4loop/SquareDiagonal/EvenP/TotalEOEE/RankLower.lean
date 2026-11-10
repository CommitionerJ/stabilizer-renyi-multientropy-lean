import Core4loop.SquareDiagonal.EvenP.TotalEOEE.BlockAlignment

set_option autoImplicit false
set_option warningAsError true
-- All four lower product-rank calculations share this elaboration budget.
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEOEEInternal

theorem rank_totalEOEEWAmplifiedCross
    {n d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (totalEOEEWAmplifiedCross (n := n) (d := d))) =
      (n ^ (d - 1) - 2) * n ^ 2 * (n - 1) := by
  unfold totalEOEEWAmplifiedCross
  rw [finrank_range_diamondTailAmplify
      (n := n) (k := d) hn2 hn hd2
      (diamondEOEEWCross (n := n)),
    finrank_diamondEvenAxisTailZero hn2 hn hd2,
    rank_diamondEOEEWCross hn2]
  ring

theorem rank_totalEOEEZAmplifiedCross
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    Module.finrank F
        (LinearMap.range
          (totalEOEEZAmplifiedCross (n := n) (c := c))) =
      (n ^ (c - 1) - 2) * n * (n - 1) * (2 * n + 1) := by
  unfold totalEOEEZAmplifiedCross
  rw [finrank_range_diamondTailAmplify
      (n := n) (k := c) hn2 hn hc2
      (diamondTailOneEvenZCross (n := n)),
    finrank_diamondEvenAxisTailZero hn2 hn hc2,
    rank_diamondTailOneEvenZCross]
  ring

theorem rank_totalEOEEZWAmplifiedCross
    {n c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (totalEOEEZWAmplifiedCross
            (n := n) (c := c) (d := d))) =
      (n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
        n ^ 2 * (n - 1) := by
  unfold totalEOEEZWAmplifiedCross
  rw [finrank_range_diamondMixedTailAmplify
      (n := n) (k := c) (l := d)
      hn2 hn hc2 hd2
      (diamondTailSingleICross (n := n)),
    finrank_diamondEvenAxisTailZero hn2 hn hc2,
    finrank_diamondEvenAxisTailZero hn2 hn hd2,
    rank_diamondTailSingleICross]
  ring

theorem rank_totalEOEEZAndZWCross
    {n c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (totalEOEEZAndZWCross
            (n := n) (c := c) (d := d))) =
      (n ^ (c - 1) - 2) * n * (n - 1) * (2 * n + 1) +
        (n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
          n ^ 2 * (n - 1) := by
  unfold totalEOEEZAndZWCross
  rw [finrank_range_diamondCrossProd
      (totalEOEEZAmplifiedCross (n := n) (c := c))
      (totalEOEEZWAmplifiedCross (n := n) (c := c) (d := d)),
    rank_totalEOEEZAmplifiedCross hn2 hn hc2,
    rank_totalEOEEZWAmplifiedCross hn2 hn hc2 hd2]


end TotalEOEEInternal

end

end Core4loop.SquareDiagonal.EvenP
