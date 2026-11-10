import Core4loop.CompleteGraph.EvenAllLarge.DescendedRank

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP

noncomputable section


theorem finrank_range_k4EvenPBaseCross_addition_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (k4EvenPBaseCross
            (n := n) (b := b) (c := c) (d := d))) =
      2 * (n * (n - 1) * (n ^ c - 2 * (n - 1))) +
      ((n - 1) * (3 * n ^ 2 - 4 * n + 6) +
      ((n ^ (b - 1) - 2) * (2 * n * (n - 1)) +
      ((n ^ (d - 1) - 2) * (2 * n * (n - 1)) +
      ((n ^ (c - 1) - 2) * ((n - 1) * (n ^ 2 + 3 * n)) +
      ((n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) *
          (n ^ 2 * (n - 1)) +
      ((n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
          (n ^ 2 * (n - 1)) + (0 + 0))))))) := by
  rw [finrank_range_k4BaseCross_eq_gPolar_add_descended,
    finrank_range_k4EvenPGPolar hn2 hn hb2 hc2 hd2,
    finrank_range_k4BaseDescendedCross_addition_first hn2 hn hb2 hc2 hd2]


end
end Core4loop.CompleteGraph.EvenP.BaseKKT
