import Core4loop.SquareDiagonal.EvenP.TotalBWSymmetry
import Core4loop.SquareDiagonal.EvenP.TotalEOEE

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

theorem rank_diamondEvenPCross_EEEO
    {n b c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := b) (c := c) (d := 1)))
      =
    3 * n ^ 2 * (n - 1)
      + (n ^ (b - 1) - 2) * n ^ 2 * (n - 1)
      + (n ^ (c - 1) - 2) * n * (n - 1) * (2 * n + 1)
      + (n ^ (c - 1) - 2) * (n ^ (b - 1) - 2) *
          n ^ 2 * (n - 1) := by
  rw [rank_diamondEvenPCross_bw
    (n := n) (b := 1) (c := c) (d := b)]
  exact rank_diamondEvenPCross_EOEE hn2 hn hc2 hb2

end Core4loop.SquareDiagonal.EvenP
