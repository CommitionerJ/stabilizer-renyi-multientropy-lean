import Core4loop.SquareDiagonal.EvenP.TotalBWSymmetry
import Core4loop.SquareDiagonal.EvenP.TotalEOOE

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

theorem rank_diamondEvenPCross_EEOO
    {n b : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hb2 : 2 ≤ b) :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := b) (c := 1) (d := 1)))
      =
    n * (n - 1) ^ 2 := by
  rw [rank_diamondEvenPCross_bw
    (n := n) (b := 1) (c := 1) (d := b)]
  exact rank_diamondEvenPCross_EOOE hn2 hn hb2

end Core4loop.SquareDiagonal.EvenP
