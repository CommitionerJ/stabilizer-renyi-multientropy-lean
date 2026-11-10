import Core4loop.SquareDiagonal.EvenP.TotalEOOO
import Core4loop.SquareDiagonal.EvenP.TotalEOOE
import Core4loop.SquareDiagonal.EvenP.TotalEOEO
import Core4loop.SquareDiagonal.EvenP.TotalEOEE
import Core4loop.SquareDiagonal.EvenP.TotalEEOO
import Core4loop.SquareDiagonal.EvenP.TotalEEOE
import Core4loop.SquareDiagonal.EvenP.TotalEEEO
import Core4loop.SquareDiagonal.EvenP.TotalEEEE.Rank

namespace Core4loop.SquareDiagonal.EvenP

noncomputable section

def diamondEvenPTotalHalfRank (n b c d : Nat) : Nat :=
  if b = 1 then
    if c = 1 then
      if d = 1 then
        n * (n - 1) ^ 2
      else
        n * (n - 1) ^ 2
    else
      if d = 1 then
        2 * n ^ 2 * (n - 1) +
          (n ^ (c - 1) - 2) * n * (n - 1) * (n + 1)
      else
        3 * n ^ 2 * (n - 1) +
          (n ^ (d - 1) - 2) * n ^ 2 * (n - 1) +
          (n ^ (c - 1) - 2) * n * (n - 1) * (2 * n + 1) +
          (n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
            n ^ 2 * (n - 1)
  else
    if c = 1 then
      if d = 1 then
        n * (n - 1) ^ 2
      else
        2 * (n - 1) ^ 2
    else
      if d = 1 then
        3 * n ^ 2 * (n - 1) +
          (n ^ (b - 1) - 2) * n ^ 2 * (n - 1) +
          (n ^ (c - 1) - 2) * n * (n - 1) * (2 * n + 1) +
          (n ^ (c - 1) - 2) * (n ^ (b - 1) - 2) *
            n ^ 2 * (n - 1)
      else
        (n - 1) *
          (n ^ 2 * (n ^ (d - 1) - 2) * (n ^ (c - 1) - 2) +
            n ^ 2 * (n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) +
            (3 * n ^ 2 + n) * (n ^ (c - 1) - 2) +
            2 * n * (n ^ (d - 1) - 2) +
            2 * n * (n ^ (b - 1) - 2) +
            3 * n ^ 2 + 4)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 500000 in
theorem rank_diamondEvenPCross_eq_totalHalfRank
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := b) (c := c) (d := d))) =
      diamondEvenPTotalHalfRank n b c d := by
  by_cases hb1 : b = 1
  · subst b
    by_cases hc1 : c = 1
    · subst c
      by_cases hd1 : d = 1
      · subst d
        simpa [diamondEvenPTotalHalfRank] using
          (rank_diamondEvenPCross_EOOO (n := n) hn2 hn)
      · have hd2 : 2 ≤ d := by omega
        simpa [diamondEvenPTotalHalfRank, hd1] using
          (rank_diamondEvenPCross_EOOE
            (n := n) (d := d) hn2 hn hd2)
    · have hc2 : 2 ≤ c := by omega
      by_cases hd1 : d = 1
      · subst d
        simpa [diamondEvenPTotalHalfRank, hc1] using
          (rank_diamondEvenPCross_EOEO
            (n := n) (c := c) hn2 hn hc2)
      · have hd2 : 2 ≤ d := by omega
        simpa [diamondEvenPTotalHalfRank, hc1, hd1] using
          (rank_diamondEvenPCross_EOEE
            (n := n) (c := c) (d := d) hn2 hn hc2 hd2)
  · have hb2 : 2 ≤ b := by omega
    by_cases hc1 : c = 1
    · subst c
      by_cases hd1 : d = 1
      · subst d
        simpa [diamondEvenPTotalHalfRank, hb1] using
          (rank_diamondEvenPCross_EEOO
            (n := n) (b := b) hn2 hn hb2)
      · have hd2 : 2 ≤ d := by omega
        simpa [diamondEvenPTotalHalfRank, hb1, hd1] using
          (rank_diamondEvenPCross_EEOE
            (n := n) (b := b) (d := d) hn2 hn hb2 hd2)
    · have hc2 : 2 ≤ c := by omega
      by_cases hd1 : d = 1
      · subst d
        simpa [diamondEvenPTotalHalfRank, hb1, hc1] using
          (rank_diamondEvenPCross_EEEO
            (n := n) (b := b) (c := c) hn2 hn hb2 hc2)
      · have hd2 : 2 ≤ d := by omega
        simpa [diamondEvenPTotalHalfRank, hb1, hc1, hd1] using
          (rank_diamondEvenPCross_EEEE
            (n := n) (b := b) (c := c) (d := d)
            hn2 hn hb2 hc2 hd2)

end

end Core4loop.SquareDiagonal.EvenP
