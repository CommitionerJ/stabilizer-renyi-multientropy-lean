import Core4loop.SquareDiagonal.EvenP.Residual
import Core4loop.SquareDiagonal.EvenP.RankDispatcher

namespace Core4loop.SquareDiagonal.EvenP

theorem diamondEvenP_residual_add_totalHalfRank_eq_source
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    diamondEvenPResidualExponent n a b c d +
      diamondEvenPTotalHalfRank n b c d =
      Module.finrank F (DiamondPreCSource n a b c d) := by
  rw [← rank_diamondEvenPCross_eq_totalHalfRank hn2 hn hb hc hd]
  exact diamondEvenP_residual_add_crossRank_eq_source hn ha2

end Core4loop.SquareDiagonal.EvenP
