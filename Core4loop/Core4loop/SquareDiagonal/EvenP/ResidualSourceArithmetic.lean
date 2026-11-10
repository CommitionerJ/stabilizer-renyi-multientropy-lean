import Core4loop.SquareDiagonal.EvenP.ResidualRank
import Core4loop.SquareDiagonal.DirectWitt.SourceRank

namespace Core4loop.SquareDiagonal.EvenP

theorem diamondEvenP_residual_source_add_range
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    diamondEvenPResidualExponent n a b c d +
        diamondEvenPTotalHalfRank n b c d +
        Module.finrank F
          (LinearMap.range
            (diamondPreCMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
      n^(b+c+d) + n^(a+c+d) + n^(a+b+c) := by
  rw [diamondEvenP_residual_add_totalHalfRank_eq_source
    hn2 hn ha2 hb hc hd]
  exact DirectWitt.finrank_diamondPreCSource_add_range (by omega)

theorem diamondEvenP_residual_source_closed_addition
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    diamondEvenPResidualExponent n a b c d +
        diamondEvenPTotalHalfRank n b c d +
        ((n - 1) * (n^(a+b) + n^(a+d) + n^(b+d)) +
          (n - 1)^3) =
      (n^(b+c+d) + n^(a+c+d) + n^(a+b+c)) +
        (n - 1)^2 * (n^a + n^b + n^d) := by
  have hsource :=
    diamondEvenP_residual_source_add_range
      hn2 hn ha2 hb hc hd
  have hrange :=
    DirectWitt.finrank_range_diamondPreCMap_add_vertex_terms
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (by omega) hb hc hd
  omega

end Core4loop.SquareDiagonal.EvenP
