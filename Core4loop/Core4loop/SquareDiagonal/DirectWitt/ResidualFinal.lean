import Core4loop.SquareDiagonal.DirectWitt.OddResidual
import Core4loop.SquareDiagonal.DirectWitt.SourceRank

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal.DirectWitt

open Core4loop

theorem diamondOdd_residual_source_add_range
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    diamondOddResidualExponent
          (a := a) (b := b) (c := c) (d := d) hn +
        diamondOddHalfRank n b c d +
        Module.finrank F
          (LinearMap.range
            (diamondPreCMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
      n ^ (b + c + d) + n ^ (a + c + d) +
        n ^ (a + b + c) := by
  rw [diamondOddResidualExponent_add_halfRank_eq_preCSource
    hb hc hd hn]
  exact finrank_diamondPreCSource_add_range ha

theorem diamondOdd_residual_source_closed_addition
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    diamondOddResidualExponent
          (a := a) (b := b) (c := c) (d := d) hn +
        diamondOddHalfRank n b c d +
        ((n - 1) *
            (n ^ (a + b) + n ^ (a + d) + n ^ (b + d)) +
          (n - 1) ^ 3) =
      (n ^ (b + c + d) + n ^ (a + c + d) +
          n ^ (a + b + c)) +
        (n - 1) ^ 2 * (n ^ a + n ^ b + n ^ d) := by
  have hsource :=
    diamondOdd_residual_source_add_range ha hb hc hd hn
  have hrange :=
    finrank_range_diamondPreCMap_add_vertex_terms
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd
  omega

end Core4loop.SquareDiagonal.DirectWitt
