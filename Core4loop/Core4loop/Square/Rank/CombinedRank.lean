import Core4loop.Square.Rank.IntersectionModel
import Core4loop.Square.Rank.Final

namespace Core4loop

theorem finrank_inf_range_SquareBMap_SquareWMap_add_core
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (↑(LinearMap.range
            (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
          LinearMap.range
            (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d))))
      + 2 * (n - 1) ^ 3 =
    (n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1) := by
  exact finrank_SquareBWIntersection_add_core
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd

lemma square_combined_rank_nat_algebra
    {rankB rankW rankI rank a b c d n : ℕ} [NeZero n]
    (hSup : rank + rankI = rankB + rankW)
    (hB : rankB + (n - 1) ^ 2 * n ^ d =
      (n - 1) * n ^ (c + d) + (n - 1) * n ^ (a + d))
    (hW : rankW + (n - 1) ^ 2 * n ^ b =
      (n - 1) * n ^ (b + c) + (n - 1) * n ^ (a + b))
    (hI : rankI + 2 * (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1)) :
    rank + (n - 1) ^ 2 * (n ^ a + n ^ b + n ^ c + n ^ d) + (n - 1)
      =
        (n - 1) * (n ^ (c + d) + n ^ (a + d) + n ^ (a + b) + n ^ (b + c))
          + 2 * (n - 1) ^ 3 := by
  nlinarith

theorem finrank_range_SquareCombined_add_square_vertices
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * (n ^ a + n ^ b + n ^ c + n ^ d)
      + (n - 1)
    =
      (n - 1) * (n ^ (c + d) + n ^ (a + d) + n ^ (a + b) + n ^ (b + c))
        + 2 * (n - 1) ^ 3 := by
  let RB := LinearMap.range
    (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d))
  let RW := LinearMap.range
    (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d))
  let rank := Module.finrank F
    (LinearMap.range
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)))
  let rankB := Module.finrank F RB
  let rankW := Module.finrank F RW
  let rankI := Module.finrank F (↑(RB ⊓ RW))
  have hsup0 := Submodule.finrank_sup_add_finrank_inf_eq RB RW
  have hSup : rank + rankI = rankB + rankW := by
    dsimp [rank, rankI, rankB, rankW, RB, RW]
    rw [range_SquareCombined_eq_sup_range_B_W
      (n := n) (a := a) (b := b) (c := c) (d := d)]
    exact hsup0
  have hB : rankB + (n - 1) ^ 2 * n ^ d =
      (n - 1) * n ^ (c + d) + (n - 1) * n ^ (a + d) := by
    dsimp [rankB, RB]
    exact finrank_range_SquareBMap_add_vertex_d
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc
  have hW : rankW + (n - 1) ^ 2 * n ^ b =
      (n - 1) * n ^ (b + c) + (n - 1) * n ^ (a + b) := by
    dsimp [rankW, RW]
    exact finrank_range_SquareWMap_add_vertex_b
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hd
  have hI : rankI + 2 * (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1) := by
    dsimp [rankI, RB, RW]
    exact finrank_inf_range_SquareBMap_SquareWMap_add_core
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd
  exact square_combined_rank_nat_algebra
    (rankB := rankB) (rankW := rankW) (rankI := rankI) (rank := rank)
    (a := a) (b := b) (c := c) (d := d) (n := n) hSup hB hW hI

theorem DeltaNF_square_closed
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .square a b c d n =
      (2 : ℤ) ^ Int.toNat (X2Z a b c d n) :=
  DeltaNF_square_closed_of_rank_add (n := n) (a := a) (b := b) (c := c) (d := d) ha
    (finrank_range_SquareCombined_add_square_vertices
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)

end Core4loop
