import Core4loop.CompleteGraph.CorrectedProvenance.CorrectionDefinitions
import Core4loop.CompleteGraph.CorrectedProvenance.Definitions

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

open CompleteGraph.Odd

noncomputable section

theorem k4OddRawExponentNat_eq_X4PaperOldZ
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Odd n)
    (ha2 : 2 <= a) (hb2 : 2 <= b)
    (hc2 : 2 <= c) (hd2 : 2 <= d) :
    (k4OddRawExponentNat
        (a := a) (b := b) (c := c) (d := d) hn : Int) =
      X4PaperOldZ a b c d n := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : c ≠ 0)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hraw := k4OddRawExponentNat_add_halfRank_eq_scale_add_source
    (n := n) (a := a + 1) (b := b + 1) (c := c + 1) (d := d + 1)
    hn2 hn ha2 hb2 hc2 hd2
  have hsource := finrank_K4PreCSource_add_range
    (n := n) (a := a + 1) (b := b + 1) (c := c + 1) (d := d + 1)
    (by omega)
  have hrange := finrank_range_k4PreCMap_add_vertex_terms
    (n := n) (a := a + 1) (b := b + 1) (c := c + 1) (d := d + 1)
    (by omega) (by omega) (by omega) (by omega)
  have hrawZ := congrArg (fun q : Nat => (q : Int)) hraw
  have hsourceZ := congrArg (fun q : Nat => (q : Int)) hsource
  have hrangeZ := congrArg (fun q : Nat => (q : Int)) hrange
  have hn1 : 1 <= n := by omega
  have hpa : 1 <= n ^ a := Nat.one_le_pow a n hn1
  have hpb : 1 <= n ^ b := Nat.one_le_pow b n hn1
  have hpc : 1 <= n ^ c := Nat.one_le_pow c n hn1
  have hpd : 1 <= n ^ d := Nat.one_le_pow d n hn1
  have hnot : ¬ Even n := Nat.not_even_iff_odd.mpr hn
  simp only [k4OddHalfRankNat, Nat.succ_sub_one,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hn1,
    Nat.cast_sub hpa, Nat.cast_sub hpb, Nat.cast_sub hpc,
    Nat.cast_sub hpd, Nat.cast_one] at hrawZ hsourceZ hrangeZ
  unfold X4PaperOldZ X4Z Sigma1Z Sigma2_4Z nPowZ ThetaZ mZ
  simp only [hnot, false_and, if_false]
  simp only [pow_add, pow_succ] at hrawZ hsourceZ hrangeZ ⊢
  linear_combination hrawZ + hsourceZ - hrangeZ

end
end Core4loop
