import Core4loop.CompleteGraph.CorrectedProvenance.CorrectionDefinitions
import Core4loop.CompleteGraph.CorrectedProvenance.Definitions
import Core4loop.SquareDiagonal.CorrectedProvenance.CastSafety

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

open CompleteGraph.EvenP

noncomputable section

set_option synthInstance.maxHeartbeats 1000000 in
-- The even all-large raw identity requires bounded finite-space instance search.
set_option maxHeartbeats 10000000 in
-- The cast-safe source/range arithmetic is normalized symbolically at all block sizes.
theorem k4EvenAllLargeRawExponentNat_eq_X4PaperOldZ_add_correction
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (ha2 : 2 <= a) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d) :
    (k4EvenAllLargeRawExponentNat
        (n := n) (a := a) (b := b) (c := c) (d := d) : Int) =
      X4PaperOldZ a b c d n -
        mZ n * ((n : Int) - 2) * (3 * (n : Int) + 1) := by
  rcases SquareDiagonal.EvenP.diamondEvenPTailIndex_nonempty hn ha2 with ⟨t0⟩
  have hraw := k4EvenAllLargeRawExponentNat_add_halfRank_eq_scale_add_source
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hn2 hn ha2 hb2 hc2 hd2 t0
  have hsource := finrank_K4PreCSource_add_range
    (n := n) (a := a) (b := b) (c := c) (d := d) (by omega)
  have hrange := finrank_range_k4PreCMap_add_vertex_terms
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (by omega) (by omega) (by omega) (by omega)
  have hrawZ := congrArg (fun q : Nat => (q : Int)) hraw
  have hsourceZ := congrArg (fun q : Nat => (q : Int)) hsource
  have hrangeZ := congrArg (fun q : Nat => (q : Int)) hrange
  have hn1 : 1 <= n := by omega
  have hcasta : ((n ^ (a - 1) - 2 : Nat) : Int) =
      (n : Int) ^ (a - 1) - 2 :=
    cast_pow_pred_sub_two hn2 ha2
  have hcastb : ((n ^ (b - 1) - 2 : Nat) : Int) =
      (n : Int) ^ (b - 1) - 2 :=
    cast_pow_pred_sub_two hn2 hb2
  have hcastc : ((n ^ (c - 1) - 2 : Nat) : Int) =
      (n : Int) ^ (c - 1) - 2 :=
    cast_pow_pred_sub_two hn2 hc2
  have hcastd : ((n ^ (d - 1) - 2 : Nat) : Int) =
      (n : Int) ^ (d - 1) - 2 :=
    cast_pow_pred_sub_two hn2 hd2
  have hq2 : 2 <= n ^ (c - 1) :=
    pow_pred_ge_two_of_ge_two hn2 hc2
  have hpowc : n ^ c = n * n ^ (c - 1) := by
    calc
      n ^ c = n ^ ((c - 1) + 1) :=
        congrArg (fun e : Nat => n ^ e) (by omega)
      _ = n ^ (c - 1) * n := pow_succ n (c - 1)
      _ = n * n ^ (c - 1) := Nat.mul_comm _ _
  have hsafety : 2 * (n - 1) <= n ^ c := by
    calc
      2 * (n - 1) <= 2 * n :=
        Nat.mul_le_mul_left 2 (Nat.sub_le n 1)
      _ = n * 2 := by ring
      _ <= n * n ^ (c - 1) := Nat.mul_le_mul_left n hq2
      _ = n ^ c := hpowc.symm
  have hcastmain : ((n ^ c - 2 * (n - 1) : Nat) : Int) =
      (n : Int) ^ c - 2 * ((n : Int) - 1) := by
    rw [Nat.cast_sub hsafety]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      Nat.cast_sub hn1, Nat.cast_one]
  have hquad : 4 * n <= 3 * n ^ 2 := by
    nlinarith [sq_nonneg (n - 2)]
  have hcastquad : ((3 * n ^ 2 - 4 * n : Nat) : Int) =
      3 * (n : Int) ^ 2 - 4 * (n : Int) := by
    rw [Nat.cast_sub hquad]
    norm_num
  have hpowa : (n : Int) ^ a = (n : Int) ^ (a - 1) * (n : Int) := by
    calc
      (n : Int) ^ a = (n : Int) ^ ((a - 1) + 1) :=
        congrArg (fun e : Nat => (n : Int) ^ e) (by omega)
      _ = (n : Int) ^ (a - 1) * (n : Int) := pow_succ _ _
  have hpowb : (n : Int) ^ b = (n : Int) ^ (b - 1) * (n : Int) := by
    calc
      (n : Int) ^ b = (n : Int) ^ ((b - 1) + 1) :=
        congrArg (fun e : Nat => (n : Int) ^ e) (by omega)
      _ = (n : Int) ^ (b - 1) * (n : Int) := pow_succ _ _
  have hpowcZ : (n : Int) ^ c = (n : Int) ^ (c - 1) * (n : Int) := by
    calc
      (n : Int) ^ c = (n : Int) ^ ((c - 1) + 1) :=
        congrArg (fun e : Nat => (n : Int) ^ e) (by omega)
      _ = (n : Int) ^ (c - 1) * (n : Int) := pow_succ _ _
  have hpowd : (n : Int) ^ d = (n : Int) ^ (d - 1) * (n : Int) := by
    calc
      (n : Int) ^ d = (n : Int) ^ ((d - 1) + 1) :=
        congrArg (fun e : Nat => (n : Int) ^ e) (by omega)
      _ = (n : Int) ^ (d - 1) * (n : Int) := pow_succ _ _
  simp only [k4EvenAllLargeHalfRankNat, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow] at hrawZ
  rw [hcasta, hcastb, hcastc, hcastd, hcastmain, hcastquad] at hrawZ
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hsourceZ hrangeZ
  rw [Nat.cast_sub hn1] at hrawZ hrangeZ
  simp only [Nat.cast_ofNat, Nat.cast_one] at hrawZ hrangeZ
  unfold X4PaperOldZ X4Z Sigma1Z Sigma2_4Z nPowZ ThetaZ mZ
  simp only [hn, ha2, hb2, hc2, hd2, and_self, if_true]
  simp only [pow_add] at hrawZ hsourceZ hrangeZ ⊢
  rw [hpowa, hpowb, hpowd] at hrawZ hsourceZ hrangeZ ⊢
  rw [hpowcZ] at hrawZ hsourceZ ⊢
  linear_combination hrawZ + hsourceZ - hrangeZ

end
end Core4loop
