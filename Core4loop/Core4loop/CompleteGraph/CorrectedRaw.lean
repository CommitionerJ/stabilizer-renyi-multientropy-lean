import Core4loop.CompleteGraph.DirectWitt.SourceFirstExponent
import Core4loop.CompleteGraph.Relabel.Permutation
import Core4loop.CompleteGraph.SingletonLC.StarKernel
import Core4loop.CompleteGraph.PreC.DiamondReuse

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop

open CompleteGraph.SingletonLC
open CompleteGraph.Odd
open CompleteGraph.EvenP
open SquareDiagonal.EvenP

noncomputable section

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

private theorem correctedRaw_DeltaNF_complete_eq_preC_kernel_sum
    {n a b c d : Nat} [NeZero n] :
    DeltaNF .complete a b c d n =
      (Fintype.card (CFun4 n a b d) : Int) *
        ∑ x : K4PreCSource n a b c d, bitSign (k4PreCQ x) := by
  have h := DeltaNF_complete_eq_preC_kernel_sum
    (n := n) (a := a) (b := b) (c := c) (d := d)
  convert h using 1
  congr 1
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _
    rfl

theorem DeltaNF_complete_eq_pow_X4SourceZ_of_a_eq_one
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (ha1 : a = 1)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .complete a b c d n =
      (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
  calc
    DeltaNF .complete a b c d n = StarDeltaNF n b c d :=
      DeltaNF_complete_eq_StarDeltaNF_of_a_eq_one hn2 ha1 hb hc hd
    _ = (2 : Int) ^ K4StarExpNat n b c d :=
      StarDeltaNF_eq_pow hn2 hb hc hd
    _ = (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
      rw [X4SourceZ_of_a_eq_one ha1, Int.toNat_natCast]

theorem DeltaNF_complete_eq_pow_X4SourceZ_of_a_ne_one_b_eq_one
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (ha1 : a ≠ 1) (hb1 : b = 1)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .complete a b c d n =
      (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
  calc
    DeltaNF .complete a b c d n = DeltaNF .complete b a c d n :=
      (DeltaNF_complete_move_B_to_root ha (by omega)).symm
    _ = StarDeltaNF n a c d :=
      DeltaNF_complete_eq_StarDeltaNF_of_a_eq_one hn2 hb1 ha hc hd
    _ = (2 : Int) ^ K4StarExpNat n a c d :=
      StarDeltaNF_eq_pow hn2 ha hc hd
    _ = (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
      rw [X4SourceZ_of_a_ne_one_b_eq_one ha1 hb1, Int.toNat_natCast]

theorem DeltaNF_complete_eq_pow_X4SourceZ_of_ab_ne_one_c_eq_one
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c = 1)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    DeltaNF .complete a b c d n =
      (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
  calc
    DeltaNF .complete a b c d n = DeltaNF .complete c a b d n :=
      (DeltaNF_complete_move_C_to_root ha (by omega)).symm
    _ = StarDeltaNF n a b d :=
      DeltaNF_complete_eq_StarDeltaNF_of_a_eq_one hn2 hc1 ha hb hd
    _ = (2 : Int) ^ K4StarExpNat n a b d :=
      StarDeltaNF_eq_pow hn2 ha hb hd
    _ = (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
      rw [X4SourceZ_of_ab_ne_one_c_eq_one ha1 hb1 hc1,
        Int.toNat_natCast]

theorem DeltaNF_complete_eq_pow_X4SourceZ_of_abc_ne_one_d_eq_one
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hd1 : d = 1)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    DeltaNF .complete a b c d n =
      (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
  calc
    DeltaNF .complete a b c d n = DeltaNF .complete d a b c n :=
      (DeltaNF_complete_move_D_to_root ha (by omega)).symm
    _ = StarDeltaNF n a b c :=
      DeltaNF_complete_eq_StarDeltaNF_of_a_eq_one hn2 hd1 ha hb hc
    _ = (2 : Int) ^ K4StarExpNat n a b c :=
      StarDeltaNF_eq_pow hn2 ha hb hc
    _ = (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
      rw [X4SourceZ_of_abc_ne_one_d_eq_one ha1 hb1 hc1 hd1,
        Int.toNat_natCast]

theorem DeltaNF_complete_eq_pow_X4SourceZ_odd_all_large
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Odd n)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DeltaNF .complete a b c d n =
      (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
  have hsum :
      (∑ x : K4PreCSource n a b c d, bitSign (k4PreCQ x)) =
        (2 : Int) ^
          k4OddResidualExponent
            (a := a) (b := b) (c := c) (d := d) hn := by
    convert sum_bitSign_k4PreCQ_eq_pow_odd_all_large
      hn2 hn ha2 hb2 hc2 hd2 using 1
    apply Finset.sum_congr
    · ext x
      simp
    · intro x _
      rfl
  rw [correctedRaw_DeltaNF_complete_eq_preC_kernel_sum]
  rw [card_CFun4 (by omega)]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [hsum, ← pow_add]
  rw [X4SourceZ_of_all_ne_one_odd
    (by omega) (by omega) (by omega) (by omega) hn]
  rw [Int.toNat_natCast]
  rfl

theorem DeltaNF_complete_eq_pow_X4SourceZ_even_all_large
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DeltaNF .complete a b c d n =
      (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
  rcases diamondEvenPTailIndex_nonempty hn ha2 with ⟨t0⟩
  have hsum :
      (∑ x : K4PreCSource n a b c d, bitSign (k4PreCQ x)) =
        (2 : Int) ^
          k4EvenAllLargeResidualExponent
            (n := n) (a := a) (b := b) (c := c) (d := d) := by
    convert sum_bitSign_k4PreCQ_eq_pow_even_all_large
      hn2 hn ha2 hb2 hc2 hd2 t0 using 1
    apply Finset.sum_congr
    · ext x
      simp
    · intro x _
      rfl
  rw [correctedRaw_DeltaNF_complete_eq_preC_kernel_sum]
  rw [card_CFun4 (by omega)]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [hsum, ← pow_add]
  rw [X4SourceZ_of_all_ne_one_even
    (by omega) (by omega) (by omega) (by omega) hn]
  rw [Int.toNat_natCast]
  rfl

end
end Core4loop
