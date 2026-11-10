import Core4loop.TriangleLeaf.CorrectedOdd
import Core4loop.TriangleLeaf.CorrectedDEqOne
import Core4loop.TriangleLeaf.CorrectedEvenMin
import Core4loop.TriangleLeaf.CorrectedRaw
import Core4loop.TriangleLeaf.CorrectedEvenMinGeTwoClean
import Core4loop.TriangleLeaf.CorrectedEvenLarge

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-- Logical level 7: corrected raw TriangleLeaf Delta for the even E2 branch. -/
theorem DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_triangleLeafE2
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha : a = 1)
    (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) :
    DeltaNF .triangleLeaf a b c d n =
      (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c d n) := by
  have hnot : ¬ TriangleLeafExceptional n a b c d := by
    intro hex
    unfold TriangleLeafExceptional at hex
    rcases hdeg with hb1 | hc1 <;> omega
  have hcorrected :
      X1CorrectedZ a b c d n = X1Z a b c d n := by
    unfold X1CorrectedZ
    rw [X1PaperOldZ_eq_current_X1Z]
    rw [correctionZ_nonexceptional hnot, sub_zero]
  rw [hcorrected]
  exact DeltaNF_triangleLeaf_eq_pow_X1Z_triangleLeafE2
    hn ha hb hc hdeg hd2

/-- Logical level 7: corrected raw TriangleLeaf Delta for all positive blocks. -/
theorem DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ
    {n a b c d : ℕ} [NeZero n]
    (hn2 : 2 ≤ n)
    (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .triangleLeaf a b c d n =
      (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c d n) := by
  rcases Nat.even_or_odd n with hn | hn
  · by_cases hd1 : d = 1
    · subst d
      exact DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_d_eq_one ha hb hc
    · have hd2 : 2 ≤ d := by omega
      by_cases ha1 : a = 1
      · by_cases hb1 : b = 1
        · exact DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_triangleLeafE2
            hn ha1 hb hc (Or.inl hb1) hd2
        · have hb2 : 2 ≤ b := by omega
          by_cases hc1 : c = 1
          · exact DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_triangleLeafE2
              hn ha1 hb hc (Or.inr hc1) hd2
          · have hc2 : 2 ≤ c := by omega
            exact
              Core4loop.DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_exceptional
                hn ha1 hb2 hc2 hd2
      · have ha2 : 2 ≤ a := by omega
        by_cases hb1 : b = 1
        · exact DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_triangleLeafE5
            hn2 hn ha2 hb hc (Or.inl hb1) hd2
        · have hb2 : 2 ≤ b := by omega
          by_cases hc1 : c = 1
          · exact DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_triangleLeafE5
              hn2 hn ha2 hb hc (Or.inr hc1) hd2
          · have hc2 : 2 ≤ c := by omega
            exact DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_even_large
              hn2 hn ha2 hb2 hc2 hd2
  · exact DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_of_odd
      ha hb hc hd hn

end

end TriangleLeaf
end Core4loop
