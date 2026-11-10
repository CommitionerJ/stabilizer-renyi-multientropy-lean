import Core4loop.CompleteGraph.CorrectedRaw

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem DeltaNF_complete_eq_pow_X4SourceZ
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .complete a b c d n =
      (2 : Int) ^ Int.toNat (X4SourceZ a b c d n) := by
  by_cases ha1 : a = 1
  · exact DeltaNF_complete_eq_pow_X4SourceZ_of_a_eq_one
      hn2 ha1 hb hc hd
  by_cases hb1 : b = 1
  · exact DeltaNF_complete_eq_pow_X4SourceZ_of_a_ne_one_b_eq_one
      hn2 ha1 hb1 ha hc hd
  by_cases hc1 : c = 1
  · exact DeltaNF_complete_eq_pow_X4SourceZ_of_ab_ne_one_c_eq_one
      hn2 ha1 hb1 hc1 ha hb hd
  by_cases hd1 : d = 1
  · exact DeltaNF_complete_eq_pow_X4SourceZ_of_abc_ne_one_d_eq_one
      hn2 ha1 hb1 hc1 hd1 ha hb hc
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  have hc2 : 2 ≤ c := by omega
  have hd2 : 2 ≤ d := by omega
  rcases Nat.even_or_odd n with hn | hn
  · exact DeltaNF_complete_eq_pow_X4SourceZ_even_all_large
      hn2 hn ha2 hb2 hc2 hd2
  · exact DeltaNF_complete_eq_pow_X4SourceZ_odd_all_large
      hn2 hn ha2 hb2 hc2 hd2

end Core4loop
