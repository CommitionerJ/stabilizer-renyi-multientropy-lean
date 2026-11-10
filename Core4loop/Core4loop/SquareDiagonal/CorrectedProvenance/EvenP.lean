import Core4loop.SquareDiagonal.CorrectedExponent
import Core4loop.SquareDiagonal.CorrectedProvenance.EvenP.CSingleton
import Core4loop.SquareDiagonal.CorrectedProvenance.EvenP.CLarge

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem X3CorrectedZ_eq_old_add_correction_of_even_a_ge_two
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    X3CorrectedZ a b c d n =
      X3PaperOldZ a b c d n +
        DiamondCorrectionZ n a b c d := by
  rw [X3CorrectedZ_of_even_a_ne_one hn (by omega)]
  by_cases hc1 : c = 1
  · subst c
    by_cases hb1 : b = 1
    · subst b
      by_cases hd1 : d = 1
      · subst d
        exact
          X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_one_b_one_d_one
            hn2 hn ha2
      · exact
          X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_one_b_one_d_ge_two
            hn2 hn ha2 (by omega)
    · by_cases hd1 : d = 1
      · subst d
        exact
          X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_one_b_ge_two_d_one
            hn2 hn ha2 (by omega)
      · exact
          X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_one_b_ge_two_d_ge_two
            hn2 hn ha2 (by omega) (by omega)
  · have hc2 : 2 ≤ c := by omega
    by_cases hb1 : b = 1
    · subst b
      by_cases hd1 : d = 1
      · subst d
        exact
          X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_ge_two_b_one_d_one
            hn2 hn ha2 hc2
      · exact
          X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_ge_two_b_one_d_ge_two
            hn2 hn ha2 hc2 (by omega)
    · by_cases hd1 : d = 1
      · subst d
        exact
          X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_ge_two_b_ge_two_d_one
            hn2 hn ha2 (by omega) hc2
      · exact
          X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_ge_two_b_ge_two_d_ge_two
            hn2 hn ha2 (by omega) hc2 (by omega)

end Core4loop
