import Core4loop.SquareDiagonal.CorrectedExponent
import Core4loop.SquareDiagonal.CorrectedProvenance.Singleton.CSingleton
import Core4loop.SquareDiagonal.CorrectedProvenance.Singleton.CLarge

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem X3CorrectedZ_eq_old_add_correction_of_even_a_eq_one
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    X3CorrectedZ 1 b c d n =
      X3PaperOldZ 1 b c d n +
        DiamondCorrectionZ n 1 b c d := by
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  rw [X3CorrectedZ_of_even_a_eq_one hn rfl]
  by_cases hc1 : c = 1
  · subst c
    by_cases hb1 : b = 1
    · subst b
      by_cases hd1 : d = 1
      · subst d
        exact
          X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_one_b_one_d_one
            hn
      · exact
          X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_one_b_one_d_ge_two
            hn (by omega)
    · by_cases hd1 : d = 1
      · subst d
        exact
          X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_one_b_ge_two_d_one
            hn (by omega)
      · exact
          X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_one_b_ge_two_d_ge_two
            hn (by omega) (by omega)
  · have hc2 : 2 ≤ c := by omega
    by_cases hb1 : b = 1
    · subst b
      by_cases hd1 : d = 1
      · subst d
        exact
          X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_ge_two_b_one_d_one
            hn hc2
      · exact
          X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_ge_two_b_one_d_ge_two
            hn hc2 (by omega)
    · by_cases hd1 : d = 1
      · subst d
        exact
          X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_ge_two_b_ge_two_d_one
            hn (by omega) hc2
      · exact
          X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_ge_two_b_ge_two_d_ge_two
            hn (by omega) hc2 (by omega)

end Core4loop
