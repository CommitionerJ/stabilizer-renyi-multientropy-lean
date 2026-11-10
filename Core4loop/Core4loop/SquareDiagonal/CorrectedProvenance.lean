import Core4loop.SquareDiagonal.CorrectedProvenance.Odd
import Core4loop.SquareDiagonal.CorrectedProvenance.Singleton
import Core4loop.SquareDiagonal.CorrectedProvenance.EvenP

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem X3CorrectedZ_eq_X3PaperOldZ_add_DiamondCorrectionZ
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    X3CorrectedZ a b c d n =
      X3PaperOldZ a b c d n +
        DiamondCorrectionZ n a b c d := by
  by_cases hn : Odd n
  · exact X3CorrectedZ_eq_old_add_correction_of_odd hn hb hc hd
  · have heven : Even n := Nat.not_odd_iff_even.mp hn
    by_cases ha1 : a = 1
    · subst a
      exact
        X3CorrectedZ_eq_old_add_correction_of_even_a_eq_one
          hn2 heven hb hc hd
    · exact
        X3CorrectedZ_eq_old_add_correction_of_even_a_ge_two
          hn2 heven (by omega) hb hc hd

end Core4loop
