import Core4loop.SquareDiagonal.CorrectedRaw

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal

theorem DeltaNF_squareDiagonal_eq_pow_X3CorrectedZ
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : Int) ^ Int.toNat (X3CorrectedZ a b c d n) := by
  rcases Nat.even_or_odd n with hn | hn
  · by_cases ha1 : a = 1
    · subst a
      exact
        DeltaNF_squareDiagonal_eq_pow_X3CorrectedZ_even_a_one
          hn2 hn hb hc hd
    · have ha2 : 2 ≤ a := by omega
      exact
        DeltaNF_squareDiagonal_eq_pow_X3CorrectedZ_even_P
          hn2 hn ha2 hb hc hd
  · exact
      DeltaNF_squareDiagonal_eq_pow_X3CorrectedZ_odd
        hn ha hb hc hd

end Core4loop.SquareDiagonal
