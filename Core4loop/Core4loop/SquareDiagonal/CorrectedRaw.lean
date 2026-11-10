import Core4loop.SquareDiagonal.CorrectedExponent
import Core4loop.SquareDiagonal.SingletonLC.FiniteTransform
import Core4loop.TriangleLeaf.CorrectedFacade

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal

noncomputable section

attribute [local instance] Fintype.ofFinite

theorem DeltaNF_squareDiagonal_eq_pow_X3CorrectedZ_odd
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : Int) ^ Int.toNat (X3CorrectedZ a b c d n) := by
  rw [DeltaNF_squareDiagonal_eq_preC_kernel_sum]
  rw [card_CFun4 ha]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hsum :
      (∑ x : DiamondPreCSource n a b c d,
          bitSign (diamondPreCQ x)) =
        (2 : Int) ^
          DirectWitt.diamondOddResidualExponent
            (a := a) (b := b) (c := c) (d := d) hn := by
    convert
      DirectWitt.sum_bitSign_diamondPreCQ_eq_pow_of_odd
        hb hc hd hn using 1
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  rw [hsum]
  rw [← pow_add]
  have hexponent :
      n ^ (a + b + d) +
          DirectWitt.diamondOddResidualExponent
            (a := a) (b := b) (c := c) (d := d) hn =
        Int.toNat (X3CorrectedZ a b c d n) := by
    exact
      (Int.toNat_natCast _).symm.trans
        (congrArg Int.toNat
          (diamondOdd_rawExponent_cast_eq_X3CorrectedZ
            ha hb hc hd hn))
  rw [hexponent]

theorem DeltaNF_squareDiagonal_eq_pow_X3CorrectedZ_even_a_one
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .squareDiagonal 1 b c d n =
      (2 : Int) ^ Int.toNat (X3CorrectedZ 1 b c d n) := by
  calc
    DeltaNF .squareDiagonal 1 b c d n =
        DeltaNF .triangleLeaf 1 b d c n :=
      SingletonLC.DeltaNF_squareDiagonal_eq_triangleLeaf_of_a_eq_one
        hn2 rfl hb hc hd
    _ = (2 : Int) ^ Int.toNat (X1CorrectedZ 1 b d c n) :=
      TriangleLeaf.DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ
        hn2 (by norm_num) hb hd hc
    _ = (2 : Int) ^ Int.toNat (X3CorrectedZ 1 b c d n) := by
      rw [X3CorrectedZ_of_even_a_eq_one hn rfl]

theorem DeltaNF_squareDiagonal_eq_pow_X3CorrectedZ_even_P
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : Int) ^ Int.toNat (X3CorrectedZ a b c d n) := by
  rw [DeltaNF_squareDiagonal_eq_preC_kernel_sum]
  rw [card_CFun4 (by omega)]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [EvenP.diamondEvenP_sum_eq_pow_residual hn ha2]
  rw [← pow_add]
  have hexponent :
      n ^ (a + b + d) +
          EvenP.diamondEvenPResidualExponent n a b c d =
        Int.toNat (X3CorrectedZ a b c d n) := by
    exact
      (Int.toNat_natCast _).symm.trans
        (congrArg Int.toNat
          (diamondEvenP_rawExponent_cast_eq_X3CorrectedZ
            hn2 hn ha2 hb hc hd))
  rw [hexponent]

end

end Core4loop.SquareDiagonal
