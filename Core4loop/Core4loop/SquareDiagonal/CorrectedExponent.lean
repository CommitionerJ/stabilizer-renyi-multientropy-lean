import Core4loop.SquareDiagonal.DirectWitt.ResidualFinal
import Core4loop.SquareDiagonal.EvenP.ResidualSourceArithmetic
import Core4loop.TriangleLeaf.CorrectedExponent

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

noncomputable section

attribute [local instance] Classical.propDecidable

private def diamondSigma1Nat
    (n a b c d : Nat) : Nat :=
  n ^ (b + c + d) + n ^ (a + c + d) +
    n ^ (a + b + d) + n ^ (a + b + c)

private def diamondPairTermNat
    (n a b d : Nat) : Nat :=
  (n - 1) *
    (n ^ (a + b) + n ^ (a + d) + n ^ (b + d))

private def diamondVertexTermNat
    (n a b d : Nat) : Nat :=
  (n - 1) ^ 2 * (n ^ a + n ^ b + n ^ d)

def X3FromHalfRankZ
    (a b c d n halfRank : Nat) : Int :=
  Sigma1Z a b c d n
    - mZ n *
        (nPowZ n (a + b) +
          nPowZ n (a + d) +
          nPowZ n (b + d))
    + (mZ n) ^ 2 *
        (nPowZ n a + nPowZ n b + nPowZ n d)
    - (mZ n) ^ 3
    - (halfRank : Int)

private def diamondFromHalfRankNatCastZ
    (a b c d n halfRank : Nat) : Int :=
  (diamondSigma1Nat n a b c d : Int) +
      (diamondVertexTermNat n a b d : Int) -
    (diamondPairTermNat n a b d : Int) -
    ((n - 1) ^ 3 : Nat) -
    (halfRank : Int)

private theorem diamondFromHalfRankNatCastZ_eq_X3FromHalfRankZ
    {n a b c d halfRank : Nat} [NeZero n] :
    diamondFromHalfRankNatCastZ a b c d n halfRank =
      X3FromHalfRankZ a b c d n halfRank := by
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  unfold diamondFromHalfRankNatCastZ X3FromHalfRankZ
    diamondSigma1Nat diamondPairTermNat diamondVertexTermNat
    Sigma1Z nPowZ mZ
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub hn1, Nat.cast_one]
  ring

private theorem diamondRawExponent_cast_eq_X3FromHalfRankZ
    {n a b c d residual halfRank : Nat} [NeZero n]
    (h :
      (n ^ (a + b + d) + residual) + halfRank +
            diamondPairTermNat n a b d + (n - 1) ^ 3 =
        diamondSigma1Nat n a b c d +
          diamondVertexTermNat n a b d) :
    ((n ^ (a + b + d) + residual : Nat) : Int) =
      X3FromHalfRankZ a b c d n halfRank := by
  rw [← diamondFromHalfRankNatCastZ_eq_X3FromHalfRankZ]
  have hz :
      ((n ^ (a + b + d) + residual : Nat) : Int) +
            halfRank + diamondPairTermNat n a b d +
            ((n - 1) ^ 3 : Nat) =
        diamondSigma1Nat n a b c d +
          diamondVertexTermNat n a b d := by
    exact_mod_cast h
  unfold diamondFromHalfRankNatCastZ
  omega

noncomputable def X3CorrectedZ
    (a b c d n : Nat) : Int :=
  if Odd n then
    X3FromHalfRankZ a b c d n
      (SquareDiagonal.DirectWitt.diamondOddHalfRank n b c d)
  else if a = 1 then
    X1CorrectedZ a b d c n
  else
    X3FromHalfRankZ a b c d n
      (SquareDiagonal.EvenP.diamondEvenPTotalHalfRank n b c d)

@[simp] theorem X3CorrectedZ_of_odd
    {n a b c d : Nat} (hn : Odd n) :
    X3CorrectedZ a b c d n =
      X3FromHalfRankZ a b c d n
        (SquareDiagonal.DirectWitt.diamondOddHalfRank n b c d) := by
  simp [X3CorrectedZ, hn]

@[simp] theorem X3CorrectedZ_of_even_a_eq_one
    {n a b c d : Nat} (hn : Even n) (ha : a = 1) :
    X3CorrectedZ a b c d n =
      X1CorrectedZ a b d c n := by
  have hnot : ¬ Odd n := Nat.not_odd_iff_even.mpr hn
  simp [X3CorrectedZ, hnot, ha]

@[simp] theorem X3CorrectedZ_of_even_a_ne_one
    {n a b c d : Nat} (hn : Even n) (ha : a ≠ 1) :
    X3CorrectedZ a b c d n =
      X3FromHalfRankZ a b c d n
        (SquareDiagonal.EvenP.diamondEvenPTotalHalfRank n b c d) := by
  have hnot : ¬ Odd n := Nat.not_odd_iff_even.mpr hn
  simp [X3CorrectedZ, hnot, ha]

theorem diamondOdd_rawExponent_cast_eq_X3CorrectedZ
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    ((n ^ (a + b + d) +
        SquareDiagonal.DirectWitt.diamondOddResidualExponent
          (a := a) (b := b) (c := c) (d := d) hn : Nat) : Int) =
      X3CorrectedZ a b c d n := by
  rw [X3CorrectedZ_of_odd hn]
  apply diamondRawExponent_cast_eq_X3FromHalfRankZ
  have hclosed :=
    SquareDiagonal.DirectWitt.diamondOdd_residual_source_closed_addition
      ha hb hc hd hn
  unfold diamondSigma1Nat diamondPairTermNat diamondVertexTermNat
  omega

theorem diamondEvenP_rawExponent_cast_eq_X3CorrectedZ
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ((n ^ (a + b + d) +
        SquareDiagonal.EvenP.diamondEvenPResidualExponent
          n a b c d : Nat) : Int) =
      X3CorrectedZ a b c d n := by
  rw [X3CorrectedZ_of_even_a_ne_one hn (by omega)]
  apply diamondRawExponent_cast_eq_X3FromHalfRankZ
  have hclosed :=
    SquareDiagonal.EvenP.diamondEvenP_residual_source_closed_addition
      hn2 hn ha2 hb hc hd
  unfold diamondSigma1Nat diamondPairTermNat diamondVertexTermNat
  omega

end

end Core4loop
