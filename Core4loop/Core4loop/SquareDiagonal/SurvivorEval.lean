import Core4loop.Gauss.SurvivorSum
import Core4loop.LinearSignSum
import Core4loop.RootSpaces.KernelRank
import Core4loop.ZeroSumSpaces.ProfileMRange
import Core4loop.SquareDiagonal.TerminalCertificate

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable def X3AfterAZ (a b c d n : ℕ) : ℤ :=
  X3Z a b c d n - nPowZ n (b + c + d)

lemma Q3_eq_Q2
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    Q3 B C W = Q2 B C W := by
  rfl

lemma rootExp_toNat (n b c d : ℕ) :
    Int.toNat (nPowZ n (b + c + d)) = n ^ (b + c + d) := by
  unfold nPowZ
  have hpow :
      (n : ℤ) ^ (b + c + d) = ((n ^ (b + c + d) : ℕ) : ℤ) :=
    (Nat.cast_pow n (b + c + d)).symm
  rw [hpow]
  exact Int.toNat_natCast _

lemma X3AfterAZ_eq_support_afterA (a b c d n : ℕ) :
    X3AfterAZ a b c d n =
      supportSumZ a b c d n - nPowZ n (b + c + d) := by
  unfold X3AfterAZ
  rw [supportSumZ_eq_X3Z]

lemma X3Z_eq_rootExp_add_X3AfterAZ (a b c d n : ℕ) :
    X3Z a b c d n =
      nPowZ n (b + c + d) + X3AfterAZ a b c d n := by
  unfold X3AfterAZ
  ring

lemma supportSumZ_toNat_eq_rootExp_add_X3AfterAZ_toNat
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n) :
    Int.toNat (supportSumZ a b c d n) =
      n ^ (b + c + d) + Int.toNat (X3AfterAZ a b c d n) := by
  rw [supportSumZ_eq_X3Z]
  rw [X3Z_eq_rootExp_add_X3AfterAZ]
  rw [Int_toNat_add_of_nonneg
    (nPowZ_nonneg n (b + c + d)) hAfter]
  rw [rootExp_toNat]

theorem DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hsurvivor :
      (∑ x : Surviving_yzw n a b c d,
        bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  calc
    DeltaNF .squareDiagonal a b c d n
        =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
          rw [DeltaNF_squareDiagonal_survivors]
          rw [hsurvivor]
    _ =
      (2 : ℤ) ^ (n ^ (b + c + d) + Int.toNat (X3AfterAZ a b c d n)) := by
        rw [← pow_add]
    _ =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
        rw [supportSumZ_toNat_eq_rootExp_add_X3AfterAZ_toNat
          (n := n) (a := a) (b := b) (c := c) (d := d) hAfter]

theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hsurvivor :
      (∑ x : Surviving_yzw n a b c d,
        bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  rw [← supportSumZ_eq_X3Z]
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d) hAfter hsurvivor

end SquareDiagonal
end Core4loop
