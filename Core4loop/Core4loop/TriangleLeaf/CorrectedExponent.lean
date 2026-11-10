import Core4loop.TriangleLeaf.ExponentSplit
import Core4loop.TriangleCore.Parity

namespace Core4loop

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Frozen exceptional-branch predicate for the corrected paper exponent. -/
def TriangleLeafExceptional (n a b c d : ℕ) : Prop :=
  Even n ∧ a = 1 ∧ 2 ≤ b ∧ 2 ≤ c ∧ 2 ≤ d

/-- Frozen correction term; it is supported only on the exceptional branch. -/
def TriangleLeafCorrectionZ (a b c d n : ℕ) : ℤ :=
  if TriangleLeafExceptional n a b c d then
    mZ n * ((n : ℤ) - 2) *
      (nPowZ n d - 2 * mZ n)
  else 0

/-- Frozen historical copy of the audited current `X1Z` body. -/
def X1PaperOldZ (a b c d n : ℕ) : ℤ :=
  Sigma1Z a b c d n
    - mZ n * Sigma2_1Z a b c d n
    + (mZ n) ^ 2 * (nPowZ n b + nPowZ n c)
    + ThetaZ (a + d) b c n * (nPowZ n d - mZ n)

theorem X1PaperOldZ_eq_current_X1Z
    (a b c d n : ℕ) :
    X1PaperOldZ a b c d n = X1Z a b c d n := by
  unfold X1PaperOldZ X1Z
  rfl

/-- Corrected paper-facing exponent, without changing the production `X1Z`. -/
def X1CorrectedZ (a b c d n : ℕ) : ℤ :=
  X1PaperOldZ a b c d n -
    TriangleLeafCorrectionZ a b c d n

/-- Natural exceptional residual exponent proved in Round 6. -/
def TriangleLeafExceptionalResidualExpNat
    (b c d n : ℕ) : ℕ :=
  (n ^ d - (n - 1)) * (n ^ b + n ^ c + (n - 1) ^ 2)
    + (n - 1) * (n ^ (b + 1) + n ^ (c + 1))
    - 2 * (n - 1) ^ 2

theorem correctionZ_exceptional
    {n b c d : ℕ}
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TriangleLeafCorrectionZ 1 b c d n
      =
    mZ n * ((n : ℤ) - 2) *
      (nPowZ n d - 2 * mZ n) := by
  unfold TriangleLeafCorrectionZ
  rw [if_pos]
  exact ⟨hn, rfl, hb2, hc2, hd2⟩

theorem correctionZ_nonexceptional
    {n a b c d : ℕ}
    (h : ¬ TriangleLeafExceptional n a b c d) :
    TriangleLeafCorrectionZ a b c d n = 0 := by
  simp [TriangleLeafCorrectionZ, h]

/-- Closed corrected exponent on the exceptional branch.  The only parity
simplification is the production TriangleCore theorem. -/
theorem X1CorrectedZ_exceptional_closed
    {n b c d : ℕ}
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    X1CorrectedZ 1 b c d n
      =
    nPowZ n (b + c + d)
      + nPowZ n (b + c)
      + nPowZ n (b + d)
      + nPowZ n (c + d)
      + (mZ n) ^ 2 *
          (nPowZ n b + nPowZ n c + nPowZ n d - (n : ℤ) - 1) := by
  have hd : 0 < d := by omega
  unfold X1CorrectedZ X1PaperOldZ TriangleLeafCorrectionZ
  rw [if_pos
    (show TriangleLeafExceptional n 1 b c d from
      ⟨hn, rfl, hb2, hc2, hd2⟩)]
  unfold Sigma1Z Sigma2_1Z
  rw [TriangleCore.ThetaZ_triangleLeaf_eq_of_even_large
    (a := 1) (b := b) (c := c) (d := d) (n := n)
    (by omega) hd hn hb2 hc2]
  simp only [nPowZ, mZ, pow_add, pow_one]
  ring

private theorem TriangleLeafExceptionalResidualExpNat_cast
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) :
    (TriangleLeafExceptionalResidualExpNat b c d n : ℤ)
      =
    (nPowZ n d - mZ n) *
        (nPowZ n b + nPowZ n c + (mZ n) ^ 2)
      +
      mZ n * (nPowZ n (b + 1) + nPowZ n (c + 1))
      -
      2 * (mZ n) ^ 2 := by
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  have hn2 : 2 ≤ n := by
    rcases hn with ⟨k, hk⟩
    omega
  have hnpos : 0 < n := by omega
  have hpowD : n ^ 2 ≤ n ^ d :=
    Nat.pow_le_pow_right hnpos hd2
  have hsq : n + 1 ≤ n ^ 2 := by
    nlinarith
  have hpowLower : n + 1 ≤ n ^ d :=
    le_trans hsq hpowD
  have hVsub : n - 1 ≤ n ^ d := by
    omega
  have hVtwo : 2 ≤ n ^ d - (n - 1) := by
    omega
  have hP :
      (n - 1) ^ 2
        ≤
      n ^ b + n ^ c + (n - 1) ^ 2 := by
    omega
  have hRsource :
      2 * (n - 1) ^ 2
        ≤
      (n ^ d - (n - 1)) *
        (n ^ b + n ^ c + (n - 1) ^ 2) := by
    calc
      2 * (n - 1) ^ 2
          ≤
        (n ^ d - (n - 1)) * (n - 1) ^ 2 :=
          Nat.mul_le_mul_right ((n - 1) ^ 2) hVtwo
      _ ≤
        (n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2) :=
            Nat.mul_le_mul_left (n ^ d - (n - 1)) hP
  have hRtotal :
      2 * (n - 1) ^ 2
        ≤
      (n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2)
        +
        (n - 1) * (n ^ (b + 1) + n ^ (c + 1)) := by
    omega
  unfold TriangleLeafExceptionalResidualExpNat
  rw [Nat.cast_sub hRtotal]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_sub hVsub, Nat.cast_sub hn1]
  unfold nPowZ mZ
  ring

/-- Cast bridge from the natural front plus exceptional residual exponent to
the independently derived corrected integer exponent. -/
theorem exceptional_residual_plus_front_eq_X1CorrectedZ
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    ((n ^ (b + c + d) + n ^ (b + c)
        + TriangleLeafExceptionalResidualExpNat b c d n : ℕ) : ℤ)
      =
    X1CorrectedZ 1 b c d n := by
  rw [X1CorrectedZ_exceptional_closed hn hb2 hc2 hd2]
  rw [Nat.cast_add, Nat.cast_add]
  rw [TriangleLeafExceptionalResidualExpNat_cast hn hd2]
  simp only [Nat.cast_mul, Nat.cast_pow, nPowZ, mZ, pow_add, pow_one]
  ring

end

end Core4loop
