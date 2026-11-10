import Core4loop.Phase

namespace Core4loop

def Sigma1Z (a b c d n : ℕ) : ℤ :=
  nPowZ n (b + c + d) + nPowZ n (a + c + d) +
  nPowZ n (a + b + d) + nPowZ n (a + b + c)

def Sigma2_1Z (a b c d n : ℕ) : ℤ :=
  nPowZ n (c + d) + nPowZ n (a + d) +
  nPowZ n (b + d) + nPowZ n (b + c)

def Sigma2_2Z (a b c d n : ℕ) : ℤ :=
  nPowZ n (c + d) + nPowZ n (a + d) +
  nPowZ n (a + b) + nPowZ n (b + c)

def Sigma2_3Z (a b c d n : ℕ) : ℤ :=
  nPowZ n (c + d) + nPowZ n (a + d) +
  nPowZ n (a + b) + nPowZ n (b + c) + nPowZ n (b + d)

def Sigma2_4Z (a b c d n : ℕ) : ℤ :=
  nPowZ n (c + d) + nPowZ n (b + d) + nPowZ n (b + c) +
  nPowZ n (a + d) + nPowZ n (a + c) + nPowZ n (a + b)

def SectorExpZ (r s t passive n : ℕ) : ℤ :=
  ThetaZ r s t n * (nPowZ n passive - mZ n)

def OverlapG3Z (n : ℕ) : ℤ := (mZ n) ^ 3

def OverlapG4Z (n : ℕ) : ℤ :=
  5 * (mZ n) ^ 3 + (mZ n) ^ 2 - mZ n

def SquareRankZ (a b c d n : ℕ) : ℤ :=
  mZ n * Sigma2_2Z a b c d n
  - (mZ n) ^ 2 *
      (nPowZ n a + nPowZ n b + nPowZ n c + nPowZ n d)
  - mZ n + 2 * (mZ n) ^ 3

/-- Historical pre-erratum TriangleLeaf exponent. It is retained for
compatibility and for proved restricted/nonexceptional uses, but it is not
the canonical target for the arbitrary-positive TriangleLeaf theorem.
After importing `Core4loop.TriangleLeaf.CorrectedExponent`, use
`X1CorrectedZ`; import `Core4loop.TriangleLeaf.CorrectedFacade` for the
final public theorem. -/
def X1Z (a b c d n : ℕ) : ℤ :=
  Sigma1Z a b c d n
  - mZ n * Sigma2_1Z a b c d n
  + (mZ n) ^ 2 * (nPowZ n b + nPowZ n c)
  + ThetaZ (a + d) b c n * (nPowZ n d - mZ n)

def X2Z (a b c d n : ℕ) : ℤ :=
  Sigma1Z a b c d n
  - mZ n * Sigma2_2Z a b c d n
  + (mZ n) ^ 2 *
      (nPowZ n a + nPowZ n b + nPowZ n c + nPowZ n d)
  + mZ n - 2 * (mZ n) ^ 3

def X3Z (a b c d n : ℕ) : ℤ :=
  Sigma1Z a b c d n
  - mZ n * Sigma2_3Z a b c d n
  + (mZ n) ^ 2 * (nPowZ n a + nPowZ n c)
  + ThetaZ a b c n * (nPowZ n d - mZ n)
  + ThetaZ a c d n * (nPowZ n b - mZ n)
  + (mZ n) ^ 3

def X4Z (a b c d n : ℕ) : ℤ :=
  Sigma1Z a b c d n
  - mZ n * Sigma2_4Z a b c d n
  + ThetaZ a b c n * (nPowZ n d - mZ n)
  + ThetaZ a b d n * (nPowZ n c - mZ n)
  + ThetaZ a c d n * (nPowZ n b - mZ n)
  + ThetaZ b c d n * (nPowZ n a - mZ n)
  + 5 * (mZ n) ^ 3 + (mZ n) ^ 2 - mZ n

/-- Historical natural wrapper `Int.toNat (X1Z ...)`. It is not the
canonical arbitrary-positive TriangleLeaf exponent. Use
`Int.toNat (X1CorrectedZ ...)` after importing the corrected exponent
module; no `X1Corrected : ℕ` alias is defined. -/
def X1 (a b c d n : ℕ) : ℕ := Int.toNat (X1Z a b c d n)
def X2 (a b c d n : ℕ) : ℕ := Int.toNat (X2Z a b c d n)
def X3 (a b c d n : ℕ) : ℕ := Int.toNat (X3Z a b c d n)
def X4 (a b c d n : ℕ) : ℕ := Int.toNat (X4Z a b c d n)

theorem X2Z_eq_Sigma1_sub_SquareRankZ (a b c d n : ℕ) :
    X2Z a b c d n = Sigma1Z a b c d n - SquareRankZ a b c d n := by
  unfold X2Z SquareRankZ Sigma1Z Sigma2_2Z nPowZ mZ
  ring

theorem X3Z_sector_formula (a b c d n : ℕ) :
    X3Z a b c d n =
      Sigma1Z a b c d n
      - mZ n * Sigma2_3Z a b c d n
      + (mZ n) ^ 2 * (nPowZ n a + nPowZ n c)
      + SectorExpZ a b c d n
      + SectorExpZ a c d b n
      + OverlapG3Z n := by
  unfold X3Z SectorExpZ OverlapG3Z
  ring

theorem X4Z_sector_formula (a b c d n : ℕ) :
    X4Z a b c d n =
      Sigma1Z a b c d n
      - mZ n * Sigma2_4Z a b c d n
      + SectorExpZ a b c d n
      + SectorExpZ a b d c n
      + SectorExpZ a c d b n
      + SectorExpZ b c d a n
      + OverlapG4Z n := by
  unfold X4Z SectorExpZ OverlapG4Z
  ring

lemma passiveTransfer_nonneg {passive n : ℕ} [NeZero n] (hp : 0 < passive) :
    0 ≤ nPowZ n passive - mZ n :=
  nPowZ_sub_mZ_nonneg hp

lemma OverlapG3Z_nonneg {n : ℕ} [NeZero n] :
    0 ≤ OverlapG3Z n := by
  unfold OverlapG3Z
  exact pow_nonneg (mZ_nonneg (n := n)) 3

end Core4loop
