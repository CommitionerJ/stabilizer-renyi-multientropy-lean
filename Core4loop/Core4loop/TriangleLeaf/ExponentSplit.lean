import Core4loop.TriangleLeaf.Exponent

namespace Core4loop

def CompatibleResidualExpZ (a b c d n : ℕ) : ℤ :=
  nPowZ n (a + c + d) + nPowZ n (a + b + d)
  - mZ n * (nPowZ n (c + d) + nPowZ n (a + d) + nPowZ n (b + d))
  + (mZ n) ^ 2 * (nPowZ n b + nPowZ n c)
  + ThetaZ (a + d) b c n * (nPowZ n d - mZ n)

def PassiveVisibleDimZ (d n : ℕ) : ℤ :=
  nPowZ n d - mZ n

def LeafProfileDimZ (a d n : ℕ) : ℤ :=
  nPowZ n (a + d - 1)

def LeafTailUnitZ (b c n : ℕ) : ℤ :=
  (n : ℤ) * (nPowZ n b + nPowZ n c - mZ n)

def LeafVisibleUnitZ (a b c d n : ℕ) : ℤ :=
  LeafTailUnitZ b c n
    - mZ n * (nPowZ n b + nPowZ n c)
    + ThetaZ (a + d) b c n

def CompatibleResidualSplitZ (a b c d n : ℕ) : ℤ :=
  (LeafProfileDimZ a d n - PassiveVisibleDimZ d n) * LeafTailUnitZ b c n
    + PassiveVisibleDimZ d n * LeafVisibleUnitZ a b c d n

def TriangleLeafAfterWKernelExpZ (a b c _d n : ℕ) : ℤ :=
  nPowZ n (a + b + c) - mZ n * nPowZ n (b + c)

theorem CompatibleResidualSplitZ_eq_CompatibleResidualExpZ
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    CompatibleResidualSplitZ a b c d n =
      CompatibleResidualExpZ a b c d n := by
  have hAD :
      nPowZ n (a + d) = LeafProfileDimZ a d n * (n : ℤ) := by
    unfold LeafProfileDimZ
    calc
      nPowZ n (a + d) = nPowZ n (a + d - 1 + 1) := by
        congr 1
        omega
      _ = nPowZ n (a + d - 1) * (n : ℤ) := nPowZ_succ n (a + d - 1)
  have hABD :
      nPowZ n (a + b + d) =
        LeafProfileDimZ a d n * (n : ℤ) * nPowZ n b := by
    calc
      nPowZ n (a + b + d) = nPowZ n ((a + d) + b) := by
        congr 1
        omega
      _ = nPowZ n (a + d) * nPowZ n b := nPowZ_add n (a + d) b
      _ = LeafProfileDimZ a d n * (n : ℤ) * nPowZ n b := by rw [hAD]
  have hACD :
      nPowZ n (a + c + d) =
        LeafProfileDimZ a d n * (n : ℤ) * nPowZ n c := by
    calc
      nPowZ n (a + c + d) = nPowZ n ((a + d) + c) := by
        congr 1
        omega
      _ = nPowZ n (a + d) * nPowZ n c := nPowZ_add n (a + d) c
      _ = LeafProfileDimZ a d n * (n : ℤ) * nPowZ n c := by rw [hAD]
  have hBD :
      nPowZ n (b + d) = nPowZ n b * nPowZ n d := by
    rw [nPowZ_add]
  have hCD :
      nPowZ n (c + d) = nPowZ n c * nPowZ n d := by
    rw [nPowZ_add]
  unfold CompatibleResidualSplitZ CompatibleResidualExpZ PassiveVisibleDimZ
    LeafVisibleUnitZ LeafTailUnitZ
  rw [hABD, hACD, hBD, hCD, hAD]
  ring_nf

theorem CompatibleResidualExpZ_d_eq_one
    {n a b c : ℕ} [NeZero n] :
    CompatibleResidualExpZ a b c 1 n =
      XtriangleZ (a + 1) b c n - nPowZ n (b + c) := by
  unfold CompatibleResidualExpZ XtriangleZ nPowZ mZ
  ring_nf

theorem X1Z_eq_afterW_plus_compatible
    {n a b c d : ℕ} [NeZero n] :
    X1Z a b c d n =
      nPowZ n (b + c + d)
      + TriangleLeafAfterWKernelExpZ a b c d n
      + CompatibleResidualExpZ a b c d n := by
  unfold X1Z Sigma1Z Sigma2_1Z TriangleLeafAfterWKernelExpZ
    CompatibleResidualExpZ
  ring

end Core4loop
