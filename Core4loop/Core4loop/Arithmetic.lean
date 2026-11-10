import Core4loop.Sign

namespace Core4loop

def mZ (n : ℕ) : ℤ := (n : ℤ) - 1

def nPowZ (n e : ℕ) : ℤ := (n : ℤ) ^ e

def ThetaZ (r s t n : ℕ) : ℤ :=
  let m : ℤ := mZ n
  if Even n ∧ 2 ≤ r ∧ 2 ≤ s ∧ 2 ≤ t then
    3 * m ^ 2
  else
    m * (2 * (n : ℤ) - 1)

def Theta (r s t n : ℕ) : ℕ := Int.toNat (ThetaZ r s t n)

def XtriangleZ (r s t n : ℕ) : ℤ :=
  nPowZ n (r + s) + nPowZ n (r + t) + nPowZ n (s + t)
  - mZ n * (nPowZ n r + nPowZ n s + nPowZ n t)
  + ThetaZ r s t n

def Xtriangle (r s t n : ℕ) : ℕ := Int.toNat (XtriangleZ r s t n)

lemma mZ_nonneg {n : ℕ} [NeZero n] : 0 ≤ mZ n := by
  unfold mZ
  have hn : (1 : ℤ) ≤ n := by
    exact_mod_cast (one_le_of_neZero (n := n))
  omega

lemma nPowZ_nonneg (n e : ℕ) : 0 ≤ nPowZ n e := by
  unfold nPowZ
  positivity

lemma two_mul_n_sub_one_nonneg {n : ℕ} [NeZero n] :
    0 ≤ (2 * (n : ℤ) - 1) := by
  have hn : (1 : ℤ) ≤ n := by
    exact_mod_cast (one_le_of_neZero (n := n))
  omega

lemma ThetaZ_nonneg {r s t n : ℕ} [NeZero n] :
    0 ≤ ThetaZ r s t n := by
  unfold ThetaZ
  by_cases h : Even n ∧ 2 ≤ r ∧ 2 ≤ s ∧ 2 ≤ t
  · simp only [h]
    change 0 ≤ 3 * (mZ n) ^ 2
    positivity
  · simp only [h, if_false]
    exact mul_nonneg (mZ_nonneg (n := n)) (two_mul_n_sub_one_nonneg (n := n))

lemma nPowZ_sub_mZ_nonneg {n k : ℕ} [NeZero n] (hk : 0 < k) :
    0 ≤ nPowZ n k - mZ n := by
  unfold nPowZ mZ
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  have hnk : n ≤ n ^ k := Nat.le_pow hk
  have hnkZ : (n : ℤ) ≤ (n : ℤ) ^ k := by
    exact_mod_cast hnk
  omega

lemma Int_toNat_add_of_nonneg {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Int.toNat (x + y) = Int.toNat x + Int.toNat y := by
  apply Int.ofNat.inj
  change ((Int.toNat (x + y) : ℕ) : ℤ) =
    ((Int.toNat x + Int.toNat y : ℕ) : ℤ)
  rw [Nat.cast_add]
  rw [Int.toNat_of_nonneg (add_nonneg hx hy)]
  rw [Int.toNat_of_nonneg hx]
  rw [Int.toNat_of_nonneg hy]

lemma nPowZ_add (n e₁ e₂ : ℕ) :
    nPowZ n (e₁ + e₂) = nPowZ n e₁ * nPowZ n e₂ := by
  simp [nPowZ, pow_add]

lemma nPowZ_succ (n k : ℕ) :
    nPowZ n (k + 1) = nPowZ n k * (n : ℤ) := by
  simp [nPowZ, pow_add]

end Core4loop
