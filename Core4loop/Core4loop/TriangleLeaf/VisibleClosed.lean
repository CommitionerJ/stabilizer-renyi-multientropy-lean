import Core4loop.TriangleLeaf.CanonicalVisibleBaseSign

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

local instance instDecidableEqPassiveVisibleIndexClosed
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    DecidableEq (PassiveVisibleIndex n d hd) :=
  Classical.decEq _

private theorem intCast_passiveVisibleNat_eq
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    ((n ^ d - (n - 1) : ℕ) : ℤ) = PassiveVisibleDimZ d n := by
  have hle : n - 1 ≤ n ^ d := by
    have hnle : n ≤ n ^ d := Nat.le_pow hd
    exact Nat.le_trans (Nat.sub_le n 1) hnle
  unfold PassiveVisibleDimZ nPowZ mZ
  rw [Nat.cast_sub hle]
  simp only [Nat.cast_pow]
  have hpred : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    have hn : 1 ≤ n := one_le_of_neZero
    omega
  rw [hpred]

private theorem intCast_genericScalarVisibleNat_eq
    {n b c : ℕ} [NeZero n] :
    ((n ^ b + n ^ c + (n - 1) ^ 2 : ℕ) : ℤ) =
      nPowZ n b + nPowZ n c + (mZ n) ^ 2 := by
  unfold nPowZ mZ
  simp only [Nat.cast_add, Nat.cast_pow]
  have hpred : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    have hn : 1 ≤ n := one_le_of_neZero
    omega
  rw [hpred]

private theorem intToNat_visible_generic_product_eq
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Int.toNat
        (PassiveVisibleDimZ d n *
          (nPowZ n b + nPowZ n c + (mZ n) ^ 2))
      =
      (n ^ d - (n - 1)) * (n ^ b + n ^ c + (n - 1) ^ 2) := by
  have hvisible := intCast_passiveVisibleNat_eq (n := n) (d := d) hd
  have hunit := intCast_genericScalarVisibleNat_eq (n := n) (b := b) (c := c)
  have hprod :
      PassiveVisibleDimZ d n *
          (nPowZ n b + nPowZ n c + (mZ n) ^ 2)
        =
        (((n ^ d - (n - 1)) * (n ^ b + n ^ c + (n - 1) ^ 2) : ℕ) : ℤ) := by
    rw [← hvisible, ← hunit, Nat.cast_mul]
  rw [hprod]
  exact Int.toNat_natCast _

private theorem two_le_of_even_neZero {n : ℕ} [NeZero n] (hn : Even n) :
    2 ≤ n := by
  rcases hn with ⟨k, hk⟩
  have hn1 : 1 ≤ n := one_le_of_neZero
  omega

private theorem four_mul_le_even_scalar_large
    {n b c : ℕ} [NeZero n] (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    4 * n ≤ n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 := by
  have hn1 : 1 ≤ n := one_le_of_neZero
  have hn2 : 2 ≤ n := two_le_of_even_neZero (n := n) hn
  have hbpow : n ^ 2 ≤ n ^ b := Nat.pow_le_pow_right hn1 hb2
  have hcpow : n ^ 2 ≤ n ^ c := Nat.pow_le_pow_right hn1 hc2
  have hsq : 2 * n ≤ n ^ 2 := by
    nlinarith [sq_nonneg (n : ℤ)]
  omega

private theorem intCast_evenScalarBlockLargeNat_eq
    {n b c : ℕ} [NeZero n] (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3 : ℕ) : ℤ)
      =
      nPowZ n (b + 1) + nPowZ n (c + 1) + nPowZ n b + nPowZ n c
        + nPowZ n 2 - 4 * (n : ℤ) + 3 := by
  have hle := four_mul_le_even_scalar_large
    (n := n) (b := b) (c := c) hn hb2 hc2
  unfold nPowZ
  rw [Nat.cast_add]
  rw [Nat.cast_sub hle]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]

private theorem intCast_evenScalarBlockMinNat_eq
    {n b c : ℕ} [NeZero n] (hb : 0 < b) :
    ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1 : ℕ) : ℤ)
      =
      nPowZ n (b + 1) + nPowZ n (c + 1) + nPowZ n b + nPowZ n c
        - (n : ℤ) + 1 := by
  have hn1 : 1 ≤ n := one_le_of_neZero
  have hbpow : n ≤ n ^ b := by
    have h := Nat.pow_le_pow_right hn1 hb
    simpa [pow_one] using h
  have hle : n ≤ n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c := by
    omega
  unfold nPowZ
  rw [Nat.cast_add]
  rw [Nat.cast_sub hle]
  simp only [Nat.cast_add, Nat.cast_pow]
  norm_num

private theorem intToNat_visible_even_large_product_eq
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d)
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    Int.toNat
        (PassiveVisibleDimZ d n *
          (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n))
      =
      (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3)
        * (n ^ d - (n - 1)) := by
  let scalarNat :=
    n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3
  let visibleNat := n ^ d - (n - 1)
  have hvisible := intCast_passiveVisibleNat_eq (n := n) (d := d) hd
  have hscalarNat := intCast_evenScalarBlockLargeNat_eq
    (n := n) (b := b) (c := c) hn hb2 hc2
  have hscalarZ :=
    LeafTailUnitZ_add_LeafVisibleUnitZ_eq_evenScalarBlockExpZ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hd hn hb2 hc2
  have hprod :
      PassiveVisibleDimZ d n *
          (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n)
        =
        ((scalarNat * visibleNat : ℕ) : ℤ) := by
    rw [hscalarZ, ← hvisible, ← hscalarNat]
    change ((visibleNat : ℤ) * (scalarNat : ℤ)) =
      ((scalarNat * visibleNat : ℕ) : ℤ)
    rw [Nat.cast_mul]
    ring
  rw [hprod]
  exact Int.toNat_natCast _

private theorem intToNat_visible_even_min_product_eq
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hgeneric : ¬ (Even n ∧ 2 ≤ b ∧ 2 ≤ c)) :
    Int.toNat
        (PassiveVisibleDimZ d n *
          (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n))
      =
      (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1)
        * (n ^ d - (n - 1)) := by
  let scalarNat := n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1
  let visibleNat := n ^ d - (n - 1)
  have hvisible := intCast_passiveVisibleNat_eq (n := n) (d := d) hd
  have hscalarNat := intCast_evenScalarBlockMinNat_eq
    (n := n) (b := b) (c := c) hb
  have hscalarZ :=
    LeafTailUnitZ_add_LeafVisibleUnitZ_eq_genericEvenScalarBlockExpZ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hd hgeneric
  have hprod :
      PassiveVisibleDimZ d n *
          (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n)
        =
        ((scalarNat * visibleNat : ℕ) : ℤ) := by
    rw [hscalarZ, ← hvisible, ← hscalarNat]
    change ((visibleNat : ℤ) * (scalarNat : ℤ)) =
      ((scalarNat * visibleNat : ℕ) : ℤ)
    rw [Nat.cast_mul]
    ring
  rw [hprod]
  exact Int.toNat_natCast _

theorem triangleLeaf_visible_sum_closed_odd
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n) :
    (∑ H : LeafVisibleKernel n b c d,
      leafVisibleCanonicalBaseSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      =
      (2 : ℤ) ^
        Int.toNat (PassiveVisibleDimZ d n * LeafVisibleUnitZ a b c d n) := by
  have hnotEven : ¬ Even n := by
    intro he
    rcases hn with ⟨k, hk⟩
    rcases he with ⟨l, hl⟩
    omega
  have hgeneric : ¬ (Even n ∧ 2 ≤ b ∧ 2 ≤ c) := by
    intro h
    exact hnotEven h.1
  calc
    (∑ H : LeafVisibleKernel n b c d,
      leafVisibleCanonicalBaseSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        =
        (2 : ℤ) ^ ((n ^ b + n ^ c + (n - 1) ^ 2) * (n ^ d - (n - 1))) := by
          exact sum_leafVisibleCanonicalBaseSign_eq_closed_form_of_odd
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hn
    _ =
        (2 : ℤ) ^
          Int.toNat (PassiveVisibleDimZ d n * LeafVisibleUnitZ a b c d n) := by
          rw [LeafVisibleUnitZ_eq_genericScalarVisibleExpZ
            (n := n) (a := a) (b := b) (c := c) (d := d) ha hd hgeneric]
          rw [intToNat_visible_generic_product_eq (n := n) (b := b) (c := c) (d := d) hd]
          rw [Nat.mul_comm]

theorem triangleLeaf_even_block_sum_closed_all_ge_two
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X)
      =
      (2 : ℤ) ^
        Int.toNat
          (PassiveVisibleDimZ d n *
            (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n)) := by
  calc
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X)
        =
        (2 : ℤ) ^
          ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3)
            * (n ^ d - (n - 1))) := by
          exact sum_leafEvenBlockProductSign_eq_closed_form_all_ge_two
            (n := n) (b := b) (c := c) (d := d) hd hn hb2 hc2
    _ =
        (2 : ℤ) ^
          Int.toNat
            (PassiveVisibleDimZ d n *
              (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n)) := by
          rw [intToNat_visible_even_large_product_eq
            (n := n) (a := a) (b := b) (c := c) (d := d)
            ha hd hn hb2 hc2]

theorem triangleLeaf_even_block_sum_closed_min_eq_one
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Even n)
    (hdeg : b = 1 ∨ c = 1) :
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X)
      =
      (2 : ℤ) ^
        Int.toNat
          (PassiveVisibleDimZ d n *
            (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n)) := by
  have hgeneric : ¬ (Even n ∧ 2 ≤ b ∧ 2 ≤ c) := by
    intro h
    rcases hdeg with hdeg | hdeg
    · omega
    · omega
  calc
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X)
        =
        (2 : ℤ) ^
          ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1)
            * (n ^ d - (n - 1))) := by
          exact sum_leafEvenBlockProductSign_eq_closed_form_min_eq_one
            (n := n) (b := b) (c := c) (d := d) hb hc hd hn hdeg
    _ =
        (2 : ℤ) ^
          Int.toNat
            (PassiveVisibleDimZ d n *
              (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n)) := by
          rw [intToNat_visible_even_min_product_eq
            (n := n) (a := a) (b := b) (c := c) (d := d)
            ha hb hd hgeneric]

theorem triangleLeaf_even_block_sum_closed_generic
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Even n)
    (hgeneric : ¬ (Even n ∧ 2 ≤ b ∧ 2 ≤ c)) :
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X)
      =
      (2 : ℤ) ^
        Int.toNat
          (PassiveVisibleDimZ d n *
            (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n)) := by
  have hdeg : b = 1 ∨ c = 1 := by
    by_cases hb2 : 2 ≤ b
    · right
      have hcnot : ¬ 2 ≤ c := by
        intro hc2
        exact hgeneric ⟨hn, hb2, hc2⟩
      omega
    · left
      omega
  exact triangleLeaf_even_block_sum_closed_min_eq_one
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hb hc hd hn hdeg

end

end TriangleLeaf
end Core4loop
