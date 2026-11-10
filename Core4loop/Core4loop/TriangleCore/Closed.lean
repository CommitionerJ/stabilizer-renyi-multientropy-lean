import Core4loop.TriangleCore.Parity
import Core4loop.TriangleCore.Core3Bridge

namespace Core4loop
namespace TriangleCore

lemma pred_mul_pow_le_pair_pow
    {n r s : ℕ} [NeZero n] (hs : 0 < s) :
    (n - 1) * n ^ r ≤ n ^ (r + s) := by
  have hm : n - 1 ≤ n ^ s := by
    have hns : n ≤ n ^ s := Nat.le_pow hs
    omega
  calc
    (n - 1) * n ^ r ≤ n ^ s * n ^ r := Nat.mul_le_mul_right (n ^ r) hm
    _ = n ^ (r + s) := by
      rw [mul_comm, ← Nat.pow_add]

lemma pred_mul_three_pows_le_pair_sum
    {n r s t : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    (n - 1) * (n ^ r + n ^ s + n ^ t) ≤
      n ^ (r + s) + n ^ (r + t) + n ^ (s + t) := by
  have h1 : (n - 1) * n ^ r ≤ n ^ (r + s) :=
    pred_mul_pow_le_pair_pow (n := n) (r := r) (s := s) hs
  have h2 : (n - 1) * n ^ s ≤ n ^ (s + t) :=
    pred_mul_pow_le_pair_pow (n := n) (r := s) (s := t) ht
  have h3 : (n - 1) * n ^ t ≤ n ^ (r + t) := by
    simpa [Nat.add_comm] using
      pred_mul_pow_le_pair_pow (n := n) (r := t) (s := r) hr
  calc
    (n - 1) * (n ^ r + n ^ s + n ^ t)
        = (n - 1) * n ^ r + (n - 1) * n ^ s + (n - 1) * n ^ t := by
            ring
    _ ≤ n ^ (r + s) + n ^ (s + t) + n ^ (r + t) := by
            omega
    _ = n ^ (r + s) + n ^ (r + t) + n ^ (s + t) := by
            ring

lemma two_mul_n_le_pow_sum
    {n r s t : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    2 * n ≤ n ^ r + n ^ s + n ^ t := by
  have hR : n ≤ n ^ r := Nat.le_pow hr
  have hS : n ≤ n ^ s := Nat.le_pow hs
  have hT : n ≤ n ^ t := Nat.le_pow ht
  omega

lemma three_mul_n_le_pow_sum
    {n r s t : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    3 * n ≤ n ^ r + n ^ s + n ^ t := by
  have hR : n ≤ n ^ r := Nat.le_pow hr
  have hS : n ≤ n ^ s := Nat.le_pow hs
  have hT : n ≤ n ^ t := Nat.le_pow ht
  omega

lemma generic_triangle_subtrahend_le_pair_sum
    {n r s t : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    (n - 1) * (n ^ r + n ^ s + n ^ t - 2 * n + 1) ≤
      n ^ (r + s) + n ^ (r + t) + n ^ (s + t) := by
  have hinner :
      n ^ r + n ^ s + n ^ t - 2 * n + 1 ≤ n ^ r + n ^ s + n ^ t := by
    have hA : 2 * n ≤ n ^ r + n ^ s + n ^ t :=
      two_mul_n_le_pow_sum (n := n) (r := r) (s := s) (t := t) hr hs ht
    have hone : 1 ≤ 2 * n := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      omega
    calc
      n ^ r + n ^ s + n ^ t - 2 * n + 1
          ≤ n ^ r + n ^ s + n ^ t - 2 * n + 2 * n := by
              exact Nat.add_le_add_left hone (n ^ r + n ^ s + n ^ t - 2 * n)
      _ = n ^ r + n ^ s + n ^ t := by
              exact Nat.sub_add_cancel hA
  exact le_trans (Nat.mul_le_mul_left (n - 1) hinner)
    (pred_mul_three_pows_le_pair_sum (n := n) (r := r) (s := s) (t := t) hr hs ht)

lemma evenSpecial_triangle_subtrahend_le_pair_sum
    {n r s t : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    (n - 1) * (n ^ r + n ^ s + n ^ t - 3 * n + 3) ≤
      n ^ (r + s) + n ^ (r + t) + n ^ (s + t) := by
  have hinner :
      n ^ r + n ^ s + n ^ t - 3 * n + 3 ≤ n ^ r + n ^ s + n ^ t := by
    have hA : 3 * n ≤ n ^ r + n ^ s + n ^ t :=
      three_mul_n_le_pow_sum (n := n) (r := r) (s := s) (t := t) hr hs ht
    have hthree : 3 ≤ 3 * n := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      omega
    calc
      n ^ r + n ^ s + n ^ t - 3 * n + 3
          ≤ n ^ r + n ^ s + n ^ t - 3 * n + 3 * n := by
              exact Nat.add_le_add_left hthree (n ^ r + n ^ s + n ^ t - 3 * n)
      _ = n ^ r + n ^ s + n ^ t := by
              exact Nat.sub_add_cancel hA
  exact le_trans (Nat.mul_le_mul_left (n - 1) hinner)
    (pred_mul_three_pows_le_pair_sum (n := n) (r := r) (s := s) (t := t) hr hs ht)

lemma genericDeltaExponent_cast_eq_XtriangleZ_of_not_special
    {r s t n : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (h : ¬ specialBranch r s t n) :
    (Core3loop.genericDeltaExponent r s t n : ℤ) =
      XtriangleZ r s t n := by
  have hsub :
      (n - 1) * (n ^ r + n ^ s + n ^ t - 2 * n + 1) ≤
        n ^ (r + s) + n ^ (r + t) + n ^ (s + t) :=
    generic_triangle_subtrahend_le_pair_sum
      (n := n) (r := r) (s := s) (t := t) hr hs ht
  have hinner : 2 * n ≤ n ^ r + n ^ s + n ^ t :=
    two_mul_n_le_pow_sum (n := n) (r := r) (s := s) (t := t) hr hs ht
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  unfold Core3loop.genericDeltaExponent XtriangleZ
  rw [ThetaZ_eq_of_not_special h]
  unfold nPowZ mZ
  rw [Nat.cast_sub hsub]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  rw [Nat.cast_sub hinner]
  rw [Nat.cast_sub hn1]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring_nf

lemma evenSpecialDeltaExponent_cast_eq_XtriangleZ_of_special
    {r s t n : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (h : specialBranch r s t n) :
    (Core3loop.evenSpecialDeltaExponent r s t n : ℤ) =
      XtriangleZ r s t n := by
  have hsub :
      (n - 1) * (n ^ r + n ^ s + n ^ t - 3 * n + 3) ≤
        n ^ (r + s) + n ^ (r + t) + n ^ (s + t) :=
    evenSpecial_triangle_subtrahend_le_pair_sum
      (n := n) (r := r) (s := s) (t := t) hr hs ht
  have hinner : 3 * n ≤ n ^ r + n ^ s + n ^ t :=
    three_mul_n_le_pow_sum (n := n) (r := r) (s := s) (t := t) hr hs ht
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  unfold Core3loop.evenSpecialDeltaExponent XtriangleZ
  rw [ThetaZ_eq_of_special h]
  unfold nPowZ mZ
  rw [Nat.cast_sub hsub]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  rw [Nat.cast_sub hinner]
  rw [Nat.cast_sub hn1]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring_nf

lemma genericDeltaExponent_eq_Xtriangle_of_not_special
    {r s t n : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (h : ¬ specialBranch r s t n) :
    Core3loop.genericDeltaExponent r s t n =
      Int.toNat (XtriangleZ r s t n) := by
  have hcast :=
    genericDeltaExponent_cast_eq_XtriangleZ_of_not_special
      (r := r) (s := s) (t := t) (n := n) hr hs ht h
  have hx : 0 ≤ XtriangleZ r s t n := by
    rw [← hcast]
    exact Int.natCast_nonneg _
  apply Int.ofNat.inj
  change (Core3loop.genericDeltaExponent r s t n : ℤ) =
    (Int.toNat (XtriangleZ r s t n) : ℤ)
  rw [Int.toNat_of_nonneg hx]
  exact hcast

lemma evenSpecialDeltaExponent_eq_Xtriangle_of_special
    {r s t n : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (h : specialBranch r s t n) :
    Core3loop.evenSpecialDeltaExponent r s t n =
      Int.toNat (XtriangleZ r s t n) := by
  have hcast :=
    evenSpecialDeltaExponent_cast_eq_XtriangleZ_of_special
      (r := r) (s := s) (t := t) (n := n) hr hs ht h
  have hx : 0 ≤ XtriangleZ r s t n := by
    rw [← hcast]
    exact Int.natCast_nonneg _
  apply Int.ofNat.inj
  change (Core3loop.evenSpecialDeltaExponent r s t n : ℤ) =
    (Int.toNat (XtriangleZ r s t n) : ℤ)
  rw [Int.toNat_of_nonneg hx]
  exact hcast

theorem DeltaTriangleCore_closed
    {r s t n : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    DeltaTriangleCore r s t n =
      (2 : ℤ) ^ Int.toNat (XtriangleZ r s t n) := by
  rw [DeltaTriangleCore_eq_Core3DeltaABC (r := r) (s := s) (t := t) (n := n) hr hs ht]
  rw [Core3loop.DeltaABC_closed_by_cases_main
    (a := r) (b := s) (c := t) (n := n) hr hs ht]
  by_cases h : specialBranch r s t n
  · rw [if_pos (by simpa [specialBranch] using h)]
    congr 1
    exact evenSpecialDeltaExponent_eq_Xtriangle_of_special
      (r := r) (s := s) (t := t) (n := n) hr hs ht h
  · rw [if_neg (by simpa [specialBranch] using h)]
    congr 1
    exact genericDeltaExponent_eq_Xtriangle_of_not_special
      (r := r) (s := s) (t := t) (n := n) hr hs ht h

end TriangleCore
end Core4loop
