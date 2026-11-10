import Core4loop.TriangleLeaf.E6CompatibleSourceRank
import Core4loop.TriangleLeaf.E6RankDomain
import Core4loop.TriangleLeaf.E6SecondCoeffRank
import Core4loop.TriangleLeaf.ExponentSplit
import Core4loop.TriangleCore.Parity

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem finrank_range_coeffCompat_add_finrank_triangleLeafE5LB
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffCompat
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      Module.finrank F (triangleLeafE5LB n a b c d) =
    Module.finrank F
      (triangleLeafCompatibleSubmodule n a b c d) := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafBOnlyPolarMap
        (n := n) (a := a) (b := b) (c := c) (d := d))
  rw [range_triangleLeafBOnlyPolarMap_eq_coeffCompat] at h
  exact h

private theorem intCast_passiveVisibleDim
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    ((n ^ d - (n - 1) : ℕ) : ℤ) = PassiveVisibleDimZ d n := by
  have hle : n - 1 ≤ n ^ d :=
    (Nat.sub_le n 1).trans (Nat.le_pow hd)
  unfold PassiveVisibleDimZ nPowZ mZ
  rw [Nat.cast_sub hle, Nat.cast_pow]
  have hpred : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    have hn : 1 ≤ n := one_le_of_neZero
    omega
  rw [hpred]

private theorem intCast_finrank_range_coeffCompat_eq
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc : 0 < c) (hd : 0 < d) :
    (Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffCompat
            (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ) =
      mZ n * nPowZ n (a + d)
        - 2 * (mZ n) ^ 2 * PassiveVisibleDimZ d n := by
  have h :=
    finrank_range_triangleLeafQ1BOnlyCoeffCompat_add_twoDefects_closed
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn ha2 hb2 hc hd
  have hZ := congrArg (fun x : ℕ => (x : ℤ)) h
  push_cast at hZ
  rw [intCast_passiveVisibleDim (n := n) (d := d) hd] at hZ
  have hpred : ((n - 1 : ℕ) : ℤ) = mZ n := by
    unfold mZ
    have hn1 : 1 ≤ n := one_le_of_neZero
    omega
  rw [hpred] at hZ
  simp only [nPowZ]
  ring_nf at hZ ⊢
  linarith

theorem finrank_triangleLeafE5LB_eq_CompatibleResidualSplitZ_even_large
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc2 : 2 ≤ c) (hd : 0 < d) :
    (Module.finrank F (triangleLeafE5LB n a b c d) : ℤ) =
      CompatibleResidualSplitZ a b c d n := by
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  have hnull :=
    finrank_range_coeffCompat_add_finrank_triangleLeafE5LB
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hnullZ := congrArg (fun x : ℕ => (x : ℤ)) hnull
  push_cast at hnullZ
  rw [intCast_finrank_triangleLeafCompatibleSubmodule_eq
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd,
    intCast_finrank_range_coeffCompat_eq
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn ha2 hb2 hc hd] at hnullZ
  rw [CompatibleResidualSplitZ_eq_CompatibleResidualExpZ ha hd]
  unfold CompatibleResidualExpZ
  rw [TriangleCore.ThetaZ_triangleLeaf_eq_of_even_large
      ha hd hn hb2 hc2]
  rw [nPowZ_add n c d, nPowZ_add n b d]
  unfold PassiveVisibleDimZ at hnullZ
  ring_nf at hnullZ ⊢
  linarith

set_option synthInstance.maxHeartbeats 100000 in
-- Nested kernel finrank inference needs more than the project default.
theorem toNat_CompatibleResidualSplitZ_eq_finrank_triangleLeafE5LB_even_large
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc2 : 2 ≤ c) (hd : 0 < d) :
    Int.toNat (CompatibleResidualSplitZ a b c d n) =
      Module.finrank F (triangleLeafE5LB n a b c d) := by
  rw [←
    finrank_triangleLeafE5LB_eq_CompatibleResidualSplitZ_even_large
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn ha2 hb2 hc2 hd]
  simp

end

end TriangleLeaf
end Core4loop
