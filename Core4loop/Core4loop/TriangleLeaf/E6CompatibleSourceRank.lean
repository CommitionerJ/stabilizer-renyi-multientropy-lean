import Core4loop.TriangleLeaf.FiberCard
import Core4loop.TriangleLeaf.E5CompatibleQuadratic
import Core4loop.TriangleLeaf.VisibleMapsExp

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Level 5: source-derived structural/dimension certificates for the exact
TriangleLeaf compatible source.
-/

set_option maxHeartbeats 1000000 in
-- Exact cardinal transport across nested finite function-space equivalences is deep.
set_option synthInstance.maxHeartbeats 1000000 in
theorem finrank_triangleLeafCompatibleSubmodule_eq_visibleFiberSum
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (triangleLeafCompatibleSubmodule n a b c d) =
      Module.finrank F
          (LinearMap.ker
            (leafBVisMap (n := n) (a := a) (c := c) (d := d))) +
      Module.finrank F
          (LinearMap.ker
            (leafCVisMap (n := n) (a := a) (b := b) (d := d))) +
      (n ^ d - (n - 1)) *
        (n ^ b + n ^ c + (n - 1) ^ 2) := by
  classical
  let e :=
    (triangleLeafCompatibleEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d)).trans
      (leafCompatibleBCEquivVisibleSigma
        (n := n) (a := a) (b := b) (c := c) (d := d))
  have hcard :
      Fintype.card (triangleLeafCompatibleSubmodule n a b c d) =
        Fintype.card (LeafSurvivingSigma n a b c d) :=
    Fintype.card_congr e
  rw [Module.card_eq_pow_finrank
      (K := F) (V := triangleLeafCompatibleSubmodule n a b c d),
    card_LeafSurvivingSigma_factor,
    card_LeafVisibleKernel (n := n) (b := b) (c := c) (d := d) hb hc hd] at hcard
  simp only [F, ZMod.card] at hcard
  rw [← pow_mul, ← pow_add, ← pow_add] at hcard
  have hexponent := Nat.pow_right_injective (by omega : 1 < 2) hcard
  simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hexponent

private theorem intCast_passiveVisibleNat_eq_sourceRank
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

set_option maxHeartbeats 1000000 in
-- Casting the exact source finrank again needs the same deep module instances.
set_option synthInstance.maxHeartbeats 1000000 in
theorem intCast_finrank_triangleLeafCompatibleSubmodule_eq
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (Module.finrank F
        (triangleLeafCompatibleSubmodule n a b c d) : ℤ) =
      nPowZ n (a + c + d) + nPowZ n (a + b + d)
      - mZ n * (nPowZ n b + nPowZ n c) *
          PassiveVisibleDimZ d n
      + (mZ n) ^ 2 * PassiveVisibleDimZ d n := by
  have hsource :=
    finrank_triangleLeafCompatibleSubmodule_eq_visibleFiberSum
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
  have hsourceZ := congrArg (fun x : ℕ => (x : ℤ)) hsource
  push_cast at hsourceZ
  rw [intCast_finrank_ker_leafBVisMap_eq
      (n := n) (a := a) (c := c) (d := d) ha hd,
    intCast_finrank_ker_leafCVisMap_eq
      (n := n) (a := a) (b := b) (d := d) ha hd,
    intCast_passiveVisibleNat_eq_sourceRank
      (n := n) (d := d) hd] at hsourceZ
  have hpred : ((n - 1 : ℕ) : ℤ) = mZ n := by
    unfold mZ
    have hn : 1 ≤ n := one_le_of_neZero
    omega
  rw [hpred] at hsourceZ
  calc
    (Module.finrank F
        (triangleLeafCompatibleSubmodule n a b c d) : ℤ)
        =
        (nPowZ n (a + c + d) - LeafBVisibleDimZ c d n) +
          (nPowZ n (a + b + d) - LeafCVisibleDimZ b d n) +
          PassiveVisibleDimZ d n *
            (nPowZ n b + nPowZ n c + mZ n ^ 2) := by
              simpa [nPowZ] using hsourceZ
    _ =
        nPowZ n (a + c + d) + nPowZ n (a + b + d)
          - mZ n * (nPowZ n b + nPowZ n c) *
              PassiveVisibleDimZ d n
          + (mZ n) ^ 2 * PassiveVisibleDimZ d n := by
            unfold LeafBVisibleDimZ LeafCVisibleDimZ nPowZ mZ
            rw [pow_succ', pow_succ']
            ring

set_option maxHeartbeats 1000000 in
-- The cast bridge elaborates the compatible-source finrank instance a second time.
set_option synthInstance.maxHeartbeats 1000000 in
theorem finrank_triangleLeafCompatibleSubmodule_add_constraint_terms
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (triangleLeafCompatibleSubmodule n a b c d)
      + (n - 1) * (n ^ (c + d) + n ^ (b + d))
      + (n - 1) ^ 3
    =
      n ^ (a + c + d) + n ^ (a + b + d)
      + (n - 1) ^ 2 * (n ^ b + n ^ c + n ^ d) := by
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [intCast_finrank_triangleLeafCompatibleSubmodule_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd]
  have hpred : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    have hn : 1 ≤ n := one_le_of_neZero
    omega
  rw [hpred]
  simp only [nPowZ, mZ, PassiveVisibleDimZ]
  rw [pow_add (n : ℤ) c d, pow_add (n : ℤ) b d]
  ring

end

end TriangleLeaf
end Core4loop
