import Core4loop.TriangleLeaf.VisibleMaps
import Core4loop.TriangleLeaf.ExponentSplit

namespace Core4loop
namespace TriangleLeaf

def LeafBVisibleDimZ (c d n : ℕ) : ℤ :=
  nPowZ n (c + 1) * PassiveVisibleDimZ d n

def LeafCVisibleDimZ (b d n : ℕ) : ℤ :=
  nPowZ n (b + 1) * PassiveVisibleDimZ d n

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

theorem intCast_finrank_LeafBVisible_eq {n c d : ℕ} [NeZero n] (hd : 0 < d) :
    (Module.finrank F (LeafBVisible n c d) : ℤ) =
      LeafBVisibleDimZ c d n := by
  rw [finrank_LeafBVisible (n := n) (c := c) (d := d) hd]
  unfold LeafBVisibleDimZ nPowZ
  rw [Nat.cast_mul, Nat.cast_pow, intCast_passiveVisibleNat_eq (n := n) (d := d) hd]

theorem intCast_finrank_LeafCVisible_eq {n b d : ℕ} [NeZero n] (hd : 0 < d) :
    (Module.finrank F (LeafCVisible n b d) : ℤ) =
      LeafCVisibleDimZ b d n := by
  rw [finrank_LeafCVisible (n := n) (b := b) (d := d) hd]
  unfold LeafCVisibleDimZ nPowZ
  rw [Nat.cast_mul, Nat.cast_pow, intCast_passiveVisibleNat_eq (n := n) (d := d) hd]

theorem intCast_finrank_ker_leafBVisMap_eq
    {n a c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    (Module.finrank F
        (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))) : ℤ)
      =
      nPowZ n (a + c + d) - LeafBVisibleDimZ c d n := by
  have h :=
    finrank_ker_leafBVisMap_add (n := n) (a := a) (c := c) (d := d) ha hd
  have hZ :
      (Module.finrank F
          (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))) : ℤ)
        + (n ^ (c + 1) * (n ^ d - (n - 1)) : ℕ)
        =
        (n ^ (a + c + d) : ℕ) := by
    exact_mod_cast h
  have hvisible :
      ((n ^ (c + 1) * (n ^ d - (n - 1)) : ℕ) : ℤ) =
        LeafBVisibleDimZ c d n := by
    unfold LeafBVisibleDimZ nPowZ
    rw [Nat.cast_mul, Nat.cast_pow, intCast_passiveVisibleNat_eq (n := n) (d := d) hd]
  have htotal :
      ((n ^ (a + c + d) : ℕ) : ℤ) = nPowZ n (a + c + d) := by
    unfold nPowZ
    simp
  rw [hvisible, htotal] at hZ
  linarith

theorem intCast_finrank_ker_leafCVisMap_eq
    {n a b d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    (Module.finrank F
        (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d))) : ℤ)
      =
      nPowZ n (a + b + d) - LeafCVisibleDimZ b d n := by
  have h :=
    finrank_ker_leafCVisMap_add (n := n) (a := a) (b := b) (d := d) ha hd
  have hZ :
      (Module.finrank F
          (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d))) : ℤ)
        + (n ^ (b + 1) * (n ^ d - (n - 1)) : ℕ)
        =
        (n ^ (a + b + d) : ℕ) := by
    exact_mod_cast h
  have hvisible :
      ((n ^ (b + 1) * (n ^ d - (n - 1)) : ℕ) : ℤ) =
        LeafCVisibleDimZ b d n := by
    unfold LeafCVisibleDimZ nPowZ
    rw [Nat.cast_mul, Nat.cast_pow, intCast_passiveVisibleNat_eq (n := n) (d := d) hd]
  have htotal :
      ((n ^ (a + b + d) : ℕ) : ℤ) = nPowZ n (a + b + d) := by
    unfold nPowZ
    simp
  rw [hvisible, htotal] at hZ
  linarith

end TriangleLeaf
end Core4loop
