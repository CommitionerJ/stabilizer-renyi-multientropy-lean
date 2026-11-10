import Core4loop.TriangleLeaf.PassiveProfile
import Core4loop.TriangleLeaf.ExponentSplit

namespace Core4loop
namespace TriangleLeaf

theorem intCast_finrank_ker_leafSigmaQuot_eq
    {n a d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    (Module.finrank F
        (LinearMap.ker (leafSigmaQuot (n := n) (a := a) (d := d))) : ℤ)
      =
      LeafProfileDimZ a d n - PassiveVisibleDimZ d n := by
  have h :=
    finrank_ker_leafSigmaQuot_add (n := n) (a := a) (d := d) ha hd
  have hZ :
      (Module.finrank F
          (LinearMap.ker (leafSigmaQuot (n := n) (a := a) (d := d))) : ℤ)
        + ((n ^ d - (n - 1) : ℕ) : ℤ)
        =
        (n ^ (a + d - 1) : ℕ) := by
    exact_mod_cast h
  have hle : n - 1 ≤ n ^ d := by
    have hnle : n ≤ n ^ d := Nat.le_pow hd
    exact Nat.le_trans (Nat.sub_le n 1) hnle
  have hvisible :
      ((n ^ d - (n - 1) : ℕ) : ℤ) = PassiveVisibleDimZ d n := by
    unfold PassiveVisibleDimZ nPowZ mZ
    rw [Nat.cast_sub hle]
    simp only [Nat.cast_pow]
    have hpred : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      have hn : 1 ≤ n := one_le_of_neZero
      omega
    rw [hpred]
  have hprofile :
      ((n ^ (a + d - 1) : ℕ) : ℤ) = LeafProfileDimZ a d n := by
    unfold LeafProfileDimZ nPowZ
    simp
  rw [hvisible, hprofile] at hZ
  linarith

end TriangleLeaf
end Core4loop
