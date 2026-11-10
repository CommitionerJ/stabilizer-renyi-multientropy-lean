import Core4loop.TriangleLeaf.LeafProfileKernelSplitDims

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem card_kCdFamily_expanded
    {n a b : ℕ} [NeZero n] :
    Fintype.card (YVec n b → I n → LeafDiffProfileCoord n a) =
      (2 : ℕ) ^ ((n - 1) * n ^ (a - 1) * (n * n ^ b)) := by
  classical
  rw [Fintype.card_fun]
  rw [Fintype.card_fun]
  rw [card_LeafDiffProfileCoord, card_vec]
  simp only [ZMod.card]
  rw [pow_mul, pow_mul]
  ring_nf

theorem card_kCdFamily
    {n a b : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (YVec n b → I n → LeafDiffProfileCoord n a) =
      (2 : ℕ) ^ (n ^ (a + b) * (n - 1)) := by
  rw [card_kCdFamily_expanded (n := n) (a := a) (b := b)]
  congr 1
  have hpowa : n ^ (a + b) = n ^ (a - 1) * (n * n ^ b) := by
    have hsplit : a + b = (a - 1) + (b + 1) := by omega
    rw [hsplit, Nat.pow_add, Nat.pow_add, pow_one]
    ring
  rw [hpowa]
  ring

theorem intCast_card_kCdFamily
    {n a b : ℕ} [NeZero n] (ha : 0 < a) :
    (Fintype.card (YVec n b → I n → LeafDiffProfileCoord n a) : ℤ) =
      (2 : ℤ) ^ (n ^ (a + b) * (n - 1)) := by
  exact_mod_cast card_kCdFamily (n := n) (a := a) (b := b) ha

end

end TriangleLeaf
end Core4loop
