import Core4loop.TriangleLeaf.ProfileKernelInteraction

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem intToNat_leafProfileKernelDim_eq_finrank
    {n a d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    Int.toNat (LeafProfileDimZ a d n - PassiveVisibleDimZ d n) =
      Module.finrank F (LeafProfileKernel n a d) := by
  have h :=
    intCast_finrank_ker_leafSigmaQuot_eq
      (n := n) (a := a) (d := d) ha hd
  rw [← h]
  simp

theorem card_LeafProfileKernel_eq_two_pow_splitDim
    {n a d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    Fintype.card (LeafProfileKernel n a d) =
      (2 : ℕ) ^ Int.toNat (LeafProfileDimZ a d n - PassiveVisibleDimZ d n) := by
  rw [card_LeafProfileKernel_eq_pow_finrank]
  rw [intToNat_leafProfileKernelDim_eq_finrank (n := n) (a := a) (d := d) ha hd]

theorem card_leafBProfileKernelCoord_eq_two_pow_splitDim
    {n a c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    Fintype.card (I n → ZVec n c → LeafProfileKernel n a d) =
      (2 : ℕ) ^
        (Int.toNat (LeafProfileDimZ a d n - PassiveVisibleDimZ d n)
          * (Fintype.card (ZVec n c) * Fintype.card (I n))) := by
  rw [Fintype.card_fun]
  rw [Fintype.card_fun]
  rw [card_LeafProfileKernel_eq_two_pow_splitDim (n := n) (a := a) (d := d) ha hd]
  rw [pow_mul]
  rw [pow_mul]

theorem card_leafCProfileKernelCoord_eq_two_pow_splitDim
    {n a b d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    Fintype.card (YVec n b → I n → LeafProfileKernel n a d) =
      (2 : ℕ) ^
        (Int.toNat (LeafProfileDimZ a d n - PassiveVisibleDimZ d n)
          * (Fintype.card (I n) * Fintype.card (YVec n b))) := by
  rw [Fintype.card_fun]
  rw [Fintype.card_fun]
  rw [card_LeafProfileKernel_eq_two_pow_splitDim (n := n) (a := a) (d := d) ha hd]
  rw [pow_mul]
  rw [pow_mul]

end

end TriangleLeaf
end Core4loop
