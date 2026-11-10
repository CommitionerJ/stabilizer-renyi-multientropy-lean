import Core4loop.TriangleLeaf.LeafProfileKernelDimensions

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable instance instFintypeZeroSumProfile {n : ℕ} [NeZero n] :
    Fintype (ZeroSumProfile n) := by
  classical
  exact Fintype.ofEquiv (NonzeroI n → F)
    (zeroSumProfileEquivNonzero (n := n)).symm.toEquiv

noncomputable instance instFintypeLeafDiffProfileCoord
    {n a : ℕ} [NeZero n] :
    Fintype (LeafDiffProfileCoord n a) := by
  classical
  infer_instance

theorem finrank_LeafDiffProfileCoord
    {n a : ℕ} [NeZero n] :
    Module.finrank F (LeafDiffProfileCoord n a) =
      n ^ (a - 1) * (n - 1) := by
  calc
    Module.finrank F (LeafDiffProfileCoord n a)
        = ∑ _ : PVec n a, Module.finrank F (ZeroSumProfile n) := by
            simp [LeafDiffProfileCoord, Module.finrank_pi_fintype
              (R := F) (M := fun _ : PVec n a => ZeroSumProfile n)]
    _ = Fintype.card (PVec n a) * (n - 1) := by
            rw [finrank_ZeroSumProfile]
            simp
    _ = n ^ (a - 1) * (n - 1) := by
            rw [card_vec]

theorem card_ZeroSumProfile_eq_pow_finrank
    {n : ℕ} [NeZero n] :
    Fintype.card (ZeroSumProfile n) =
      2 ^ Module.finrank F (ZeroSumProfile n) := by
  rw [← Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

theorem card_ZeroSumProfile
    {n : ℕ} [NeZero n] :
    Fintype.card (ZeroSumProfile n) = 2 ^ (n - 1) := by
  rw [card_ZeroSumProfile_eq_pow_finrank,
    finrank_ZeroSumProfile]

theorem card_LeafDiffProfileCoord
    {n a : ℕ} [NeZero n] :
    Fintype.card (LeafDiffProfileCoord n a) =
      (2 ^ (n - 1)) ^ (n ^ (a - 1)) := by
  classical
  rw [Fintype.card_fun]
  rw [card_ZeroSumProfile, card_vec]

theorem finrank_LeafProfileKernel_visible_diff
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (LeafProfileKernel n a d) =
      Module.finrank F (LeafVisibleProfileKernel n a d hd)
        + Module.finrank F (LeafDiffProfileCoord n a) := by
  calc
    Module.finrank F (LeafProfileKernel n a d)
        =
        Module.finrank F
          (LeafVisibleProfileKernel n a d hd × LeafDiffProfileCoord n a) := by
          exact LinearEquiv.finrank_eq
            (leafProfileKernelEquivVisibleDiff
              (n := n) (a := a) (d := d) hd)
    _ =
        Module.finrank F (LeafVisibleProfileKernel n a d hd)
          + Module.finrank F (LeafDiffProfileCoord n a) := by
          simp

theorem finrank_LeafProfileKernel_explicit
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (LeafProfileKernel n a d) =
      (n ^ d - (n - 1)) * (n ^ (a - 1) - 1)
        + n ^ (a - 1) * (n - 1) := by
  rw [finrank_LeafProfileKernel_visible_diff
      (n := n) (a := a) (d := d) hd,
    finrank_LeafVisibleProfileKernel (n := n) (a := a) (d := d) hd,
    finrank_LeafDiffProfileCoord (n := n) (a := a)]

theorem card_LeafProfileKernel_visible_diff
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype.card (LeafProfileKernel n a d) =
      Fintype.card (LeafVisibleProfileKernel n a d hd)
        * Fintype.card (LeafDiffProfileCoord n a) := by
  classical
  rw [Fintype.card_congr
    (leafProfileKernelEquivVisibleDiff
      (n := n) (a := a) (d := d) hd).toEquiv]
  rw [Fintype.card_prod]

theorem card_LeafProfileKernel_visible_diff_explicit
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype.card (LeafProfileKernel n a d) =
      (2 ^ (n ^ (a - 1) - 1)) ^ (n ^ d - (n - 1))
        * (2 ^ (n - 1)) ^ (n ^ (a - 1)) := by
  rw [card_LeafProfileKernel_visible_diff
      (n := n) (a := a) (d := d) hd,
    card_LeafVisibleProfileKernel (n := n) (a := a) (d := d) hd,
    card_LeafDiffProfileCoord (n := n) (a := a)]

end

end TriangleLeaf
end Core4loop
