import Core4loop.TriangleLeaf.LeafProfileKernelSplitDims
import Core4loop.Sign

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafDiffCoeffApply {n a : ℕ} [NeZero n]
    (C : PVec n a → I n → F) (X : LeafDiffProfileCoord n a) : F :=
  ∑ p : PVec n a, ∑ s : I n, (X p).1 s * C p s

def leafDiffCoeffRead {n a : ℕ} [NeZero n]
    (C : PVec n a → I n → F) : PVec n a × NonzeroI n → F :=
  fun ps => C ps.1 ps.2.1 + C ps.1 0

noncomputable def leafDiffProfileCoordEquivNonzero {n a : ℕ} [NeZero n] :
    LeafDiffProfileCoord n a ≃ (PVec n a × NonzeroI n → F) where
  toFun X := fun ps =>
    (zeroSumProfileEquivNonzero (n := n) (X ps.1)) ps.2
  invFun f := fun p =>
    (zeroSumProfileEquivNonzero (n := n)).symm (fun s => f (p, s))
  left_inv X := by
    funext p
    exact (zeroSumProfileEquivNonzero (n := n)).left_inv (X p)
  right_inv f := by
    funext ps
    rcases ps with ⟨p, s⟩
    exact congrFun ((zeroSumProfileEquivNonzero (n := n)).right_inv (fun s => f (p, s))) s

private theorem zeroSumProfile_coeff_apply_eq_nonzero_read
    {n : ℕ} [NeZero n] (C : I n → F) (X : ZeroSumProfile n) :
    (∑ s : I n, X.1 s * C s) =
      ∑ u : NonzeroI n, X.1 u.1 * (C u.1 + C 0) := by
  have hzero : X.1 0 = ∑ u : NonzeroI n, X.1 u.1 :=
    value_zero_eq_sum_nonzero_of_sum_zero (LinearMap.mem_ker.mp X.2)
  calc
    (∑ s : I n, X.1 s * C s)
        = X.1 0 * C 0 + ∑ u : NonzeroI n, X.1 u.1 * C u.1 := by
            rw [sum_I_eq_value_zero_add_sum_nonzero]
    _ = (∑ u : NonzeroI n, X.1 u.1) * C 0
          + ∑ u : NonzeroI n, X.1 u.1 * C u.1 := by
            rw [hzero]
    _ = (∑ u : NonzeroI n, X.1 u.1 * C 0)
          + ∑ u : NonzeroI n, X.1 u.1 * C u.1 := by
            rw [Finset.sum_mul]
    _ = ∑ u : NonzeroI n, (X.1 u.1 * C 0 + X.1 u.1 * C u.1) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ u : NonzeroI n, X.1 u.1 * (C u.1 + C 0) := by
            refine Finset.sum_congr rfl ?_
            intro u _
            ring

theorem leafDiffCoeffApply_eq_coeffApply_read
    {n a : ℕ} [NeZero n]
    (C : PVec n a → I n → F) (X : LeafDiffProfileCoord n a) :
    leafDiffCoeffApply (n := n) (a := a) C X =
      coeffApply (leafDiffCoeffRead (n := n) (a := a) C)
        (leafDiffProfileCoordEquivNonzero (n := n) (a := a) X) := by
  unfold leafDiffCoeffApply coeffApply leafDiffCoeffRead leafDiffProfileCoordEquivNonzero
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro p _
  exact zeroSumProfile_coeff_apply_eq_nonzero_read (n := n) (C p) (X p)

theorem card_leafDiffCoeffIndex {n a : ℕ} [NeZero n] :
    Fintype.card (PVec n a × NonzeroI n) = n ^ (a - 1) * (n - 1) := by
  rw [Fintype.card_prod, card_vec, card_NonzeroI]

theorem sum_leafDiffProfileCoord_bitSign_linear
    {n a : ℕ} [NeZero n] (C : PVec n a → I n → F) :
    (∑ X : LeafDiffProfileCoord n a,
      bitSign (leafDiffCoeffApply (n := n) (a := a) C X))
      =
      if leafDiffCoeffRead (n := n) (a := a) C = 0 then
        (2 : ℤ) ^ (n ^ (a - 1) * (n - 1))
      else 0 := by
  classical
  let e := leafDiffProfileCoordEquivNonzero (n := n) (a := a)
  calc
    (∑ X : LeafDiffProfileCoord n a,
      bitSign (leafDiffCoeffApply (n := n) (a := a) C X))
        =
        ∑ f : PVec n a × NonzeroI n → F,
          bitSign (coeffApply (leafDiffCoeffRead (n := n) (a := a) C) f) := by
            simpa [e, leafDiffCoeffApply_eq_coeffApply_read
              (n := n) (a := a) C] using
              (Equiv.sum_comp e
                (fun f : PVec n a × NonzeroI n → F =>
                  bitSign (coeffApply (leafDiffCoeffRead (n := n) (a := a) C) f)))
    _ =
        signedCoeffSum (leafDiffCoeffRead (n := n) (a := a) C) := by
          rfl
    _ =
      if leafDiffCoeffRead (n := n) (a := a) C = 0 then
        (2 : ℤ) ^ (n ^ (a - 1) * (n - 1))
      else 0 := by
        rw [signedCoeffSum_formula]
        rw [card_leafDiffCoeffIndex (n := n) (a := a)]

end

end TriangleLeaf
end Core4loop
