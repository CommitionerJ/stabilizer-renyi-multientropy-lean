import Core4loop.TriangleLeaf.DiffProfileFamilySignSum

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private theorem coeffApply_forall_eq_zero_iff
    {ι : Type*} [Fintype ι] (c : ι → F) :
    (∀ f : ι → F, coeffApply c f = 0) ↔ c = 0 := by
  classical
  constructor
  · intro h
    funext i
    have hi := h (fun j => if j = i then (1 : F) else 0)
    unfold coeffApply at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa using hi
    · intro j _ hj
      simp [hj]
    · simp
  · intro hc f
    simp [coeffApply, hc]

theorem leafDiffFamilyCoeffApply_forall_eq_zero_iff
    {ι : Type*} [Fintype ι]
    {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → I n → F) :
    (∀ X : ι → LeafDiffProfileCoord n a,
        leafDiffFamilyCoeffApply (n := n) (a := a) C X = 0)
      ↔ leafDiffFamilyCoeffRead (n := n) (a := a) C = 0 := by
  classical
  constructor
  · intro h
    apply (coeffApply_forall_eq_zero_iff
      (leafDiffFamilyCoeffRead (n := n) (a := a) C)).1
    intro f
    let e := leafDiffFamilyEquivNonzero (ι := ι) (n := n) (a := a)
    have hf := h (e.symm f)
    rw [leafDiffFamilyCoeffApply_eq_coeffApply_read
      (n := n) (a := a) C] at hf
    simpa [e] using hf
  · intro hread X
    rw [leafDiffFamilyCoeffApply_eq_coeffApply_read
      (n := n) (a := a) C, hread]
    simp [coeffApply]

theorem linearMap_eq_zero_iff_of_apply_eq_leafDiffFamilyCoeffApply
    {ι : Type*} [Fintype ι]
    {n a : ℕ} [NeZero n]
    (L : (ι → LeafDiffProfileCoord n a) →ₗ[F] F)
    (C : ι → PVec n a → I n → F)
    (hL : ∀ X : ι → LeafDiffProfileCoord n a,
      L X = leafDiffFamilyCoeffApply (n := n) (a := a) C X) :
    L = 0 ↔ leafDiffFamilyCoeffRead (n := n) (a := a) C = 0 := by
  have hzero := leafDiffFamilyCoeffApply_forall_eq_zero_iff
    (n := n) (a := a) C
  constructor
  · intro h
    rw [← hzero]
    intro X
    rw [← hL X, h]
    rfl
  · intro hread
    apply LinearMap.ext
    intro X
    rw [hL X]
    exact hzero.2 hread X

end

end TriangleLeaf
end Core4loop
