import Core4loop.TriangleLeaf.DiffProfileSignSum

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafDiffFamilyCoeffApply {ι : Type*} [Fintype ι]
    {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → I n → F)
    (X : ι → LeafDiffProfileCoord n a) : F :=
  ∑ i : ι, leafDiffCoeffApply (n := n) (a := a) (C i) (X i)

def leafDiffFamilyCoeffRead {ι : Type*}
    {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → I n → F) :
    ι × (PVec n a × NonzeroI n) → F :=
  fun ips => leafDiffCoeffRead (n := n) (a := a) (C ips.1) ips.2

theorem leafDiffFamilyCoeffRead_add {ι : Type*}
    {n a : ℕ} [NeZero n]
    (C D : ι → PVec n a → I n → F) :
    leafDiffFamilyCoeffRead (n := n) (a := a) (C + D)
      =
      leafDiffFamilyCoeffRead (n := n) (a := a) C
        +
      leafDiffFamilyCoeffRead (n := n) (a := a) D := by
  funext ips
  rcases ips with ⟨i, p, s⟩
  simp [leafDiffFamilyCoeffRead, leafDiffCoeffRead, Pi.add_apply]
  abel

theorem leafDiffFamilyCoeffRead_smul {ι : Type*}
    {n a : ℕ} [NeZero n]
    (r : F) (C : ι → PVec n a → I n → F) :
    leafDiffFamilyCoeffRead (n := n) (a := a) (r • C)
      =
      r • leafDiffFamilyCoeffRead (n := n) (a := a) C := by
  funext ips
  rcases ips with ⟨i, p, s⟩
  simp [leafDiffFamilyCoeffRead, leafDiffCoeffRead, Pi.smul_apply]
  ring

noncomputable def leafDiffFamilyEquivNonzero {ι : Type*}
    {n a : ℕ} [NeZero n] :
    (ι → LeafDiffProfileCoord n a) ≃
      (ι × (PVec n a × NonzeroI n) → F) where
  toFun X := fun ips =>
    leafDiffProfileCoordEquivNonzero (n := n) (a := a) (X ips.1) ips.2
  invFun f := fun i =>
    (leafDiffProfileCoordEquivNonzero (n := n) (a := a)).symm
      (fun ps => f (i, ps))
  left_inv X := by
    funext i
    exact (leafDiffProfileCoordEquivNonzero (n := n) (a := a)).left_inv (X i)
  right_inv f := by
    funext ips
    rcases ips with ⟨i, ps⟩
    exact congrFun
      ((leafDiffProfileCoordEquivNonzero (n := n) (a := a)).right_inv
        (fun ps => f (i, ps))) ps

theorem leafDiffFamilyCoeffApply_eq_coeffApply_read
    {ι : Type*} [Fintype ι]
    {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → I n → F)
    (X : ι → LeafDiffProfileCoord n a) :
    leafDiffFamilyCoeffApply (n := n) (a := a) C X =
      coeffApply (leafDiffFamilyCoeffRead (n := n) (a := a) C)
        (leafDiffFamilyEquivNonzero (n := n) (a := a) X) := by
  unfold leafDiffFamilyCoeffApply coeffApply leafDiffFamilyCoeffRead
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [leafDiffCoeffApply_eq_coeffApply_read (n := n) (a := a) (C i) (X i)]
  unfold coeffApply
  simp [leafDiffFamilyEquivNonzero]

theorem card_leafDiffFamilyCoeffIndex
    {ι : Type*} [Fintype ι] {n a : ℕ} [NeZero n] :
    Fintype.card (ι × (PVec n a × NonzeroI n)) =
      Fintype.card ι * (n ^ (a - 1) * (n - 1)) := by
  rw [Fintype.card_prod, card_leafDiffCoeffIndex]

theorem sum_leafDiffFamily_bitSign_linear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → I n → F) :
    (∑ X : ι → LeafDiffProfileCoord n a,
      bitSign (leafDiffFamilyCoeffApply (n := n) (a := a) C X))
      =
      if leafDiffFamilyCoeffRead (n := n) (a := a) C = 0 then
        (2 : ℤ) ^ (Fintype.card ι * (n ^ (a - 1) * (n - 1)))
      else 0 := by
  classical
  let e := leafDiffFamilyEquivNonzero (ι := ι) (n := n) (a := a)
  calc
    (∑ X : ι → LeafDiffProfileCoord n a,
      bitSign (leafDiffFamilyCoeffApply (n := n) (a := a) C X))
        =
        ∑ f : ι × (PVec n a × NonzeroI n) → F,
          bitSign (coeffApply
            (leafDiffFamilyCoeffRead (n := n) (a := a) C) f) := by
            simpa [e, leafDiffFamilyCoeffApply_eq_coeffApply_read
              (n := n) (a := a) C] using
              (Equiv.sum_comp e
                (fun f : ι × (PVec n a × NonzeroI n) → F =>
                  bitSign (coeffApply
                    (leafDiffFamilyCoeffRead (n := n) (a := a) C) f)))
    _ =
        signedCoeffSum
          (leafDiffFamilyCoeffRead (n := n) (a := a) C) := by
          rfl
    _ =
      if leafDiffFamilyCoeffRead (n := n) (a := a) C = 0 then
        (2 : ℤ) ^ (Fintype.card ι * (n ^ (a - 1) * (n - 1)))
      else 0 := by
        rw [signedCoeffSum_formula]
        rw [card_leafDiffFamilyCoeffIndex (ι := ι) (n := n) (a := a)]

theorem sum_leafDiffFamily_bitSign_linear_add_const
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → I n → F) (q : F) :
    (∑ X : ι → LeafDiffProfileCoord n a,
      bitSign (leafDiffFamilyCoeffApply (n := n) (a := a) C X + q))
      =
      (if leafDiffFamilyCoeffRead (n := n) (a := a) C = 0 then
        (2 : ℤ) ^ (Fintype.card ι * (n ^ (a - 1) * (n - 1)))
      else 0) * bitSign q := by
  calc
    (∑ X : ι → LeafDiffProfileCoord n a,
      bitSign (leafDiffFamilyCoeffApply (n := n) (a := a) C X + q))
        =
        ∑ X : ι → LeafDiffProfileCoord n a,
          bitSign (leafDiffFamilyCoeffApply (n := n) (a := a) C X) *
            bitSign q := by
            refine Finset.sum_congr rfl ?_
            intro X _
            rw [bitSign_add]
    _ =
        (∑ X : ι → LeafDiffProfileCoord n a,
          bitSign (leafDiffFamilyCoeffApply (n := n) (a := a) C X)) *
            bitSign q := by
            rw [Finset.sum_mul]
    _ =
      (if leafDiffFamilyCoeffRead (n := n) (a := a) C = 0 then
        (2 : ℤ) ^ (Fintype.card ι * (n ^ (a - 1) * (n - 1)))
      else 0) * bitSign q := by
        rw [sum_leafDiffFamily_bitSign_linear (n := n) (a := a) C]

end

end TriangleLeaf
end Core4loop
