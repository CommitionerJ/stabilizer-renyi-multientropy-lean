import TreeGraph.Imbalance.PhysicalRootCoords

namespace TreeGraph
namespace Imbalance

structure OpenNormalAssignmentClean
    (n : Nat) [NeZero n] (T : RTree) where
  nodeField :
    (v : NonRootVertex T) →
      NonRootFieldDomainClean n T v → F2
  deriving Fintype

noncomputable def closeOpenNormalAssignmentClean
    {n : Nat} [NeZero n] {T : RTree}
    (root : RootFieldAssignmentClean n T)
    (A : OpenNormalAssignmentClean n T) :
    NormalAssignmentClean n T where
  rootField := root
  nodeField := A.nodeField

noncomputable def normalAssignmentCleanEquivRootOpen
    (n : Nat) [NeZero n] (T : RTree) :
    NormalAssignmentClean n T ≃
      RootFieldAssignmentClean n T × OpenNormalAssignmentClean n T where
  toFun A := (A.rootField, ⟨A.nodeField⟩)
  invFun P := closeOpenNormalAssignmentClean P.1 P.2
  left_inv A := by
    cases A
    rfl
  right_inv P := by
    rcases P with ⟨root, Aopen⟩
    cases Aopen
    rfl

noncomputable def openNormalSignedSumClean
    (n : Nat) [NeZero n] (T : RTree)
    (root : RootFieldAssignmentClean n T) : ℤ :=
  ∑ A : OpenNormalAssignmentClean n T,
    weightClean T (closeOpenNormalAssignmentClean root A)

theorem normalSignedSumClean_eq_sum_openNormalSignedSumClean
    (n : Nat) [NeZero n] (T : RTree) :
    normalSignedSumClean n T =
      ∑ root : RootFieldAssignmentClean n T,
        openNormalSignedSumClean n T root := by
  classical
  unfold normalSignedSumClean openNormalSignedSumClean
  calc
    (∑ A : NormalAssignmentClean n T, weightClean T A) =
        ∑ P : RootFieldAssignmentClean n T × OpenNormalAssignmentClean n T,
          weightClean T ((normalAssignmentCleanEquivRootOpen n T).symm P) := by
      exact (Equiv.sum_comp
        (normalAssignmentCleanEquivRootOpen n T).symm
        (fun A : NormalAssignmentClean n T => weightClean T A)).symm
    _ = ∑ root : RootFieldAssignmentClean n T,
          ∑ A : OpenNormalAssignmentClean n T,
            weightClean T (closeOpenNormalAssignmentClean root A) := by
      rw [Fintype.sum_prod_type]
      rfl

open Classical in
structure OpenNormalCleanReductionBridge
    (n : Nat) [NeZero n] (T : RTree)
    (hT : RTree.PositiveWeights T) where
  rootMessageSpace : Submodule F2 (RootFieldAssignmentClean n T)
  rootMessageSpace_finrank :
    Module.finrank F2 rootMessageSpace = Ydim n T hT
  open_signed_sum_eq :
    ∀ root : RootFieldAssignmentClean n T,
      openNormalSignedSumClean n T root =
        if root ∈ rootMessageSpace then
          (2 : ℤ) ^ (Xdim n T - Ydim n T hT)
        else 0

end Imbalance
end TreeGraph
