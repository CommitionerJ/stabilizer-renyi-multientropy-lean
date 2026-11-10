import TreeGraph.Imbalance.HeadOpenFubini
import TreeGraph.Imbalance.NodeConsOpenSumArchitecture

namespace TreeGraph
namespace Imbalance

noncomputable def HeadChildPhysicalPackageReduction.ofDataFubini
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT) :
    HeadChildPhysicalPackageReduction n a C rest hT I where
  head_reduction_eq := by
    intro root
    simpa [headChildPhysicalSignedSum] using
      headChildOpenDataSignedSum_eq_descScalar_mul_messageSum
        n a C rest
        (child_positive_of_node hT C (by simp))
        (I.childPackage C (by simp))
        root

theorem headChildPhysicalSignedSum_eq_if_headAllowed_branchScalar
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (ha : 0 < a)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildPhysicalSignedSum n a C rest hC P root =
      (by
        classical
        exact
          if headParentRootBoundaryFieldFromRoot n a C rest root ∈
              headAllowedBoundarySpace n a C rest hC P then
            (2 : ℤ) ^ branchScalarExponent n a 0 C rest
          else
            0) := by
  classical
  rw [headChildPhysicalSignedSum]
  rw [headChildOpenDataSignedSum_eq_descScalar_mul_messageSum]
  rw [headBranchMessageSignedSum_eq_if_headAllowed_branchScalar]
  by_cases hhead : headParentRootBoundaryFieldFromRoot n a C rest root ∈
      headAllowedBoundarySpace n a C rest hC P
  · rw [if_pos hhead, if_pos hhead]
    rw [← pow_add]
    rw [branchScalarExponent_split n a 0 C rest ha hC]
  · rw [if_neg hhead, if_neg hhead]
    rw [mul_zero]

theorem headChildPhysicalSignedSum_of_head_allowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (ha : 0 < a)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest hC P →
      headChildPhysicalSignedSum n a C rest hC P root =
        (2 : ℤ) ^ branchScalarExponent n a 0 C rest := by
  intro hhead
  rw [headChildPhysicalSignedSum_eq_if_headAllowed_branchScalar
    n a C rest ha hC P root]
  rw [if_pos hhead]

theorem headChildPhysicalSignedSum_of_root_mem_packageAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageAllowedRootFieldSpace n a (C :: rest) hT I →
      headChildPhysicalSignedSum n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) root =
        (2 : ℤ) ^ branchScalarExponent n a 0 C rest := by
  intro hroot
  have ha : 0 < a := by
    have hnode : 0 < a ∧ ∀ D ∈ C :: rest, RTree.PositiveWeights D := by
      simpa [RTree.PositiveWeights] using hT
    exact hnode.1
  have hmsg :=
    headBranchMessageSignedSum_of_root_mem_packageAllowed
      n a C rest hT I hbridge root hroot
  calc
    headChildPhysicalSignedSum n a C rest
        (child_positive_of_node hT C (by simp))
        (I.childPackage C (by simp)) root =
        (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest
            (child_positive_of_node hT C (by simp)) *
          headBranchMessageSignedSum n a C rest
            (child_positive_of_node hT C (by simp))
            (I.childPackage C (by simp)) root := by
          exact (HeadChildPhysicalPackageReduction.ofDataFubini
            n a C rest hT I).head_reduction_eq root
    _ = (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest
            (child_positive_of_node hT C (by simp)) *
          (2 : ℤ) ^ branchMessageScalarExponent n a 0 C rest
            (child_positive_of_node hT C (by simp)) := by
          rw [hmsg]
    _ = (2 : ℤ) ^ branchScalarExponent n a 0 C rest := by
          rw [← pow_add]
          rw [branchScalarExponent_split n a 0 C rest ha
            (child_positive_of_node hT C (by simp))]

theorem headChildPhysicalSignedSum_of_head_notAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBoundaryFieldFromRoot n a C rest root ∉
        headAllowedBoundarySpace n a C rest hC P →
      headChildPhysicalSignedSum n a C rest hC P root = 0 := by
  intro hhead
  rw [headChildPhysicalSignedSum]
  rw [headChildOpenDataSignedSum_eq_descScalar_mul_messageSum]
  rw [headBranchMessageSignedSum_of_head_notAllowed n a C rest hC P root hhead]
  rw [mul_zero]

end Imbalance
end TreeGraph
