import TreeGraph.Imbalance.NodeHeadOpenDataEquiv

namespace TreeGraph
namespace Imbalance

noncomputable def parentHeadFieldsDataWeightAtHead
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) : ℤ :=
  let e := parentOpenHeadFieldsEquivHeadChildOpenData n a C rest hC P
  headChildOpenDataInternalWeight n a C rest (e head) *
    chi (headChildOpenDataBoundaryExponent
      n a C rest hC P root (e head))

theorem parentHeadFieldsDataSignedSum_eq_sum_dataWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    parentHeadFieldsDataSignedSum n a C rest hC P root =
      ∑ head : ParentOpenHeadFields n a C rest,
        parentHeadFieldsDataWeightAtHead n a C rest hC P root head := by
  unfold parentHeadFieldsDataSignedSum parentHeadFieldsDataWeightAtHead
  rfl

theorem parentHeadFieldsDataSignedSum_eq_descScalar_mul_messageSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    parentHeadFieldsDataSignedSum n a C rest
        (child_positive_of_node hT C (by simp))
        (I.childPackage C (by simp)) root =
      (2 : ℤ) ^
          branchDescendantScalarExponent n a 0 C rest
            (child_positive_of_node hT C (by simp)) *
        headBranchMessageSignedSum n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) root := by
  rw [parentHeadFieldsDataSignedSum_eq_headChildPhysicalSignedSum]
  exact (HeadChildPhysicalPackageReduction.ofDataFubini
    n a C rest hT I).head_reduction_eq root

theorem parentHeadFieldsDataSignedSum_eq_if_headAllowed_branchScalar
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (ha : 0 < a)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    parentHeadFieldsDataSignedSum n a C rest hC P root =
      (by
        classical
        exact
          if headParentRootBoundaryFieldFromRoot n a C rest root ∈
              headAllowedBoundarySpace n a C rest hC P then
            (2 : ℤ) ^ branchScalarExponent n a 0 C rest
          else
            0) := by
  rw [parentHeadFieldsDataSignedSum_eq_headChildPhysicalSignedSum]
  exact headChildPhysicalSignedSum_eq_if_headAllowed_branchScalar
    n a C rest ha hC P root

theorem parentHeadFieldsDataSignedSum_of_head_allowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (ha : 0 < a)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest hC P →
      parentHeadFieldsDataSignedSum n a C rest hC P root =
        (2 : ℤ) ^ branchScalarExponent n a 0 C rest := by
  intro hhead
  rw [parentHeadFieldsDataSignedSum_eq_headChildPhysicalSignedSum]
  exact headChildPhysicalSignedSum_of_head_allowed
    n a C rest ha hC P root hhead

theorem parentHeadFieldsDataSignedSum_of_root_mem_packageAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageAllowedRootFieldSpace n a (C :: rest) hT I →
      parentHeadFieldsDataSignedSum n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) root =
        (2 : ℤ) ^ branchScalarExponent n a 0 C rest := by
  intro hroot
  rw [parentHeadFieldsDataSignedSum_eq_headChildPhysicalSignedSum]
  exact headChildPhysicalSignedSum_of_root_mem_packageAllowed
    n a C rest hT I hbridge root hroot

theorem parentHeadFieldsDataSignedSum_of_head_notAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBoundaryFieldFromRoot n a C rest root ∉
        headAllowedBoundarySpace n a C rest hC P →
      parentHeadFieldsDataSignedSum n a C rest hC P root = 0 := by
  intro hhead
  rw [parentHeadFieldsDataSignedSum_eq_headChildPhysicalSignedSum]
  exact headChildPhysicalSignedSum_of_head_notAllowed
    n a C rest hC P root hhead

theorem sum_parentHeadFieldsDataWeight_of_root_mem_packageAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageAllowedRootFieldSpace n a (C :: rest) hT I →
      (∑ head : ParentOpenHeadFields n a C rest,
        parentHeadFieldsDataWeightAtHead n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) root head) =
        (2 : ℤ) ^ branchScalarExponent n a 0 C rest := by
  intro hroot
  rw [← parentHeadFieldsDataSignedSum_eq_sum_dataWeight]
  exact
    parentHeadFieldsDataSignedSum_of_root_mem_packageAllowed
      n a C rest hT I hbridge root hroot

theorem sum_parentHeadFieldsDataWeight_of_head_notAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBoundaryFieldFromRoot n a C rest root ∉
        headAllowedBoundarySpace n a C rest hC P →
      (∑ head : ParentOpenHeadFields n a C rest,
        parentHeadFieldsDataWeightAtHead n a C rest hC P root head) =
        0 := by
  intro hhead
  rw [← parentHeadFieldsDataSignedSum_eq_sum_dataWeight]
  exact
    parentHeadFieldsDataSignedSum_of_head_notAllowed
      n a C rest hC P root hhead

end Imbalance
end TreeGraph
