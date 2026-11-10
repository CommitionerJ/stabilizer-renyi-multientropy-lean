import TreeGraph.Imbalance.NodeOpenExponent
import TreeGraph.Imbalance.NodeCanonicalInputSanity

namespace TreeGraph
namespace Imbalance

theorem canonical_root_mem_packageAllowedRootFieldSpace_iff_head_tailRootRows
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ C :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈
        packageAllowedRootFieldSpace n a (C :: rest) hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage) ↔
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
          headAllowedBoundarySpace n a C rest
            (child_positive_of_node hT C (by simp))
            (childPackage C (by simp)) ∧
        ∀ p : Cplus n C,
          tailRootFieldFromHeadCplus n a C rest root p ∈
            packageAllowedRootFieldSpace n a rest
              (positiveWeights_node_tail_of_cons hT)
              (nodeTailInputsOfCons n a C rest hT
                (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                  n a (C :: rest) hT childPackage)) := by
  simpa [NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages]
    using
      root_mem_packageAllowedRootFieldSpace_iff_head_tailRootRows
        n a C rest hT
        (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
          n a (C :: rest) hT childPackage)
        rfl root

theorem canonical_root_not_mem_packageAllowedRootFieldSpace_iff_head_tailRoot
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ C :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∉
        packageAllowedRootFieldSpace n a (C :: rest) hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage) ↔
      headParentRootBoundaryFieldFromRoot n a C rest root ∉
          headAllowedBoundarySpace n a C rest
            (child_positive_of_node hT C (by simp))
            (childPackage C (by simp)) ∨
        ∃ p : Cplus n C,
          tailRootFieldFromHeadCplus n a C rest root p ∉
            packageAllowedRootFieldSpace n a rest
              (positiveWeights_node_tail_of_cons hT)
              (nodeTailInputsOfCons n a C rest hT
                (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                  n a (C :: rest) hT childPackage)) := by
  simpa [NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages]
    using
      root_not_mem_packageAllowedRootFieldSpace_iff_head_notAllowed_or_exists_tailRoot
        n a C rest hT
        (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
          n a (C :: rest) hT childPackage)
        rfl root

theorem canonical_parentHeadFieldsDataSignedSum_of_root_mem_packageAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ C :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈
        packageAllowedRootFieldSpace n a (C :: rest) hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage) →
      parentHeadFieldsDataSignedSum n a C rest
          (child_positive_of_node hT C (by simp))
          (childPackage C (by simp)) root =
        (2 : ℤ) ^ branchScalarExponent n a 0 C rest := by
  intro hroot
  simpa [NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages]
    using
      parentHeadFieldsDataSignedSum_of_root_mem_packageAllowed
        n a C rest hT
        (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
          n a (C :: rest) hT childPackage)
        rfl root hroot

theorem canonical_parentHeadFieldsDataSignedSum_of_root_not_headAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ C :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBoundaryFieldFromRoot n a C rest root ∉
        headAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (childPackage C (by simp)) →
      parentHeadFieldsDataSignedSum n a C rest
          (child_positive_of_node hT C (by simp))
          (childPackage C (by simp)) root = 0 := by
  intro hhead
  exact
    parentHeadFieldsDataSignedSum_of_head_notAllowed
      n a C rest
      (child_positive_of_node hT C (by simp))
      (childPackage C (by simp)) root hhead

end Imbalance
end TreeGraph
