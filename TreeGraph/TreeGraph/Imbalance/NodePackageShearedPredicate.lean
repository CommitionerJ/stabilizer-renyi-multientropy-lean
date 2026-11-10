import TreeGraph.Imbalance.NodePackageShearedStepCertificate

namespace TreeGraph
namespace Imbalance

def rootShearedHeadTailAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hT : RTree.PositiveWeights
      (RTree.node a (RTree.node b ds :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ RTree.node b ds :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest))) : Prop :=
  headParentRootBoundaryFieldFromRoot
      n a (RTree.node b ds) rest root ∈
      headShearedAllowedBoundarySpace
        n a (RTree.node b ds) rest
        (child_positive_of_node hT (RTree.node b ds) (by simp))
        (childPackage (RTree.node b ds) (by simp)) ∧
    ∀ p : Cplus n (RTree.node b ds),
      tailRootFieldFromHeadCplus
        n a (RTree.node b ds) rest root p ∈
        packageShearedAllowedRootFieldSpace n a rest
          (positiveWeights_node_tail_of_cons hT)
          (nodeTailInputsOfCons
            n a (RTree.node b ds) rest hT
            (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
              n a (RTree.node b ds :: rest) hT childPackage))

open Classical in
theorem canonical_openNormalSignedSumClean_node_cons_eq_if_rootShearedHeadTailAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hT : RTree.PositiveWeights
      (RTree.node a (RTree.node b ds :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ RTree.node b ds :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (Wtail :
      NodeShearedOpenPackageStepCertificate n a rest
        (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a (RTree.node b ds) rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (RTree.node b ds :: rest) hT childPackage)))
    (hPhead :
      (childPackage (RTree.node b ds) (by simp)).IsCanonical)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest))) :
    openNormalSignedSumClean
        n (RTree.node a (RTree.node b ds :: rest)) root =
      if rootShearedHeadTailAllowed n a b ds rest hT childPackage root then
        (2 : ℤ) ^
          (Xdim n (RTree.node a (RTree.node b ds :: rest)) -
            Ydim n (RTree.node a (RTree.node b ds :: rest)) hT)
      else
        0 := by
  let I :
      NodeOpenPackageStepInputs n a (RTree.node b ds :: rest) hT :=
    NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
      n a (RTree.node b ds :: rest) hT childPackage
  have hrootIff :
      root ∈ packageShearedAllowedRootFieldSpace
          n a (RTree.node b ds :: rest) hT I ↔
        rootShearedHeadTailAllowed n a b ds rest hT childPackage root := by
    simpa [rootShearedHeadTailAllowed, I] using
      (root_mem_packageShearedAllowedRootFieldSpace_iff_head_tailRootRows
        n a (RTree.node b ds) rest hT I
        (by
          simp [I])
        root)
  rw [canonical_openNormalSignedSumClean_node_cons_eq_if_packageShearedAllowed
    n a b ds rest hT childPackage Wtail hPhead root]
  by_cases hroot :
      rootShearedHeadTailAllowed n a b ds rest hT childPackage root
  · rw [if_pos ((hrootIff).2 hroot), if_pos hroot]
  · rw [if_neg (by
      intro hmem
      exact hroot ((hrootIff).1 hmem)), if_neg hroot]

theorem canonical_openNormalSignedSumClean_node_cons_of_rootShearedHeadTailAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hT : RTree.PositiveWeights
      (RTree.node a (RTree.node b ds :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ RTree.node b ds :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (Wtail :
      NodeShearedOpenPackageStepCertificate n a rest
        (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a (RTree.node b ds) rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (RTree.node b ds :: rest) hT childPackage)))
    (hPhead :
      (childPackage (RTree.node b ds) (by simp)).IsCanonical)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest))) :
    rootShearedHeadTailAllowed n a b ds rest hT childPackage root →
      openNormalSignedSumClean
          n (RTree.node a (RTree.node b ds :: rest)) root =
        (2 : ℤ) ^
          (Xdim n (RTree.node a (RTree.node b ds :: rest)) -
            Ydim n (RTree.node a (RTree.node b ds :: rest)) hT) := by
  intro hroot
  rw [canonical_openNormalSignedSumClean_node_cons_eq_if_rootShearedHeadTailAllowed
    n a b ds rest hT childPackage Wtail hPhead root]
  rw [if_pos hroot]

theorem canonical_openNormalSignedSumClean_node_cons_of_not_rootShearedHeadTailAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hT : RTree.PositiveWeights
      (RTree.node a (RTree.node b ds :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ RTree.node b ds :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (Wtail :
      NodeShearedOpenPackageStepCertificate n a rest
        (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a (RTree.node b ds) rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (RTree.node b ds :: rest) hT childPackage)))
    (hPhead :
      (childPackage (RTree.node b ds) (by simp)).IsCanonical)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest))) :
    ¬ rootShearedHeadTailAllowed n a b ds rest hT childPackage root →
      openNormalSignedSumClean
          n (RTree.node a (RTree.node b ds :: rest)) root = 0 := by
  intro hroot
  rw [canonical_openNormalSignedSumClean_node_cons_eq_if_rootShearedHeadTailAllowed
    n a b ds rest hT childPackage Wtail hPhead root]
  rw [if_neg hroot]

end Imbalance
end TreeGraph
