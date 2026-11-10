import TreeGraph.Imbalance.NodeHeadProjectionBridge
import TreeGraph.Imbalance.BranchTransfer

namespace TreeGraph
namespace Imbalance

noncomputable def headBranchMessageSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) : ℤ :=
  by
    classical
    letI : Fintype P.boundaryMessageSpace :=
      Fintype.ofFinite P.boundaryMessageSpace
    exact
      branchMessageSignedSum n
        (Block n (a - 1))
        (CoordsList n rest)
        (BranchField n C)
        P.boundaryMessageSpace
        (headChildR n C hC P)
        (headParentRootBranchFieldFromRoot n a C rest root)

theorem headParentRootBranch_mem_rtildeVisibleKernel_iff_headAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBranchFieldFromRoot n a C rest root ∈
        rtildeVisibleKernel n (CoordsList n rest)
          (BranchField n C) P.boundaryMessageSpace
          (headChildR n C hC P) ↔
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest hC P := by
  rfl

theorem headBranchMessageSignedSum_eq_if_headAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headBranchMessageSignedSum n a C rest hC P root =
      (by
        classical
        exact
          if headParentRootBoundaryFieldFromRoot n a C rest root ∈
              headAllowedBoundarySpace n a C rest hC P then
            (2 : ℤ) ^
              (Fintype.card (Block n (a - 1)) *
                Fintype.card (CoordsList n rest) * n *
                Module.finrank F2 P.boundaryMessageSpace)
          else
            0) := by
  classical
  letI : Fintype P.boundaryMessageSpace :=
    Fintype.ofFinite P.boundaryMessageSpace
  by_cases hhead :
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest hC P
  · have hbranch :
        headParentRootBranchFieldFromRoot n a C rest root ∈
          rtildeVisibleKernel n (CoordsList n rest)
            (BranchField n C) P.boundaryMessageSpace
            (headChildR n C hC P) :=
      (headParentRootBranch_mem_rtildeVisibleKernel_iff_headAllowed
        n a C rest hC P root).2 hhead
    have hsum :=
      branchMessageSignedSum_of_mem n
        (Block n (a - 1))
        (CoordsList n rest)
        (BranchField n C)
        P.boundaryMessageSpace
        (headChildR n C hC P)
        (headParentRootBranchFieldFromRoot n a C rest root)
        hbranch
    simpa [headBranchMessageSignedSum, hhead] using hsum
  · have hbranch :
        headParentRootBranchFieldFromRoot n a C rest root ∉
          rtildeVisibleKernel n (CoordsList n rest)
            (BranchField n C) P.boundaryMessageSpace
            (headChildR n C hC P) := by
      intro hmem
      exact hhead
        ((headParentRootBranch_mem_rtildeVisibleKernel_iff_headAllowed
          n a C rest hC P root).1 hmem)
    have hsum :=
      branchMessageSignedSum_of_not_mem n
        (Block n (a - 1))
        (CoordsList n rest)
        (BranchField n C)
        P.boundaryMessageSpace
        (headChildR n C hC P)
        (headParentRootBranchFieldFromRoot n a C rest root)
        hbranch
    simpa [headBranchMessageSignedSum, hhead] using hsum

theorem headBranchMessageExponent_eq_branchMessageScalarExponent
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Fintype.card (Block n (a - 1)) *
        Fintype.card (CoordsList n rest) * n *
        Module.finrank F2 P.boundaryMessageSpace =
      branchMessageScalarExponent n a 0 C rest hC := by
  unfold branchMessageScalarExponent branchMessageFamilyCardFactor
    rootMultiplicityCard visibleExternalCard
  rw [card_Block, card_CoordsList,
    OpenNormalCleanPackage.boundaryMessageSpace_finrank]
  simp

theorem headBranchMessageSignedSum_eq_if_headAllowed_branchScalar
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headBranchMessageSignedSum n a C rest hC P root =
      (by
        classical
        exact
          if headParentRootBoundaryFieldFromRoot n a C rest root ∈
              headAllowedBoundarySpace n a C rest hC P then
            (2 : ℤ) ^ branchMessageScalarExponent n a 0 C rest hC
          else
            0) := by
  rw [headBranchMessageSignedSum_eq_if_headAllowed]
  rw [headBranchMessageExponent_eq_branchMessageScalarExponent]

theorem headBranchMessageSignedSum_of_root_mem_packageAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageAllowedRootFieldSpace n a (C :: rest) hT I →
      headBranchMessageSignedSum n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) root =
        (2 : ℤ) ^
          branchMessageScalarExponent n a 0 C rest
            (child_positive_of_node hT C (by simp)) := by
  intro hroot
  have hhead :=
    root_mem_packageAllowedRootFieldSpace_imp_headParentRootBoundary_mem_headAllowed
      n a C rest hT I hbridge root hroot
  simpa [hhead] using
    headBranchMessageSignedSum_eq_if_headAllowed_branchScalar
      n a C rest
      (child_positive_of_node hT C (by simp))
      (I.childPackage C (by simp)) root

theorem headBranchMessageSignedSum_of_head_notAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBoundaryFieldFromRoot n a C rest root ∉
        headAllowedBoundarySpace n a C rest hC P →
      headBranchMessageSignedSum n a C rest hC P root = 0 := by
  intro hhead
  simpa [hhead] using
    headBranchMessageSignedSum_eq_if_headAllowed_branchScalar
      n a C rest hC P root

end Imbalance
end TreeGraph
