import TreeGraph.Imbalance.NodeHeadBoundaryOpenBridge
import TreeGraph.Imbalance.NodeHeadSlice

namespace TreeGraph
namespace Imbalance

noncomputable def headParentRootBoundaryFieldFromRoot
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    BoundaryField n (RTree.node a (C :: rest)) :=
  (RootFieldCleanCopenBridge.node n a (C :: rest)).linearEquiv root

noncomputable def headParentRootBranchFieldFromRoot
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : CoordsList n rest) : BranchField n C :=
  (boundaryHeadSliceLinearEquiv n a C rest
    (headParentRootBoundaryFieldFromRoot n a C rest root)) tail

theorem headParentRootBranchFieldFromRoot_eq_slice
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : CoordsList n rest) :
    headParentRootBranchFieldFromRoot n a C rest root tail =
      (boundaryHeadSliceLinearEquiv n a C rest
        ((RootFieldCleanCopenBridge.node n a (C :: rest)).linearEquiv root))
        tail := by
  rfl

noncomputable def headBoundaryOpenPairingExpressionAtSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  let s :=
    diagonalClean site
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
  headBoundaryParentRootKet (closeOpenNormalAssignmentClean root Aopen) site *
      headChildRootBoundaryFieldFromParentSite Aopen site s +
    headBoundaryParentRootBra (closeOpenNormalAssignmentClean root Aopen) site *
      headChildRootBoundaryFieldFromParentSite Aopen site (s + 1)

theorem headBoundaryPhaseLocalExpression_eq_openPairingAtSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryPhaseLocalExpression n a C rest hC
        (closeOpenNormalAssignmentClean root Aopen) site =
      headBoundaryOpenPairingExpressionAtSite n a C rest root Aopen site := by
  unfold headBoundaryPhaseLocalExpression headBoundaryOpenPairingExpressionAtSite
  rw [headBoundaryChildRootKet_eq_boundaryFamilyAtSite n a C rest root Aopen site]
  rw [headBoundaryChildRootBra_eq_boundaryFamilyAtSite_succ n a C rest root Aopen site]

theorem headBoundaryPhaseAtSiteClean_node_eq_openPairingAtSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryPhaseAtSiteClean_node C rest
        (closeOpenNormalAssignmentClean root Aopen) site =
      headBoundaryOpenPairingExpressionAtSite n a C rest root Aopen site := by
  rw [headBoundaryPhaseAtSiteClean_node_eq_local_expression n a C rest hC]
  exact headBoundaryPhaseLocalExpression_eq_openPairingAtSite
    n a C rest hC root Aopen site

end Imbalance
end TreeGraph
