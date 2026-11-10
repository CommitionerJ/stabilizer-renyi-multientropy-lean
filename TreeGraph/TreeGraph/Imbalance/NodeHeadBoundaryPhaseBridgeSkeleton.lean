import TreeGraph.Imbalance.NodeHeadInternalPhaseLocal

namespace TreeGraph
namespace Imbalance

noncomputable def headBoundaryParentRootContext
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    Block n (a - 1) :=
  (headChildSiteContextOfParent n a C rest hC site).1

noncomputable def headBoundaryExtraRootCoord
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    Rep n :=
  (headChildSiteContextOfParent n a C rest hC site).2.1

noncomputable def headBoundaryTailCoords
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    CoordsList n rest :=
  (headChildSiteContextOfParent n a C rest hC site).2.2

noncomputable def headBoundaryParentRootKet
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  ketAtPathClean A site []

noncomputable def headBoundaryParentRootBra
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  braAtPathClean A site []

noncomputable def headBoundaryChildRootKet
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  ketAtPathClean A site [0]

noncomputable def headBoundaryChildRootBra
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  braAtPathClean A site [0]

noncomputable def headBoundaryPhaseLocalExpression
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  let _parentRootContext :=
    headBoundaryParentRootContext n a C rest hC site
  let _extraRootCoord :=
    headBoundaryExtraRootCoord n a C rest hC site
  let _tailCoords :=
    headBoundaryTailCoords n a C rest hC site
  headBoundaryParentRootKet A site * headBoundaryChildRootKet A site +
    headBoundaryParentRootBra A site * headBoundaryChildRootBra A site

theorem headBoundaryPhaseAtSiteClean_node_eq_local_expression
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryPhaseAtSiteClean_node C rest A site =
      headBoundaryPhaseLocalExpression n a C rest hC A site := by
  rfl

end Imbalance
end TreeGraph
