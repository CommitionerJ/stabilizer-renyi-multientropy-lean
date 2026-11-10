import TreeGraph.Imbalance.NodeHeadLocalAssignment

namespace TreeGraph
namespace Imbalance

noncomputable def headChildPulledKetAtPathFromParent
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (p : List Nat) : F2 :=
  ketAtPathClean A site (0 :: p)

noncomputable def headChildPulledBraAtPathFromParent
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (p : List Nat) : F2 :=
  braAtPathClean A site (0 :: p)

noncomputable def headChildPulledEdgePhaseFromParent
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (e : List Nat × List Nat) : F2 :=
  headChildPulledKetAtPathFromParent A site e.1 *
      headChildPulledKetAtPathFromParent A site e.2 +
    headChildPulledBraAtPathFromParent A site e.1 *
      headChildPulledBraAtPathFromParent A site e.2

theorem headChild_edgePhase_parent_eq_pulled
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (e : List Nat × List Nat) :
    edgePhaseAtSiteClean A site (RTree.prefixEdge [0] e) =
      headChildPulledEdgePhaseFromParent A site e := by
  cases e
  rfl

noncomputable def headChildPulledPhaseFromParent
    {n a : Nat} [NeZero n] (C : RTree) {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  ((RTree.edgeList C).map
    (headChildPulledEdgePhaseFromParent A site)).sum

theorem headInternalPhaseAtSiteClean_node_eq_child_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (_hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headInternalPhaseAtSiteClean_node C rest A site =
      headChildPulledPhaseFromParent C A site := by
  unfold headInternalPhaseAtSiteClean_node childInternalPhaseAtSiteClean_node
    headChildPulledPhaseFromParent
  change
    ((RTree.edgeListFrom [0] C).map (edgePhaseAtSiteClean A site)).sum =
      ((RTree.edgeList C).map
        (headChildPulledEdgePhaseFromParent A site)).sum
  have hlist :
      RTree.edgeListFrom [0] C =
        (RTree.edgeList C).map (RTree.prefixEdge [0]) := by
    simpa [RTree.edgeList] using
      (RTree.edgeListFrom_append_parent [0] [] C)
  rw [hlist]
  simp [List.map_map, Function.comp_def,
    headChild_edgePhase_parent_eq_pulled]

end Imbalance
end TreeGraph
