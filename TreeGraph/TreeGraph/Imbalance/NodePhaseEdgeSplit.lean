import TreeGraph.Imbalance.NodeOpenAssignmentSplit

namespace TreeGraph
namespace Imbalance

noncomputable def boundaryPhaseAtSiteClean_node
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (A : NormalAssignmentClean n (RTree.node a cs))
    (site : NormalSiteClean n (RTree.node a cs)) : F2 :=
  ((RTree.indexedChildBoundaryEdgesFrom [] 0 cs).map
    (edgePhaseAtSiteClean A site)).sum

noncomputable def internalPhaseAtSiteClean_node
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (A : NormalAssignmentClean n (RTree.node a cs))
    (site : NormalSiteClean n (RTree.node a cs)) : F2 :=
  ((RTree.indexedChildInternalEdgesFrom [] 0 cs).map
    (edgePhaseAtSiteClean A site)).sum

theorem phaseAtSiteClean_node_eq_boundary_add_internal
    (n a : Nat) [NeZero n] (cs : List RTree)
    (A : NormalAssignmentClean n (RTree.node a cs))
    (site : NormalSiteClean n (RTree.node a cs)) :
    phaseAtSiteClean (RTree.node a cs) A site =
      boundaryPhaseAtSiteClean_node A site +
        internalPhaseAtSiteClean_node A site := by
  unfold phaseAtSiteClean boundaryPhaseAtSiteClean_node
    internalPhaseAtSiteClean_node
  exact RTree.edgeList_node_map_sum_eq_boundary_add_internal
    (edgePhaseAtSiteClean A site) a cs

noncomputable def totalBoundaryPhaseClean_node
    (n a : Nat) [NeZero n] (cs : List RTree)
    (A : NormalAssignmentClean n (RTree.node a cs)) : F2 :=
  ∑ site : NormalSiteClean n (RTree.node a cs),
    boundaryPhaseAtSiteClean_node A site

noncomputable def totalInternalPhaseClean_node
    (n a : Nat) [NeZero n] (cs : List RTree)
    (A : NormalAssignmentClean n (RTree.node a cs)) : F2 :=
  ∑ site : NormalSiteClean n (RTree.node a cs),
    internalPhaseAtSiteClean_node A site

theorem totalPhaseClean_node_eq_boundary_add_internal
    (n a : Nat) [NeZero n] (cs : List RTree)
    (A : NormalAssignmentClean n (RTree.node a cs)) :
    totalPhaseClean (RTree.node a cs) A =
      totalBoundaryPhaseClean_node n a cs A +
        totalInternalPhaseClean_node n a cs A := by
  unfold totalPhaseClean totalBoundaryPhaseClean_node
    totalInternalPhaseClean_node
  calc
    (∑ site : NormalSiteClean n (RTree.node a cs),
        phaseAtSiteClean (RTree.node a cs) A site) =
        Finset.univ.sum
          (fun site : NormalSiteClean n (RTree.node a cs) =>
            boundaryPhaseAtSiteClean_node A site +
              internalPhaseAtSiteClean_node A site) := by
      refine Finset.sum_congr rfl ?_
      intro site _
      exact phaseAtSiteClean_node_eq_boundary_add_internal n a cs A site
    _ =
        (∑ site : NormalSiteClean n (RTree.node a cs),
          boundaryPhaseAtSiteClean_node A site) +
        (∑ site : NormalSiteClean n (RTree.node a cs),
          internalPhaseAtSiteClean_node A site) := by
      exact Finset.sum_add_distrib

end Imbalance
end TreeGraph
