import TreeGraph.Imbalance.NodePhaseEdgeSplit

namespace TreeGraph
namespace Imbalance

noncomputable def childBoundaryPhaseAtSiteClean_node
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (A : NormalAssignmentClean n (RTree.node a cs))
    (site : NormalSiteClean n (RTree.node a cs))
    (j : Fin cs.length) : F2 :=
  edgePhaseAtSiteClean A site ([], [j.1])

theorem boundaryPhaseAtSiteClean_node_eq_sum_child
    (n a : Nat) [NeZero n] (cs : List RTree)
    (A : NormalAssignmentClean n (RTree.node a cs))
    (site : NormalSiteClean n (RTree.node a cs)) :
    boundaryPhaseAtSiteClean_node A site =
      ∑ j : Fin cs.length,
        childBoundaryPhaseAtSiteClean_node A site j := by
  unfold boundaryPhaseAtSiteClean_node childBoundaryPhaseAtSiteClean_node
  simpa using
    (RTree.indexedChildBoundaryEdgesFrom_map_sum_eq_sum_fin
      (edgePhaseAtSiteClean A site) [] 0 cs)

noncomputable def childInternalPhaseAtSiteClean_node
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (A : NormalAssignmentClean n (RTree.node a cs))
    (site : NormalSiteClean n (RTree.node a cs))
    (j : Fin cs.length) : F2 :=
  ((RTree.edgeListFrom [j.1] (childAt cs j)).map
    (edgePhaseAtSiteClean A site)).sum

theorem internalPhaseAtSiteClean_node_eq_sum_child
    (n a : Nat) [NeZero n] (cs : List RTree)
    (A : NormalAssignmentClean n (RTree.node a cs))
    (site : NormalSiteClean n (RTree.node a cs)) :
    internalPhaseAtSiteClean_node A site =
      ∑ j : Fin cs.length,
        childInternalPhaseAtSiteClean_node A site j := by
  unfold internalPhaseAtSiteClean_node childInternalPhaseAtSiteClean_node
  simpa using
    (RTree.indexedChildInternalEdgesFrom_map_sum_eq_sum_fin
      (edgePhaseAtSiteClean A site) [] 0 cs)

noncomputable def headBoundaryPhaseAtSiteClean_node
    {n : Nat} [NeZero n] {a : Nat} (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  childBoundaryPhaseAtSiteClean_node A site ⟨0, by simp⟩

noncomputable def tailBoundaryPhaseAtSiteClean_node
    {n : Nat} [NeZero n] {a : Nat} (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  ∑ j : Fin rest.length,
    childBoundaryPhaseAtSiteClean_node A site j.succ

noncomputable def headInternalPhaseAtSiteClean_node
    {n : Nat} [NeZero n] {a : Nat} (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  childInternalPhaseAtSiteClean_node A site ⟨0, by simp⟩

noncomputable def tailInternalPhaseAtSiteClean_node
    {n : Nat} [NeZero n] {a : Nat} (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  ∑ j : Fin rest.length,
    childInternalPhaseAtSiteClean_node A site j.succ

theorem boundaryPhaseAtSiteClean_node_cons_eq_head_add_tail
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    boundaryPhaseAtSiteClean_node A site =
      headBoundaryPhaseAtSiteClean_node C rest A site +
        tailBoundaryPhaseAtSiteClean_node C rest A site := by
  rw [boundaryPhaseAtSiteClean_node_eq_sum_child n a (C :: rest) A site]
  unfold headBoundaryPhaseAtSiteClean_node tailBoundaryPhaseAtSiteClean_node
  change
    (∑ j : Fin (rest.length + 1),
        childBoundaryPhaseAtSiteClean_node A site j) =
      childBoundaryPhaseAtSiteClean_node A site 0 +
        ∑ j : Fin rest.length,
          childBoundaryPhaseAtSiteClean_node A site j.succ
  exact Fin.sum_univ_succ
    (fun j : Fin (rest.length + 1) =>
      childBoundaryPhaseAtSiteClean_node A site j)

theorem internalPhaseAtSiteClean_node_cons_eq_head_add_tail
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    internalPhaseAtSiteClean_node A site =
      headInternalPhaseAtSiteClean_node C rest A site +
        tailInternalPhaseAtSiteClean_node C rest A site := by
  rw [internalPhaseAtSiteClean_node_eq_sum_child n a (C :: rest) A site]
  unfold headInternalPhaseAtSiteClean_node tailInternalPhaseAtSiteClean_node
  change
    (∑ j : Fin (rest.length + 1),
        childInternalPhaseAtSiteClean_node A site j) =
      childInternalPhaseAtSiteClean_node A site 0 +
        ∑ j : Fin rest.length,
          childInternalPhaseAtSiteClean_node A site j.succ
  exact Fin.sum_univ_succ
    (fun j : Fin (rest.length + 1) =>
      childInternalPhaseAtSiteClean_node A site j)

noncomputable def totalHeadBoundaryPhaseClean_node
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) : F2 :=
  ∑ site : NormalSiteClean n (RTree.node a (C :: rest)),
    headBoundaryPhaseAtSiteClean_node C rest A site

noncomputable def totalTailBoundaryPhaseClean_node
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) : F2 :=
  ∑ site : NormalSiteClean n (RTree.node a (C :: rest)),
    tailBoundaryPhaseAtSiteClean_node C rest A site

noncomputable def totalHeadInternalPhaseClean_node
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) : F2 :=
  ∑ site : NormalSiteClean n (RTree.node a (C :: rest)),
    headInternalPhaseAtSiteClean_node C rest A site

noncomputable def totalTailInternalPhaseClean_node
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) : F2 :=
  ∑ site : NormalSiteClean n (RTree.node a (C :: rest)),
    tailInternalPhaseAtSiteClean_node C rest A site

noncomputable def totalHeadPhaseClean_node
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) : F2 :=
  totalHeadBoundaryPhaseClean_node n a C rest A +
    totalHeadInternalPhaseClean_node n a C rest A

noncomputable def totalTailPhaseClean_node
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) : F2 :=
  totalTailBoundaryPhaseClean_node n a C rest A +
    totalTailInternalPhaseClean_node n a C rest A

theorem totalBoundaryPhaseClean_node_cons_eq_head_add_tail
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    totalBoundaryPhaseClean_node n a (C :: rest) A =
      totalHeadBoundaryPhaseClean_node n a C rest A +
        totalTailBoundaryPhaseClean_node n a C rest A := by
  unfold totalBoundaryPhaseClean_node totalHeadBoundaryPhaseClean_node
    totalTailBoundaryPhaseClean_node
  calc
    (∑ site : NormalSiteClean n (RTree.node a (C :: rest)),
        boundaryPhaseAtSiteClean_node A site) =
        Finset.univ.sum
          (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
            headBoundaryPhaseAtSiteClean_node C rest A site +
              tailBoundaryPhaseAtSiteClean_node C rest A site) := by
      refine Finset.sum_congr rfl ?_
      intro site _
      exact boundaryPhaseAtSiteClean_node_cons_eq_head_add_tail
        n a C rest A site
    _ =
        (∑ site : NormalSiteClean n (RTree.node a (C :: rest)),
          headBoundaryPhaseAtSiteClean_node C rest A site) +
        (∑ site : NormalSiteClean n (RTree.node a (C :: rest)),
          tailBoundaryPhaseAtSiteClean_node C rest A site) := by
      exact Finset.sum_add_distrib

theorem totalInternalPhaseClean_node_cons_eq_head_add_tail
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    totalInternalPhaseClean_node n a (C :: rest) A =
      totalHeadInternalPhaseClean_node n a C rest A +
        totalTailInternalPhaseClean_node n a C rest A := by
  unfold totalInternalPhaseClean_node totalHeadInternalPhaseClean_node
    totalTailInternalPhaseClean_node
  calc
    (∑ site : NormalSiteClean n (RTree.node a (C :: rest)),
        internalPhaseAtSiteClean_node A site) =
        Finset.univ.sum
          (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
            headInternalPhaseAtSiteClean_node C rest A site +
              tailInternalPhaseAtSiteClean_node C rest A site) := by
      refine Finset.sum_congr rfl ?_
      intro site _
      exact internalPhaseAtSiteClean_node_cons_eq_head_add_tail
        n a C rest A site
    _ =
        (∑ site : NormalSiteClean n (RTree.node a (C :: rest)),
          headInternalPhaseAtSiteClean_node C rest A site) +
        (∑ site : NormalSiteClean n (RTree.node a (C :: rest)),
          tailInternalPhaseAtSiteClean_node C rest A site) := by
      exact Finset.sum_add_distrib

theorem totalPhaseClean_node_cons_eq_head_add_tail
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    totalPhaseClean (RTree.node a (C :: rest)) A =
      totalHeadPhaseClean_node n a C rest A +
        totalTailPhaseClean_node n a C rest A := by
  rw [totalPhaseClean_node_eq_boundary_add_internal n a (C :: rest) A]
  rw [totalBoundaryPhaseClean_node_cons_eq_head_add_tail n a C rest A]
  rw [totalInternalPhaseClean_node_cons_eq_head_add_tail n a C rest A]
  unfold totalHeadPhaseClean_node totalTailPhaseClean_node
  ac_rfl

theorem weightClean_node_cons_eq_head_mul_tail
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    weightClean (RTree.node a (C :: rest)) A =
      chi (totalHeadPhaseClean_node n a C rest A) *
        chi (totalTailPhaseClean_node n a C rest A) := by
  unfold weightClean
  rw [totalPhaseClean_node_cons_eq_head_add_tail n a C rest A]
  rw [chi_add]

end Imbalance
end TreeGraph
