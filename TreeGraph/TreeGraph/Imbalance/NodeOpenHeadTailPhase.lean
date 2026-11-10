import TreeGraph.Imbalance.NodeOpenHeadTailReindex
import TreeGraph.Imbalance.NodeChildPhaseDecomposition

namespace TreeGraph
namespace Imbalance

noncomputable def parentOpenTailPhaseProductAtHead
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) : ℤ :=
  by
    classical
    let e := openNormalAssignmentCleanEquivHeadTail n a C rest
    exact
      ∑ tail : ParentOpenTailFields n a C rest,
        let A :=
          closeOpenNormalAssignmentClean root (e.symm (head, tail))
        chi (totalHeadPhaseClean_node n a C rest A) *
          chi (totalTailPhaseClean_node n a C rest A)

noncomputable def parentOpenTailPhaseSignedSumAtHead
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) : ℤ :=
  by
    classical
    let e := openNormalAssignmentCleanEquivHeadTail n a C rest
    exact
      ∑ tail : ParentOpenTailFields n a C rest,
        let A :=
          closeOpenNormalAssignmentClean root (e.symm (head, tail))
        chi (totalTailPhaseClean_node n a C rest A)

theorem parentOpenTailSignedSumAtHead_eq_phaseProduct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) :
    parentOpenTailSignedSumAtHead n a C rest root head =
      parentOpenTailPhaseProductAtHead n a C rest root head := by
  classical
  unfold parentOpenTailSignedSumAtHead parentOpenTailPhaseProductAtHead
  let e := openNormalAssignmentCleanEquivHeadTail n a C rest
  refine Finset.sum_congr rfl ?_
  intro tail _
  rw [weightClean_node_cons_eq_head_mul_tail]

theorem parentOpenTailPhaseProductAtHead_eq_headFactor_mul_tailPhaseSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (headFactor : ℤ)
    (hhead :
      ∀ tail : ParentOpenTailFields n a C rest,
        let e := openNormalAssignmentCleanEquivHeadTail n a C rest
        let A :=
          closeOpenNormalAssignmentClean root (e.symm (head, tail))
        chi (totalHeadPhaseClean_node n a C rest A) = headFactor) :
    parentOpenTailPhaseProductAtHead n a C rest root head =
      headFactor *
        parentOpenTailPhaseSignedSumAtHead n a C rest root head := by
  classical
  unfold parentOpenTailPhaseProductAtHead parentOpenTailPhaseSignedSumAtHead
  let e := openNormalAssignmentCleanEquivHeadTail n a C rest
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro tail _
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm (head, tail))
  have hA :
      chi (totalHeadPhaseClean_node n a C rest A) = headFactor := by
    simpa [A] using hhead tail
  change
    chi (totalHeadPhaseClean_node n a C rest A) *
        chi (totalTailPhaseClean_node n a C rest A) =
      headFactor * chi (totalTailPhaseClean_node n a C rest A)
  rw [hA]

theorem openNormalSignedSumClean_eq_sum_parentOpenTailPhaseProductAtHead
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      ∑ head : ParentOpenHeadFields n a C rest,
        parentOpenTailPhaseProductAtHead n a C rest root head := by
  rw [openNormalSignedSumClean_eq_sum_parentOpenTailSignedSumAtHead]
  refine Finset.sum_congr rfl ?_
  intro head _
  rw [parentOpenTailSignedSumAtHead_eq_phaseProduct]

theorem openNormalSignedSumClean_eq_sum_headFactor_mul_tailPhaseSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (headFactor : ParentOpenHeadFields n a C rest → ℤ)
    (hhead :
      ∀ head : ParentOpenHeadFields n a C rest,
        ∀ tail : ParentOpenTailFields n a C rest,
          let e := openNormalAssignmentCleanEquivHeadTail n a C rest
          let A :=
            closeOpenNormalAssignmentClean root (e.symm (head, tail))
          chi (totalHeadPhaseClean_node n a C rest A) =
            headFactor head) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      ∑ head : ParentOpenHeadFields n a C rest,
        headFactor head *
          parentOpenTailPhaseSignedSumAtHead n a C rest root head := by
  classical
  rw [openNormalSignedSumClean_eq_sum_parentOpenTailPhaseProductAtHead]
  refine Finset.sum_congr rfl ?_
  intro head _
  exact parentOpenTailPhaseProductAtHead_eq_headFactor_mul_tailPhaseSignedSum
    n a C rest root head (headFactor head) (hhead head)

end Imbalance
end TreeGraph
