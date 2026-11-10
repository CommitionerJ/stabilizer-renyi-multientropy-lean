import TreeGraph.Imbalance.NodeHeadParentFieldsReduction

namespace TreeGraph
namespace Imbalance

noncomputable def openNormalAssignmentCleanEquivHeadTail
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    OpenNormalAssignmentClean n (RTree.node a (C :: rest)) ≃
      ParentOpenHeadFields n a C rest ×
        ParentOpenTailFields n a C rest :=
  (openNormalAssignmentCleanEquivParentOpenByChild n a (C :: rest)).trans
    (parentOpenByChildConsEquiv n a C rest)

theorem openNormalAssignmentCleanEquivHeadTail_symm_fst
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) :
    ((openNormalAssignmentCleanEquivHeadTail n a C rest)
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))).1 = head := by
  exact congrArg Prod.fst
    ((openNormalAssignmentCleanEquivHeadTail n a C rest).right_inv
      (head, tail))

theorem openNormalAssignmentCleanEquivHeadTail_symm_snd
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) :
    ((openNormalAssignmentCleanEquivHeadTail n a C rest)
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))).2 = tail := by
  exact congrArg Prod.snd
    ((openNormalAssignmentCleanEquivHeadTail n a C rest).right_inv
      (head, tail))

theorem openNormalAssignmentCleanEquivHeadTail_symm_apply_head
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (v : Vertex C)
    (dom :
      NonRootFieldDomainClean n (RTree.node a (C :: rest))
        (childVertexAtAsNonRootInNode (a := a)
          ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v)))) :
    ((openNormalAssignmentCleanEquivHeadTail n a C rest)
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))).1 v dom =
      head v dom := by
  exact congrFun
    (congrFun
      (openNormalAssignmentCleanEquivHeadTail_symm_fst
        n a C rest head tail) v) dom

theorem openNormalAssignmentCleanEquivHeadTail_symm_apply_tail
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : NodeChildVertex rest)
    (dom :
      NonRootFieldDomainClean n (RTree.node a (C :: rest))
        (childVertexAtAsNonRootInNode (a := a)
          ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)))) :
    ((openNormalAssignmentCleanEquivHeadTail n a C rest)
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))).2 p dom =
      tail p dom := by
  exact congrFun
    (congrFun
      (openNormalAssignmentCleanEquivHeadTail_symm_snd
        n a C rest head tail) p) dom

noncomputable def parentOpenHeadTailSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) : ℤ :=
  by
    classical
    let e := openNormalAssignmentCleanEquivHeadTail n a C rest
    exact
      ∑ P : ParentOpenHeadFields n a C rest ×
          ParentOpenTailFields n a C rest,
        weightClean (RTree.node a (C :: rest))
          (closeOpenNormalAssignmentClean root (e.symm P))

theorem openNormalSignedSumClean_eq_parentOpenHeadTailSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      parentOpenHeadTailSignedSum n a C rest root := by
  classical
  unfold openNormalSignedSumClean parentOpenHeadTailSignedSum
  let e := openNormalAssignmentCleanEquivHeadTail n a C rest
  let F : OpenNormalAssignmentClean n (RTree.node a (C :: rest)) → ℤ :=
    fun A =>
      weightClean (RTree.node a (C :: rest))
        (closeOpenNormalAssignmentClean root A)
  change (∑ A : OpenNormalAssignmentClean n (RTree.node a (C :: rest)), F A) =
    ∑ P : ParentOpenHeadFields n a C rest × ParentOpenTailFields n a C rest,
      F (e.symm P)
  exact (Equiv.sum_comp e.symm F).symm

noncomputable def parentOpenHeadTailIterSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) : ℤ :=
  by
    classical
    let e := openNormalAssignmentCleanEquivHeadTail n a C rest
    exact
      ∑ head : ParentOpenHeadFields n a C rest,
        ∑ tail : ParentOpenTailFields n a C rest,
          weightClean (RTree.node a (C :: rest))
            (closeOpenNormalAssignmentClean root (e.symm (head, tail)))

noncomputable def parentOpenTailSignedSumAtHead
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) : ℤ :=
  by
    classical
    let e := openNormalAssignmentCleanEquivHeadTail n a C rest
    exact
      ∑ tail : ParentOpenTailFields n a C rest,
        weightClean (RTree.node a (C :: rest))
          (closeOpenNormalAssignmentClean root (e.symm (head, tail)))

theorem parentOpenHeadTailIterSignedSum_eq_sum_tailAtHead
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    parentOpenHeadTailIterSignedSum n a C rest root =
      ∑ head : ParentOpenHeadFields n a C rest,
        parentOpenTailSignedSumAtHead n a C rest root head := by
  classical
  unfold parentOpenHeadTailIterSignedSum parentOpenTailSignedSumAtHead
  rfl

theorem parentOpenHeadTailSignedSum_eq_iter
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    parentOpenHeadTailSignedSum n a C rest root =
      parentOpenHeadTailIterSignedSum n a C rest root := by
  classical
  unfold parentOpenHeadTailSignedSum parentOpenHeadTailIterSignedSum
  let e := openNormalAssignmentCleanEquivHeadTail n a C rest
  let F : ParentOpenHeadFields n a C rest ×
      ParentOpenTailFields n a C rest → ℤ :=
    fun P =>
      weightClean (RTree.node a (C :: rest))
        (closeOpenNormalAssignmentClean root (e.symm P))
  change (∑ P : ParentOpenHeadFields n a C rest ×
      ParentOpenTailFields n a C rest, F P) =
    ∑ head : ParentOpenHeadFields n a C rest,
      ∑ tail : ParentOpenTailFields n a C rest, F (head, tail)
  simpa using
    (Finset.sum_product
      (Finset.univ : Finset (ParentOpenHeadFields n a C rest))
      (Finset.univ : Finset (ParentOpenTailFields n a C rest))
      F)

theorem openNormalSignedSumClean_eq_parentOpenHeadTailIterSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      parentOpenHeadTailIterSignedSum n a C rest root := by
  rw [openNormalSignedSumClean_eq_parentOpenHeadTailSignedSum]
  rw [parentOpenHeadTailSignedSum_eq_iter]

theorem openNormalSignedSumClean_eq_sum_parentOpenTailSignedSumAtHead
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      ∑ head : ParentOpenHeadFields n a C rest,
        parentOpenTailSignedSumAtHead n a C rest root head := by
  rw [openNormalSignedSumClean_eq_parentOpenHeadTailIterSignedSum]
  rw [parentOpenHeadTailIterSignedSum_eq_sum_tailAtHead]

end Imbalance
end TreeGraph
