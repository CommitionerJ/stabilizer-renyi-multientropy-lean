import TreeGraph.Imbalance.NodeRootCopenBridgeCanonical
import TreeGraph.Imbalance.OpenNormalBridge

namespace TreeGraph
namespace Imbalance

abbrev ParentOpenFieldAt
    (n a : Nat) [NeZero n] (cs : List RTree)
    (p : NodeChildVertex cs) : Type :=
  NonRootFieldDomainClean n (RTree.node a cs)
    (childVertexAtAsNonRootInNode (a := a) p) → F2

abbrev ParentOpenByChild
    (n a : Nat) [NeZero n] (cs : List RTree) : Type :=
  (p : NodeChildVertex cs) → ParentOpenFieldAt n a cs p

def castNonRootFieldDomainCleanOfEq
    {n : Nat} [NeZero n] {T : RTree}
    {v w : NonRootVertex T} (h : v = w) :
    NonRootFieldDomainClean n T v ≃ NonRootFieldDomainClean n T w := by
  subst h
  exact Equiv.refl _

theorem nonRootVertexNodeEquivChildVertex_to_child
    {a : Nat} {cs : List RTree}
    (v : NonRootVertex (RTree.node a cs)) :
    childVertexAtAsNonRootInNode (a := a)
      ((nonRootVertexNodeEquivChildVertex a cs) v) = v :=
  (nonRootVertexNodeEquivChildVertex a cs).left_inv v

noncomputable def openNormalAssignmentCleanEquivNodeFields
    (n a : Nat) [NeZero n] (cs : List RTree) :
    OpenNormalAssignmentClean n (RTree.node a cs) ≃
      ((v : NonRootVertex (RTree.node a cs)) →
        NonRootFieldDomainClean n (RTree.node a cs) v → F2) where
  toFun A := A.nodeField
  invFun f := { nodeField := f }
  left_inv A := by
    cases A
    rfl
  right_inv f := rfl

noncomputable def openNormalAssignmentCleanEquivParentOpenByChild
    (n a : Nat) [NeZero n] (cs : List RTree) :
    OpenNormalAssignmentClean n (RTree.node a cs) ≃
      ParentOpenByChild n a cs :=
  (openNormalAssignmentCleanEquivNodeFields n a cs).trans
    ((Equiv.piCongrRight
      (fun v : NonRootVertex (RTree.node a cs) =>
        Equiv.arrowCongr
          (castNonRootFieldDomainCleanOfEq
            (nonRootVertexNodeEquivChildVertex_to_child
              (a := a) (cs := cs) v).symm)
          (Equiv.refl F2))).trans
      (Equiv.piCongrLeft
        (fun p : NodeChildVertex cs => ParentOpenFieldAt n a cs p)
        (nonRootVertexNodeEquivChildVertex a cs)))

theorem castNonRootFieldDomainCleanOfEq_apply_heq
    {n : Nat} [NeZero n] {T : RTree}
    {v w : NonRootVertex T}
    (h : v = w) (dom : NonRootFieldDomainClean n T v) :
    HEq ((castNonRootFieldDomainCleanOfEq h) dom) dom := by
  subst h
  rfl

theorem parentOpenByChild_congr_heq
    (n a : Nat) [NeZero n] (cs : List RTree)
    (F : ParentOpenByChild n a cs)
    (q p : NodeChildVertex cs)
    (domq :
      NonRootFieldDomainClean n (RTree.node a cs)
        (childVertexAtAsNonRootInNode (a := a) q))
    (domp :
      NonRootFieldDomainClean n (RTree.node a cs)
        (childVertexAtAsNonRootInNode (a := a) p))
    (hp : q = p) (hdom : HEq domq domp) :
    F q domq = F p domp := by
  let X : Sigma fun q : NodeChildVertex cs =>
      NonRootFieldDomainClean n (RTree.node a cs)
        (childVertexAtAsNonRootInNode (a := a) q) := ⟨q, domq⟩
  let Y : Sigma fun q : NodeChildVertex cs =>
      NonRootFieldDomainClean n (RTree.node a cs)
        (childVertexAtAsNonRootInNode (a := a) q) := ⟨p, domp⟩
  change
    (fun Z : Sigma fun q : NodeChildVertex cs =>
      NonRootFieldDomainClean n (RTree.node a cs)
        (childVertexAtAsNonRootInNode (a := a) q) => F Z.1 Z.2) X =
    (fun Z : Sigma fun q : NodeChildVertex cs =>
      NonRootFieldDomainClean n (RTree.node a cs)
        (childVertexAtAsNonRootInNode (a := a) q) => F Z.1 Z.2) Y
  exact
    congrArg
      (fun Z : Sigma fun q : NodeChildVertex cs =>
        NonRootFieldDomainClean n (RTree.node a cs)
          (childVertexAtAsNonRootInNode (a := a) q) => F Z.1 Z.2)
      (Sigma.ext hp hdom)

theorem openNormalAssignmentCleanEquivParentOpenByChild_symm_nodeField
    (n a : Nat) [NeZero n] (cs : List RTree)
    (F : ParentOpenByChild n a cs)
    (p : NodeChildVertex cs)
    (dom :
      NonRootFieldDomainClean n (RTree.node a cs)
        (childVertexAtAsNonRootInNode (a := a) p)) :
    ((openNormalAssignmentCleanEquivParentOpenByChild n a cs).symm F).nodeField
      (childVertexAtAsNonRootInNode (a := a) p) dom = F p dom := by
  unfold openNormalAssignmentCleanEquivParentOpenByChild
    openNormalAssignmentCleanEquivNodeFields
  simp [Equiv.piCongrLeft, Equiv.piCongrRight]
  let q :=
    (nonRootVertexNodeEquivChildVertex a cs)
      (childVertexAtAsNonRootInNode (a := a) p)
  change
    F q
      ((castNonRootFieldDomainCleanOfEq
        ((nonRootVertexNodeEquivChildVertex_to_child
          (a := a) (cs := cs)
          (childVertexAtAsNonRootInNode (a := a) p)).symm)) dom) =
      F p dom
  exact
    parentOpenByChild_congr_heq n a cs F q p
      ((castNonRootFieldDomainCleanOfEq
        ((nonRootVertexNodeEquivChildVertex_to_child
          (a := a) (cs := cs)
          (childVertexAtAsNonRootInNode (a := a) p)).symm)) dom)
      dom
      (by
        dsimp [q]
        exact (nonRootVertexNodeEquivChildVertex a cs).right_inv p)
      (castNonRootFieldDomainCleanOfEq_apply_heq _ dom)

theorem openNormalAssignmentCleanEquivParentOpenByChild_apply
    (n a : Nat) [NeZero n] (cs : List RTree)
    (A : OpenNormalAssignmentClean n (RTree.node a cs))
    (p : NodeChildVertex cs)
    (dom :
      NonRootFieldDomainClean n (RTree.node a cs)
        (childVertexAtAsNonRootInNode (a := a) p)) :
    ((openNormalAssignmentCleanEquivParentOpenByChild n a cs) A) p dom =
      A.nodeField (childVertexAtAsNonRootInNode (a := a) p) dom := by
  let e := openNormalAssignmentCleanEquivParentOpenByChild n a cs
  let F := e A
  have hselector :
      (e.symm F).nodeField
          (childVertexAtAsNonRootInNode (a := a) p) dom =
        F p dom := by
    exact openNormalAssignmentCleanEquivParentOpenByChild_symm_nodeField
      n a cs F p dom
  have hleft :
      (e.symm F).nodeField
          (childVertexAtAsNonRootInNode (a := a) p) dom =
        A.nodeField (childVertexAtAsNonRootInNode (a := a) p) dom := by
    exact
      congrArg
        (fun B : OpenNormalAssignmentClean n (RTree.node a cs) =>
          B.nodeField (childVertexAtAsNonRootInNode (a := a) p) dom)
        (e.left_inv A)
  calc
    ((openNormalAssignmentCleanEquivParentOpenByChild n a cs) A) p dom =
        F p dom := rfl
    _ =
        (e.symm F).nodeField
          (childVertexAtAsNonRootInNode (a := a) p) dom := hselector.symm
    _ =
        A.nodeField (childVertexAtAsNonRootInNode (a := a) p) dom := hleft

abbrev ParentOpenConsSumFields
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) : Type :=
  (s : Vertex C ⊕ NodeChildVertex rest) →
    ParentOpenFieldAt n a (C :: rest)
      ((nodeChildVertexConsEquiv C rest).symm s)

abbrev ParentOpenHeadFields
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) : Type :=
  (v : Vertex C) →
    ParentOpenFieldAt n a (C :: rest)
      ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))

abbrev ParentOpenTailFields
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) : Type :=
  (p : NodeChildVertex rest) →
    ParentOpenFieldAt n a (C :: rest)
      ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))

noncomputable def parentOpenByChildConsEquivSum
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    ParentOpenByChild n a (C :: rest) ≃
      ParentOpenConsSumFields n a C rest :=
  Equiv.piCongrLeft
    (fun p : NodeChildVertex (C :: rest) =>
      ParentOpenFieldAt n a (C :: rest) p)
    (nodeChildVertexConsEquiv C rest).symm |>.symm

noncomputable def parentOpenByChildConsEquiv
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    ParentOpenByChild n a (C :: rest) ≃
      ParentOpenHeadFields n a C rest ×
        ParentOpenTailFields n a C rest :=
  (parentOpenByChildConsEquivSum n a C rest).trans
    (dependentSumPiEquivProd
      (fun s : Vertex C ⊕ NodeChildVertex rest =>
        ParentOpenFieldAt n a (C :: rest)
          ((nodeChildVertexConsEquiv C rest).symm s)))

end Imbalance
end TreeGraph
