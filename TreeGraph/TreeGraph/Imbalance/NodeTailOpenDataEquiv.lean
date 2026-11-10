import TreeGraph.Imbalance.NodeOpenHeadTailReindex

namespace TreeGraph
namespace Imbalance

abbrev TailOpenByCplus
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) : Type :=
  (p : Cplus n C) → OpenNormalAssignmentClean n (RTree.node a rest)

noncomputable abbrev tailParentTargetVertex
    (a : Nat) (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) :
    NonRootVertex (RTree.node a (C :: rest)) :=
  childVertexAtAsNonRootInNode (a := a)
    ((nodeChildVertexConsEquiv C rest).symm (Sum.inr q))

abbrev tailLocalTargetVertex
    (a : Nat) (rest : List RTree)
    (q : NodeChildVertex rest) :
    NonRootVertex (RTree.node a rest) :=
  childVertexAtAsNonRootInNode (a := a) q

theorem tailParent_head_other_ne_target
    (a : Nat) (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) (v : Vertex C) :
    (childVertexAtAsNonRootInNode (a := a)
        ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))).1.1 ≠
      (tailParentTargetVertex a C rest q).1.1 := by
  intro h
  cases q with
  | mk i w =>
      simp [tailParentTargetVertex, nodeChildVertexConsEquiv] at h

theorem tailParent_tail_other_ne_target
    (a : Nat) (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest)
    (u : OtherNonRootVertexClean (RTree.node a rest)
      (tailLocalTargetVertex a rest q)) :
    (childVertexAtAsNonRootInNode (a := a)
        ((nodeChildVertexConsEquiv C rest).symm
          (Sum.inr ((nonRootVertexNodeEquivChildVertex a rest) u.1)))).1.1 ≠
      (tailParentTargetVertex a C rest q).1.1 := by
  let p := (nonRootVertexNodeEquivChildVertex a rest) u.1
  change (childVertexAtAsNonRootInNode (a := a)
        ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).1.1 ≠
      (tailParentTargetVertex a C rest q).1.1
  intro h
  apply u.2
  have hu : childVertexAtAsNonRootInNode (a := a) p = u.1 := by
    dsimp [p]
    exact (nonRootVertexNodeEquivChildVertex a rest).left_inv u.1
  rw [← hu]
  simpa [tailParentTargetVertex, tailLocalTargetVertex,
    nodeChildVertexConsEquiv] using h

abbrev TailParentChildSubtype
    (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) : Type :=
  { p : NodeChildVertex (C :: rest) //
    p ≠ (nodeChildVertexConsEquiv C rest).symm (Sum.inr q) }

abbrev TailSumSubtype
    (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) : Type :=
  { s : Vertex C ⊕ NodeChildVertex rest // s ≠ Sum.inr q }

abbrev TailLocalChildSubtype
    (rest : List RTree) (q : NodeChildVertex rest) : Type :=
  { p : NodeChildVertex rest // p ≠ q }

noncomputable def tailParentOtherVertexEquivChildSubtype
    (a : Nat) (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) :
    OtherNonRootVertexClean (RTree.node a (C :: rest))
        (tailParentTargetVertex a C rest q) ≃
      TailParentChildSubtype C rest q where
  toFun u :=
    ⟨(nonRootVertexNodeEquivChildVertex a (C :: rest)) u.1, by
      intro hp
      apply u.2
      have hchild :
          childVertexAtAsNonRootInNode (a := a)
              ((nonRootVertexNodeEquivChildVertex a (C :: rest)) u.1) =
            u.1 :=
        (nonRootVertexNodeEquivChildVertex a (C :: rest)).left_inv u.1
      rw [← hchild, hp]
      ⟩
  invFun p :=
    ⟨childVertexAtAsNonRootInNode (a := a) p.1, by
      intro haddr
      apply p.2
      apply childVertexAtAsNonRootInNode_injective (a := a) (cs := C :: rest)
      apply Subtype.ext
      apply Subtype.ext
      exact haddr⟩
  left_inv u := by
    apply Subtype.ext
    exact (nonRootVertexNodeEquivChildVertex a (C :: rest)).left_inv u.1
  right_inv p := by
    apply Subtype.ext
    simp

noncomputable def tailParentChildSubtypeEquivSumSubtype
    (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) :
    TailParentChildSubtype C rest q ≃ TailSumSubtype C rest q where
  toFun p :=
    ⟨(nodeChildVertexConsEquiv C rest) p.1, by
      intro hs
      apply p.2
      exact
        (Equiv.apply_eq_iff_eq_symm_apply
          (nodeChildVertexConsEquiv C rest)).mp hs⟩
  invFun s :=
    ⟨(nodeChildVertexConsEquiv C rest).symm s.1, by
      intro hp
      apply s.2
      have h := congrArg (nodeChildVertexConsEquiv C rest) hp
      simpa using h⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv s := by
    apply Subtype.ext
    simp

noncomputable def tailSumSubtypeEquiv
    (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) :
    TailSumSubtype C rest q ≃ Vertex C ⊕ TailLocalChildSubtype rest q where
  toFun
    | ⟨Sum.inl v, _⟩ => Sum.inl v
    | ⟨Sum.inr p, hs⟩ =>
        Sum.inr ⟨p, by
          intro hp
          apply hs
          simp [hp]⟩
  invFun
    | Sum.inl v =>
        ⟨Sum.inl v, by
          intro h
          cases h⟩
    | Sum.inr p =>
        ⟨Sum.inr p.1, by
          intro h
          apply p.2
          exact Sum.inr.inj h⟩
  left_inv s := by
    cases s with
    | mk s hs =>
        cases s with
        | inl v => rfl
        | inr p => rfl
  right_inv s := by
    cases s with
    | inl v => rfl
    | inr p =>
        dsimp

noncomputable def tailLocalChildSubtypeEquivOtherVertex
    (a : Nat) (rest : List RTree)
    (q : NodeChildVertex rest) :
    TailLocalChildSubtype rest q ≃
      OtherNonRootVertexClean (RTree.node a rest)
        (tailLocalTargetVertex a rest q) where
  toFun p :=
    ⟨childVertexAtAsNonRootInNode (a := a) p.1, by
      intro haddr
      apply p.2
      apply childVertexAtAsNonRootInNode_injective (a := a) (cs := rest)
      apply Subtype.ext
      apply Subtype.ext
      exact haddr⟩
  invFun u :=
    ⟨(nonRootVertexNodeEquivChildVertex a rest) u.1, by
      intro hp
      apply u.2
      have hchild :
          childVertexAtAsNonRootInNode (a := a)
              ((nonRootVertexNodeEquivChildVertex a rest) u.1) =
            u.1 :=
        (nonRootVertexNodeEquivChildVertex a rest).left_inv u.1
      rw [← hchild, hp]
      ⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv u := by
    apply Subtype.ext
    exact (nonRootVertexNodeEquivChildVertex a rest).left_inv u.1

noncomputable def tailParentOtherVertexEquiv
    (a : Nat) (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) :
    OtherNonRootVertexClean (RTree.node a (C :: rest))
        (tailParentTargetVertex a C rest q) ≃
      Vertex C ⊕
        OtherNonRootVertexClean (RTree.node a rest)
          (tailLocalTargetVertex a rest q) where
  toFun :=
    (tailParentOtherVertexEquivChildSubtype a C rest q).trans
      ((tailParentChildSubtypeEquivSumSubtype C rest q).trans
        ((tailSumSubtypeEquiv C rest q).trans
          (Equiv.sumCongr (Equiv.refl (Vertex C))
            (tailLocalChildSubtypeEquivOtherVertex a rest q))))
  invFun :=
    ((tailParentOtherVertexEquivChildSubtype a C rest q).trans
      ((tailParentChildSubtypeEquivSumSubtype C rest q).trans
        ((tailSumSubtypeEquiv C rest q).trans
          (Equiv.sumCongr (Equiv.refl (Vertex C))
            (tailLocalChildSubtypeEquivOtherVertex a rest q))))).symm
  left_inv u := by
    exact
      ((tailParentOtherVertexEquivChildSubtype a C rest q).trans
        ((tailParentChildSubtypeEquivSumSubtype C rest q).trans
          ((tailSumSubtypeEquiv C rest q).trans
            (Equiv.sumCongr (Equiv.refl (Vertex C))
              (tailLocalChildSubtypeEquivOtherVertex a rest q))))).left_inv u
  right_inv s := by
    exact
      ((tailParentOtherVertexEquivChildSubtype a C rest q).trans
        ((tailParentChildSubtypeEquivSumSubtype C rest q).trans
          ((tailSumSubtypeEquiv C rest q).trans
            (Equiv.sumCongr (Equiv.refl (Vertex C))
              (tailLocalChildSubtypeEquivOtherVertex a rest q))))).right_inv s

theorem tailParentOtherVertexEquiv_weight
    (a : Nat) (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest)
    (u :
      OtherNonRootVertexClean (RTree.node a (C :: rest))
        (tailParentTargetVertex a C rest q)) :
    NonRootVertex.weight u.1 =
      match tailParentOtherVertexEquiv a C rest q u with
      | Sum.inl v => Vertex.weight v
      | Sum.inr uTail => NonRootVertex.weight uTail.1 := by
  let p := (nonRootVertexNodeEquivChildVertex a (C :: rest)) u.1
  have hweight :
      NonRootVertex.weight u.1 = Vertex.weight p.2 :=
    nonRootVertexNodeEquivChildVertex_weight (a := a) (cs := C :: rest) u.1
  cases hs : (nodeChildVertexConsEquiv C rest) p with
  | inl v =>
      have hp :
          p = (nodeChildVertexConsEquiv C rest).symm (Sum.inl v) := by
        exact
          (Equiv.apply_eq_iff_eq_symm_apply
            (nodeChildVertexConsEquiv C rest)).mp hs
      rw [hweight, hp]
      have h := nodeChildVertexConsEquiv_weight
        ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))
      simpa [tailParentOtherVertexEquiv,
        tailParentOtherVertexEquivChildSubtype,
        tailParentChildSubtypeEquivSumSubtype,
        tailSumSubtypeEquiv,
        tailLocalChildSubtypeEquivOtherVertex,
        p, hs] using h
  | inr r =>
      have hp :
          p = (nodeChildVertexConsEquiv C rest).symm (Sum.inr r) := by
        exact
          (Equiv.apply_eq_iff_eq_symm_apply
            (nodeChildVertexConsEquiv C rest)).mp hs
      rw [hweight, hp]
      have h := nodeChildVertexConsEquiv_weight
        ((nodeChildVertexConsEquiv C rest).symm (Sum.inr r))
      simpa [tailParentOtherVertexEquiv,
        tailParentOtherVertexEquivChildSubtype,
        tailParentChildSubtypeEquivSumSubtype,
        tailSumSubtypeEquiv,
        tailLocalChildSubtypeEquivOtherVertex,
        p, hs, childVertexAtAsNonRootInNode_weight] using h

abbrev TailParentOtherCoord
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) : Type :=
  (u :
    OtherNonRootVertexClean (RTree.node a (C :: rest))
      (tailParentTargetVertex a C rest q)) →
    Fin (NonRootVertex.weight u.1) → Rep n

abbrev TailLocalOtherCoord
    (n a : Nat) [NeZero n] (rest : List RTree)
    (q : NodeChildVertex rest) : Type :=
  (u :
    OtherNonRootVertexClean (RTree.node a rest)
      (tailLocalTargetVertex a rest q)) →
    Fin (NonRootVertex.weight u.1) → Rep n

noncomputable def tailParentOtherCoordEquiv
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) :
    TailParentOtherCoord n a C rest q ≃
      VertexCoordDomainClean n C × TailLocalOtherCoord n a rest q :=
  (Equiv.piCongrRight
      (fun u :
        OtherNonRootVertexClean (RTree.node a (C :: rest))
          (tailParentTargetVertex a C rest q) =>
        Equiv.arrowCongr
          (finCastEquivOfEqClean
            (tailParentOtherVertexEquiv_weight a C rest q u))
          (Equiv.refl (Rep n)))).trans
    ((Equiv.piCongrLeft
        (fun s : Vertex C ⊕
            OtherNonRootVertexClean (RTree.node a rest)
              (tailLocalTargetVertex a rest q) =>
          Fin
              (match s with
              | Sum.inl v => Vertex.weight v
              | Sum.inr u => NonRootVertex.weight u.1) →
            Rep n)
        (tailParentOtherVertexEquiv a C rest q)).trans
      (dependentSumPiEquivProd
        (fun s : Vertex C ⊕
            OtherNonRootVertexClean (RTree.node a rest)
              (tailLocalTargetVertex a rest q) =>
          Fin
              (match s with
              | Sum.inl v => Vertex.weight v
              | Sum.inr u => NonRootVertex.weight u.1) →
            Rep n)))

noncomputable def tailParentFieldDomainRawEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) :
    NonRootFieldDomainClean n (RTree.node a (C :: rest))
        (tailParentTargetVertex a C rest q) ≃
      Block n (a - 1) × Rep n ×
        (VertexCoordDomainClean n C × TailLocalOtherCoord n a rest q) where
  toFun dom :=
    (dom.rootCoord, dom.diagonal,
      tailParentOtherCoordEquiv n a C rest q dom.otherCoord)
  invFun P :=
    { rootCoord := P.1
      diagonal := P.2.1
      otherCoord :=
        (tailParentOtherCoordEquiv n a C rest q).symm P.2.2 }
  left_inv dom := by
    cases dom
    simp [tailParentOtherCoordEquiv]
  right_inv P := by
    rcases P with ⟨rootCoord, diagonal, other⟩
    simp [tailParentOtherCoordEquiv]

noncomputable def tailParentFieldDomainEquivCplusLocal
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) :
    NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (childVertexAtAsNonRootInNode (a := a)
        ((nodeChildVertexConsEquiv C rest).symm (Sum.inr q))) ≃
    Cplus n C ×
      NonRootFieldDomainClean n (RTree.node a rest)
        (childVertexAtAsNonRootInNode (a := a) q) where
  toFun dom :=
    let P := tailParentFieldDomainRawEquiv n a C rest q dom
    ((vertexCoordDomainEquivCplus n C) P.2.2.1,
      { rootCoord := P.1
        diagonal := P.2.1
        otherCoord := P.2.2.2 })
  invFun P :=
    (tailParentFieldDomainRawEquiv n a C rest q).symm
      (P.2.rootCoord, P.2.diagonal,
        ((vertexCoordDomainEquivCplus n C).symm P.1, P.2.otherCoord))
  left_inv dom := by
    let R := tailParentFieldDomainRawEquiv n a C rest q dom
    change
      (tailParentFieldDomainRawEquiv n a C rest q).symm
        (R.1, R.2.1,
          ((vertexCoordDomainEquivCplus n C).symm
            ((vertexCoordDomainEquivCplus n C) R.2.2.1),
            R.2.2.2)) = dom
    have hx :
        (vertexCoordDomainEquivCplus n C).symm
            ((vertexCoordDomainEquivCplus n C) R.2.2.1) =
          R.2.2.1 :=
      (vertexCoordDomainEquivCplus n C).left_inv R.2.2.1
    rw [hx]
    exact (tailParentFieldDomainRawEquiv n a C rest q).left_inv dom
  right_inv P := by
    rcases P with ⟨p, localDom⟩
    cases localDom
    simp

theorem tailParentFieldDomainEquivCplusLocal_fst
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest)
    (dom :
      NonRootFieldDomainClean n (RTree.node a (C :: rest))
        (childVertexAtAsNonRootInNode (a := a)
          ((nodeChildVertexConsEquiv C rest).symm (Sum.inr q)))) :
    (tailParentFieldDomainEquivCplusLocal n a C rest q dom).1 =
      (vertexCoordDomainEquivCplus n C)
        ((tailParentFieldDomainRawEquiv n a C rest q dom).2.2.1) := by
  rfl

theorem tailParentFieldDomainEquivCplusLocal_snd
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest)
    (dom :
      NonRootFieldDomainClean n (RTree.node a (C :: rest))
        (childVertexAtAsNonRootInNode (a := a)
          ((nodeChildVertexConsEquiv C rest).symm (Sum.inr q)))) :
    (tailParentFieldDomainEquivCplusLocal n a C rest q dom).2 =
      { rootCoord := (tailParentFieldDomainRawEquiv n a C rest q dom).1
        diagonal := (tailParentFieldDomainRawEquiv n a C rest q dom).2.1
        otherCoord := (tailParentFieldDomainRawEquiv n a C rest q dom).2.2.2 } := by
  rfl

theorem tailParentFieldDomainEquivCplusLocal_symm_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest)
    (p : Cplus n C)
    (localDom :
      NonRootFieldDomainClean n (RTree.node a rest)
        (childVertexAtAsNonRootInNode (a := a) q)) :
    (tailParentFieldDomainEquivCplusLocal n a C rest q).symm (p, localDom) =
      (tailParentFieldDomainRawEquiv n a C rest q).symm
        (localDom.rootCoord, localDom.diagonal,
          ((vertexCoordDomainEquivCplus n C).symm p, localDom.otherCoord)) := by
  rfl

noncomputable def parentOpenTailFieldsToTailOpenByCplus
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    ParentOpenTailFields n a C rest → TailOpenByCplus n a C rest :=
  fun tail p =>
    (openNormalAssignmentCleanEquivParentOpenByChild n a rest).symm
      (fun q localDom =>
        tail q
          ((tailParentFieldDomainEquivCplusLocal n a C rest q).symm
            (p, localDom)))

noncomputable def tailOpenByCplusToParentTailFields
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    TailOpenByCplus n a C rest → ParentOpenTailFields n a C rest :=
  fun data q parentDom =>
    let P := tailParentFieldDomainEquivCplusLocal n a C rest q parentDom
    ((openNormalAssignmentCleanEquivParentOpenByChild n a rest)
      (data P.1)) q P.2

noncomputable def parentOpenTailFieldsEquivTailOpenByCplus
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    ParentOpenTailFields n a C rest ≃ TailOpenByCplus n a C rest where
  toFun := parentOpenTailFieldsToTailOpenByCplus n a C rest
  invFun := tailOpenByCplusToParentTailFields n a C rest
  left_inv tail := by
    funext q parentDom
    unfold parentOpenTailFieldsToTailOpenByCplus
      tailOpenByCplusToParentTailFields
    simp
  right_inv data := by
    funext p
    apply (openNormalAssignmentCleanEquivParentOpenByChild n a rest).injective
    funext q localDom
    unfold parentOpenTailFieldsToTailOpenByCplus
      tailOpenByCplusToParentTailFields
    simp

theorem parentOpenTailFieldsEquivTailOpenByCplus_apply
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (q : NodeChildVertex rest)
    (localDom :
      NonRootFieldDomainClean n (RTree.node a rest)
        (childVertexAtAsNonRootInNode (a := a) q)) :
    ((openNormalAssignmentCleanEquivParentOpenByChild n a rest)
      ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
        q localDom =
      tail q
        ((tailParentFieldDomainEquivCplusLocal n a C rest q).symm
          (p, localDom)) := by
  simp [parentOpenTailFieldsEquivTailOpenByCplus,
    parentOpenTailFieldsToTailOpenByCplus]

theorem parentOpenTailFieldsEquivTailOpenByCplus_symm_apply
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (data : TailOpenByCplus n a C rest)
    (q : NodeChildVertex rest)
    (parentDom :
      NonRootFieldDomainClean n (RTree.node a (C :: rest))
        (childVertexAtAsNonRootInNode (a := a)
          ((nodeChildVertexConsEquiv C rest).symm (Sum.inr q)))) :
    ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest).symm data)
        q parentDom =
      let P := tailParentFieldDomainEquivCplusLocal n a C rest q parentDom
      ((openNormalAssignmentCleanEquivParentOpenByChild n a rest)
        (data P.1)) q P.2 := by
  rfl

end Imbalance
end TreeGraph
