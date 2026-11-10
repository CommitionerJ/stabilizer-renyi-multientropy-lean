import TreeGraph.Imbalance.NodeRootCopenBridge

namespace TreeGraph
namespace Imbalance

abbrev VertexCoordDomainClean (n : Nat) [NeZero n] (T : RTree) :=
  (v : Vertex T) → Fin (Vertex.weight v) → Rep n

def castVertexOfEq {T U : RTree} (h : T = U) : Vertex T ≃ Vertex U := by
  subst h
  exact Equiv.refl _

theorem castVertexOfEq_weight {T U : RTree} (h : T = U) (v : Vertex T) :
    Vertex.weight ((castVertexOfEq h) v) = Vertex.weight v := by
  subst h
  rfl

noncomputable def vertexCoordDomainNodeEquivBlockNonRoot
    (n a : Nat) [NeZero n] (cs : List RTree) :
    VertexCoordDomainClean n (RTree.node a cs) ≃
      Block n a × RootFieldDomainClean n (RTree.node a cs) where
  toFun f :=
    (fun j => f (Vertex.root (RTree.node a cs)) j,
      fun v j => f v.1 j)
  invFun P := fun v j =>
    if h : v.1 = [] then
      have hv : v = Vertex.root (RTree.node a cs) := by
        apply Subtype.ext
        exact h
      by
        subst hv
        exact P.1 j
    else
      P.2 ⟨v, h⟩ j
  left_inv f := by
    funext v j
    by_cases h : v.1 = []
    · have hv : v = Vertex.root (RTree.node a cs) := by
        apply Subtype.ext
        exact h
      subst hv
      simp
    · simp [h]
  right_inv P := by
    cases P with
    | mk root nonroot =>
        apply Prod.ext
        · funext j
          simp [Vertex.root]
        · funext v j
          simp [v.2]

noncomputable def nodeChildVertexConsEquiv
    (C : RTree) (rest : List RTree) :
    NodeChildVertex (C :: rest) ≃ Vertex C ⊕ NodeChildVertex rest where
  toFun p :=
    Fin.cases
      (motive := fun i : ChildIdx (C :: rest) =>
        Vertex (childAt (C :: rest) i) →
          Vertex C ⊕ NodeChildVertex rest)
      (fun v => Sum.inl ((castVertexOfEq
        (childAt_cons_zero C rest)) v))
      (fun i v => Sum.inr ⟨i, (castVertexOfEq
        (childAt_cons_succ C rest i)) v⟩)
      p.1 p.2
  invFun
    | Sum.inl v =>
        ⟨0, (castVertexOfEq (childAt_cons_zero C rest).symm) v⟩
    | Sum.inr p =>
        ⟨p.1.succ,
          (castVertexOfEq (childAt_cons_succ C rest p.1).symm) p.2⟩
  left_inv p := by
    cases p with
    | mk i v =>
        cases i using Fin.cases with
        | zero =>
            apply Sigma.ext
            · rfl
            · exact HEq.rfl
        | succ i =>
            apply Sigma.ext
            · rfl
            · exact HEq.rfl
  right_inv s := by
    cases s with
    | inl v =>
        change Sum.inl v = Sum.inl v
        rfl
    | inr p =>
        cases p with
        | mk i v =>
            change Sum.inr (⟨i, v⟩ : NodeChildVertex rest) =
              Sum.inr (⟨i, v⟩ : NodeChildVertex rest)
            rfl

def nodeChildVertexSumWeight {C : RTree} {rest : List RTree}
    (s : Vertex C ⊕ NodeChildVertex rest) : Nat :=
  match s with
  | Sum.inl v => Vertex.weight v
  | Sum.inr p => Vertex.weight p.2

theorem nodeChildVertexConsEquiv_weight
    {C : RTree} {rest : List RTree}
    (p : NodeChildVertex (C :: rest)) :
    Vertex.weight p.2 =
      nodeChildVertexSumWeight ((nodeChildVertexConsEquiv C rest) p) := by
  cases p with
  | mk i v =>
      cases i using Fin.cases with
      | zero =>
          change Vertex.weight v =
            Vertex.weight ((castVertexOfEq (childAt_cons_zero C rest)) v)
          exact (castVertexOfEq_weight (childAt_cons_zero C rest) v).symm
      | succ i =>
          change Vertex.weight v =
            Vertex.weight ((castVertexOfEq (childAt_cons_succ C rest i)) v)
          exact (castVertexOfEq_weight
            (childAt_cons_succ C rest i) v).symm

def dependentSumPiEquivProd
    {α β : Type} (γ : α ⊕ β → Type) :
    ((s : α ⊕ β) → γ s) ≃
      ((a : α) → γ (Sum.inl a)) × ((b : β) → γ (Sum.inr b)) where
  toFun f := (fun a => f (Sum.inl a), fun b => f (Sum.inr b))
  invFun P
    | Sum.inl a => P.1 a
    | Sum.inr b => P.2 b
  left_inv f := by
    funext s
    cases s <;> rfl
  right_inv P := by
    cases P
    rfl

noncomputable def nodeChildVertexCoordsEquivSum
    (n : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    ((p : NodeChildVertex (C :: rest)) →
        Fin (Vertex.weight p.2) → Rep n) ≃
      ((s : Vertex C ⊕ NodeChildVertex rest) →
        Fin (nodeChildVertexSumWeight s) → Rep n) :=
  (Equiv.piCongrRight (fun p : NodeChildVertex (C :: rest) =>
    Equiv.arrowCongr
      (finCastEquivOfEqClean
        (nodeChildVertexConsEquiv_weight (C := C) (rest := rest) p))
      (Equiv.refl (Rep n)))).trans
    (Equiv.piCongrLeft
      (fun s : Vertex C ⊕ NodeChildVertex rest =>
        Fin (nodeChildVertexSumWeight s) → Rep n)
      (nodeChildVertexConsEquiv C rest))

mutual
  noncomputable def vertexCoordDomainEquivCplus
      (n : Nat) [NeZero n] :
      (T : RTree) → VertexCoordDomainClean n T ≃ Cplus n T
    | RTree.node a cs =>
        (vertexCoordDomainNodeEquivBlockNonRoot n a cs).trans
          (Equiv.prodCongr (Equiv.refl (Block n a))
            ((rootFieldDomainCleanEquivNodeChildVertex n a cs).trans
              (nodeChildVertexCoordsEquivCoordsList n cs)))

  noncomputable def nodeChildVertexCoordsEquivCoordsList
      (n : Nat) [NeZero n] :
      (cs : List RTree) →
        ((p : NodeChildVertex cs) →
          Fin (Vertex.weight p.2) → Rep n) ≃ CoordsList n cs
    | [] =>
        { toFun := fun _ => PUnit.unit
          invFun := fun _ p => False.elim (Fin.elim0 p.1)
          left_inv := by
            intro f
            funext p
            exact False.elim (Fin.elim0 p.1)
          right_inv := by
            intro u
            cases u
            rfl }
    | C :: rest =>
        (nodeChildVertexCoordsEquivSum n C rest).trans
          ((dependentSumPiEquivProd
            (fun s : Vertex C ⊕ NodeChildVertex rest =>
              Fin (nodeChildVertexSumWeight s) → Rep n)).trans
            (Equiv.prodCongr
              (vertexCoordDomainEquivCplus n C)
              (nodeChildVertexCoordsEquivCoordsList n rest)))
end

end Imbalance
end TreeGraph
