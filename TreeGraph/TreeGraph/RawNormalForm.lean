import TreeGraph.Addresses
import TreeGraph.MainTheorem

namespace TreeGraph

namespace RawNormal

abbrev RootFieldDomain (n : Nat) [NeZero n] (T : RTree) :=
  (v : NonRootVertex T) → Fin (NonRootVertex.weight v) → ZMod n

structure NormalSite (n : Nat) [NeZero n] (T : RTree) where
  rootCoord : Fin (T.rootWeight - 1) → ZMod n
  nonRootCoord : RootFieldDomain n T
  deriving DecidableEq, Fintype

abbrev OtherNonRootVertex (T : RTree) (v : NonRootVertex T) :=
  { u : NonRootVertex T // u.1.1 ≠ v.1.1 }

structure NonRootFieldDomain (n : Nat) [NeZero n] (T : RTree)
    (v : NonRootVertex T) where
  rootCoord : Fin (T.rootWeight - 1) → ZMod n
  diagonal : ZMod n
  otherCoord :
    (u : OtherNonRootVertex T v) → Fin (NonRootVertex.weight u.1) → ZMod n
  deriving DecidableEq, Fintype

structure NormalAssignment (n : Nat) [NeZero n] (T : RTree) where
  rootField : RootFieldDomain n T → F2
  nodeField :
    (v : NonRootVertex T) → NonRootFieldDomain n T v → F2
  deriving Fintype

abbrev RootFieldAssignment (n : Nat) [NeZero n] (T : RTree) :=
  RootFieldDomain n T → F2

abbrev NodeFieldAssignment (n : Nat) [NeZero n] (T : RTree) :=
  (v : NonRootVertex T) → NonRootFieldDomain n T v → F2

noncomputable def normalAssignmentEquivRootNodeFields
    (n : Nat) [NeZero n] (T : RTree) :
    NormalAssignment n T ≃
      RootFieldAssignment n T × NodeFieldAssignment n T where
  toFun A := (A.rootField, A.nodeField)
  invFun P := { rootField := P.1, nodeField := P.2 }
  left_inv A := by
    cases A
    rfl
  right_inv P := by
    cases P
    rfl

theorem sum_normalAssignment_eq_sum_root_nodeFields
    {n : Nat} [NeZero n] (T : RTree)
    (F : NormalAssignment n T → ℤ) :
    (∑ A : NormalAssignment n T, F A) =
      ∑ P : RootFieldAssignment n T × NodeFieldAssignment n T,
        F ((normalAssignmentEquivRootNodeFields n T).symm P) := by
  classical
  exact (Equiv.sum_comp
    (normalAssignmentEquivRootNodeFields n T).symm F).symm

abbrev NodeRootFieldAssignment
    (n a : Nat) [NeZero n] (cs : List RTree) :=
  RootFieldAssignment n (RTree.node a cs)

abbrev NodeNonRootFieldAssignment
    (n a : Nat) [NeZero n] (cs : List RTree) :=
  NodeFieldAssignment n (RTree.node a cs)

theorem sum_normalAssignment_node_eq_sum_root_nodeFields
    {n a : Nat} [NeZero n] (cs : List RTree)
    (F : NormalAssignment n (RTree.node a cs) → ℤ) :
    (∑ A : NormalAssignment n (RTree.node a cs), F A) =
      ∑ P : NodeRootFieldAssignment n a cs ×
          NodeNonRootFieldAssignment n a cs,
        F ((normalAssignmentEquivRootNodeFields n (RTree.node a cs)).symm P) :=
  sum_normalAssignment_eq_sum_root_nodeFields (RTree.node a cs) F

def childVertexInNode {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) (v : Vertex C) :
    Vertex (RTree.node a cs) :=
  ⟨idx :: v.1,
    RTree.childAddress_mem_addresses_node_of_get?
      (a := a) hget v.2⟩

def childVertexAtInNode {a : Nat} {cs : List RTree}
    (i : ChildIdx cs) (v : Vertex (childAt cs i)) :
    Vertex (RTree.node a cs) :=
  childVertexInNode (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i) v

def childRootAsNonRootInNode {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) :
    NonRootVertex (RTree.node a cs) :=
  ⟨childVertexInNode (a := a) hget (Vertex.root C), by simp [childVertexInNode]⟩

def childRootAtAsNonRootInNode {a : Nat} {cs : List RTree}
    (i : ChildIdx cs) :
    NonRootVertex (RTree.node a cs) :=
  childRootAsNonRootInNode (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i)

def childNonRootVertexInNode {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) (v : NonRootVertex C) :
    NonRootVertex (RTree.node a cs) :=
  ⟨childVertexInNode (a := a) hget v.1, by simp [childVertexInNode]⟩

def childNonRootVertexAtInNode {a : Nat} {cs : List RTree}
    (i : ChildIdx cs) (v : NonRootVertex (childAt cs i)) :
    NonRootVertex (RTree.node a cs) :=
  childNonRootVertexInNode (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i) v

@[simp] theorem childVertexInNode_addr
    {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) (v : Vertex C) :
    (childVertexInNode (a := a) hget v).1 = idx :: v.1 := rfl

@[simp] theorem childVertexAtInNode_addr
    {a : Nat} {cs : List RTree}
    (i : ChildIdx cs) (v : Vertex (childAt cs i)) :
    (childVertexAtInNode (a := a) i v).1 = i.1 :: v.1 := rfl

@[simp] theorem childRootAsNonRootInNode_addr
    {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) :
    (childRootAsNonRootInNode (a := a) hget).1.1 = [idx] := rfl

@[simp] theorem childRootAtAsNonRootInNode_addr
    {a : Nat} {cs : List RTree} (i : ChildIdx cs) :
    (childRootAtAsNonRootInNode (a := a) i).1.1 = [i.1] := rfl

@[simp] theorem childNonRootVertexInNode_addr
    {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) (v : NonRootVertex C) :
    (childNonRootVertexInNode (a := a) hget v).1.1 = idx :: v.1.1 := rfl

@[simp] theorem childNonRootVertexAtInNode_addr
    {a : Nat} {cs : List RTree}
    (i : ChildIdx cs) (v : NonRootVertex (childAt cs i)) :
    (childNonRootVertexAtInNode (a := a) i v).1.1 =
      i.1 :: v.1.1 := rfl

theorem childVertexInNode_weight
    {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) (v : Vertex C) :
    Vertex.weight (childVertexInNode (a := a) hget v) =
      Vertex.weight v := by
  simp [Vertex.weight, childVertexInNode,
    RTree.weightAt_childAddress_of_get? (a := a) hget]

theorem childVertexAtInNode_weight
    {a : Nat} {cs : List RTree}
    (i : ChildIdx cs) (v : Vertex (childAt cs i)) :
    Vertex.weight (childVertexAtInNode (a := a) i v) =
      Vertex.weight v :=
  childVertexInNode_weight (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i) v

theorem childNonRootVertexInNode_weight
    {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) (v : NonRootVertex C) :
    NonRootVertex.weight (childNonRootVertexInNode (a := a) hget v) =
      NonRootVertex.weight v := by
  simp [NonRootVertex.weight, childNonRootVertexInNode,
    childVertexInNode_weight (a := a) hget v.1]

theorem childNonRootVertexAtInNode_weight
    {a : Nat} {cs : List RTree}
    (i : ChildIdx cs) (v : NonRootVertex (childAt cs i)) :
    NonRootVertex.weight (childNonRootVertexAtInNode (a := a) i v) =
      NonRootVertex.weight v :=
  childNonRootVertexInNode_weight (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i) v

theorem childRootAsNonRootInNode_weight
    {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) :
    NonRootVertex.weight (childRootAsNonRootInNode (a := a) hget) =
      C.rootWeight := by
  change Vertex.weight (childVertexInNode (a := a) hget (Vertex.root C)) =
    C.rootWeight
  rw [childVertexInNode_weight]
  simp [Vertex.weight, Vertex.root]

theorem childRootAtAsNonRootInNode_weight
    {a : Nat} {cs : List RTree} (i : ChildIdx cs) :
    NonRootVertex.weight (childRootAtAsNonRootInNode (a := a) i) =
      (childAt cs i).rootWeight :=
  childRootAsNonRootInNode_weight (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i)

theorem nonRootVertex_node_exists_childVertex
    {a : Nat} {cs : List RTree}
    (v : NonRootVertex (RTree.node a cs)) :
    ∃ i : ChildIdx cs, ∃ w : Vertex (childAt cs i),
      v.1 = childVertexAtInNode (a := a) i w := by
  rcases RTree.nonroot_address_mem_node_exists_childAt
      (a := a) (cs := cs) (p := v.1.1) v.1.2 v.2 with
    ⟨i, q, hp_eq, hq⟩
  refine ⟨i, ⟨q, hq⟩, ?_⟩
  apply Subtype.ext
  simpa [childVertexAtInNode, childVertexInNode] using hp_eq

theorem nonRootVertex_node_exists_childRoot_or_childNonRoot
    {a : Nat} {cs : List RTree}
    (v : NonRootVertex (RTree.node a cs)) :
    ∃ i : ChildIdx cs,
      v = childRootAtAsNonRootInNode (a := a) i ∨
        ∃ w : NonRootVertex (childAt cs i),
          v = childNonRootVertexAtInNode (a := a) i w := by
  rcases nonRootVertex_node_exists_childVertex (a := a) (cs := cs) v with
    ⟨i, w, hv⟩
  by_cases hroot : w.1 = []
  · refine ⟨i, Or.inl ?_⟩
    apply Subtype.ext
    calc
      v.1 = childVertexAtInNode (a := a) i w := hv
      _ = childVertexAtInNode (a := a) i (Vertex.root (childAt cs i)) := by
        apply congrArg
        apply Subtype.ext
        exact hroot
      _ = (childRootAtAsNonRootInNode (a := a) i).1 := rfl
  · refine ⟨i, Or.inr ?_⟩
    refine ⟨⟨w, hroot⟩, ?_⟩
    apply Subtype.ext
    calc
      v.1 = childVertexAtInNode (a := a) i w := hv
      _ = (childNonRootVertexAtInNode (a := a) i ⟨w, hroot⟩).1 := rfl

abbrev NodeChildVertex (cs : List RTree) :=
  Sigma fun i : ChildIdx cs => Vertex (childAt cs i)

theorem nonRootVertex_node_exists_nodeChildVertex
    {a : Nat} {cs : List RTree}
    (v : NonRootVertex (RTree.node a cs)) :
    ∃ p : NodeChildVertex cs,
      v.1 = childVertexAtInNode (a := a) p.1 p.2 := by
  rcases nonRootVertex_node_exists_childVertex (a := a) (cs := cs) v with
    ⟨i, w, hv⟩
  exact ⟨⟨i, w⟩, hv⟩

def childVertexAtAsNonRootInNode
    {a : Nat} {cs : List RTree}
    (p : NodeChildVertex cs) :
    NonRootVertex (RTree.node a cs) :=
  ⟨childVertexAtInNode (a := a) p.1 p.2, by
    simp [childVertexAtInNode, childVertexInNode]⟩

@[simp] theorem childVertexAtAsNonRootInNode_addr
    {a : Nat} {cs : List RTree}
    (p : NodeChildVertex cs) :
    (childVertexAtAsNonRootInNode (a := a) p).1.1 =
      p.1.1 :: p.2.1 := rfl

theorem childVertexAtAsNonRootInNode_injective
    {a : Nat} {cs : List RTree} :
    Function.Injective
      (childVertexAtAsNonRootInNode (a := a) (cs := cs)) := by
  intro p q hpq
  cases p with
  | mk i u =>
      cases q with
      | mk j v =>
          have haddr :
              i.1 :: u.1 = j.1 :: v.1 := by
            exact congrArg (fun x : NonRootVertex (RTree.node a cs) =>
              x.1.1) hpq
          have hhead : i.1 = j.1 := by
            exact List.cons.inj haddr |>.1
          have htail : u.1 = v.1 := by
            exact List.cons.inj haddr |>.2
          have hij : i = j := by
            exact Fin.ext hhead
          subst hij
          have huv : u = v := by
            apply Subtype.ext
            exact htail
          subst huv
          rfl

noncomputable def nonRootVertexNodeEquivChildVertex
    (a : Nat) (cs : List RTree) :
    NonRootVertex (RTree.node a cs) ≃ NodeChildVertex cs where
  toFun v :=
    Classical.choose (nonRootVertex_node_exists_nodeChildVertex
      (a := a) (cs := cs) v)
  invFun p := childVertexAtAsNonRootInNode (a := a) p
  left_inv v := by
    let p := Classical.choose (nonRootVertex_node_exists_nodeChildVertex
      (a := a) (cs := cs) v)
    have hp :
        v.1 = childVertexAtInNode (a := a) p.1 p.2 :=
      Classical.choose_spec (nonRootVertex_node_exists_nodeChildVertex
        (a := a) (cs := cs) v)
    apply Subtype.ext
    exact hp.symm
  right_inv p := by
    let q := Classical.choose (nonRootVertex_node_exists_nodeChildVertex
      (a := a) (cs := cs)
        (childVertexAtAsNonRootInNode (a := a) p))
    have hq :
        (childVertexAtAsNonRootInNode (a := a) p).1 =
          childVertexAtInNode (a := a) q.1 q.2 :=
      Classical.choose_spec (nonRootVertex_node_exists_nodeChildVertex
        (a := a) (cs := cs)
          (childVertexAtAsNonRootInNode (a := a) p))
    apply childVertexAtAsNonRootInNode_injective (a := a) (cs := cs)
    apply Subtype.ext
    exact hq.symm

abbrev NodeChildVertexFieldAssignment
    (n a : Nat) [NeZero n] (cs : List RTree) :=
  (p : NodeChildVertex cs) →
    NonRootFieldDomain n (RTree.node a cs)
      ((nonRootVertexNodeEquivChildVertex a cs).symm p) → F2

noncomputable def nodeChildVertexFieldAssignmentEquivNodeField
    (n a : Nat) [NeZero n] (cs : List RTree) :
    NodeChildVertexFieldAssignment n a cs ≃
      NodeNonRootFieldAssignment n a cs :=
  Equiv.piCongrLeft
    (fun v : NonRootVertex (RTree.node a cs) =>
      NonRootFieldDomain n (RTree.node a cs) v → F2)
    (nonRootVertexNodeEquivChildVertex a cs).symm

theorem sum_nodeFieldAssignment_eq_sum_childVertexFields
    {n a : Nat} [NeZero n] (cs : List RTree)
    (F : NodeNonRootFieldAssignment n a cs → ℤ) :
    (∑ N : NodeNonRootFieldAssignment n a cs, F N) =
      ∑ G : NodeChildVertexFieldAssignment n a cs,
        F ((nodeChildVertexFieldAssignmentEquivNodeField n a cs) G) := by
  classical
  exact (Equiv.sum_comp
    (nodeChildVertexFieldAssignmentEquivNodeField n a cs) F).symm

abbrev VertexRootOrNonRoot (T : RTree) :=
  Unit ⊕ NonRootVertex T

def vertexEquivRootOrNonRoot (T : RTree) :
    Vertex T ≃ VertexRootOrNonRoot T where
  toFun v :=
    if h : v.1 = [] then Sum.inl ()
    else Sum.inr ⟨v, h⟩
  invFun
    | Sum.inl _ => Vertex.root T
    | Sum.inr v => v.1
  left_inv v := by
    by_cases h : v.1 = []
    · apply Subtype.ext
      simp [h, Vertex.root]
    · simp [h]
  right_inv x := by
    cases x with
    | inl u =>
        cases u
        simp [Vertex.root]
    | inr v =>
        simp [v.2]

abbrev NodeChildVertexKind (cs : List RTree) :=
  Sigma fun i : ChildIdx cs => VertexRootOrNonRoot (childAt cs i)

def nodeChildVertexEquivKind (cs : List RTree) :
    NodeChildVertex cs ≃ NodeChildVertexKind cs :=
  Equiv.sigmaCongrRight (fun i => vertexEquivRootOrNonRoot (childAt cs i))

@[simp] theorem nodeChildVertexEquivKind_symm_root
    {cs : List RTree} (i : ChildIdx cs) :
    (nodeChildVertexEquivKind cs).symm ⟨i, Sum.inl ()⟩ =
      ⟨i, Vertex.root (childAt cs i)⟩ := by
  rw [nodeChildVertexEquivKind, Equiv.sigmaCongrRight_symm,
    Equiv.sigmaCongrRight_apply]
  simp [vertexEquivRootOrNonRoot]

@[simp] theorem nodeChildVertexEquivKind_symm_nonRoot
    {cs : List RTree} (i : ChildIdx cs)
    (v : NonRootVertex (childAt cs i)) :
    (nodeChildVertexEquivKind cs).symm ⟨i, Sum.inr v⟩ =
      ⟨i, v.1⟩ := by
  rw [nodeChildVertexEquivKind, Equiv.sigmaCongrRight_symm,
    Equiv.sigmaCongrRight_apply]
  simp [vertexEquivRootOrNonRoot]

@[simp] theorem nonRootVertexNodeEquivChildVertex_symm_kind_root
    {a : Nat} {cs : List RTree} (i : ChildIdx cs) :
    ((nonRootVertexNodeEquivChildVertex a cs).symm
      ((nodeChildVertexEquivKind cs).symm ⟨i, Sum.inl ()⟩)) =
    childRootAtAsNonRootInNode (a := a) i := by
  change childVertexAtAsNonRootInNode (a := a)
      ((nodeChildVertexEquivKind cs).symm ⟨i, Sum.inl ()⟩) =
    childRootAtAsNonRootInNode (a := a) i
  rw [nodeChildVertexEquivKind, Equiv.sigmaCongrRight_symm,
    Equiv.sigmaCongrRight_apply]
  simp [childVertexAtAsNonRootInNode, childRootAtAsNonRootInNode,
    childRootAsNonRootInNode, childVertexAtInNode, childVertexInNode,
    vertexEquivRootOrNonRoot, Vertex.root]

@[simp] theorem nonRootVertexNodeEquivChildVertex_symm_kind_nonRoot
    {a : Nat} {cs : List RTree} (i : ChildIdx cs)
    (v : NonRootVertex (childAt cs i)) :
    ((nonRootVertexNodeEquivChildVertex a cs).symm
      ((nodeChildVertexEquivKind cs).symm ⟨i, Sum.inr v⟩)) =
    childNonRootVertexAtInNode (a := a) i v := by
  change childVertexAtAsNonRootInNode (a := a)
      ((nodeChildVertexEquivKind cs).symm ⟨i, Sum.inr v⟩) =
    childNonRootVertexAtInNode (a := a) i v
  rw [nodeChildVertexEquivKind, Equiv.sigmaCongrRight_symm,
    Equiv.sigmaCongrRight_apply]
  simp [childVertexAtAsNonRootInNode, childNonRootVertexAtInNode,
    childNonRootVertexInNode, childVertexAtInNode, childVertexInNode,
    vertexEquivRootOrNonRoot]

abbrev NodeChildVertexKindFieldAssignment
    (n a : Nat) [NeZero n] (cs : List RTree) :=
  (k : NodeChildVertexKind cs) →
    NonRootFieldDomain n (RTree.node a cs)
      ((nonRootVertexNodeEquivChildVertex a cs).symm
        ((nodeChildVertexEquivKind cs).symm k)) → F2

noncomputable def nodeChildVertexKindFieldAssignmentEquivChildVertexFields
    (n a : Nat) [NeZero n] (cs : List RTree) :
    NodeChildVertexKindFieldAssignment n a cs ≃
      NodeChildVertexFieldAssignment n a cs :=
  Equiv.piCongrLeft
    (fun p : NodeChildVertex cs =>
      NonRootFieldDomain n (RTree.node a cs)
        ((nonRootVertexNodeEquivChildVertex a cs).symm p) → F2)
    (nodeChildVertexEquivKind cs).symm

theorem sum_childVertexFields_eq_sum_childVertexKindFields
    {n a : Nat} [NeZero n] (cs : List RTree)
    (F : NodeChildVertexFieldAssignment n a cs → ℤ) :
    (∑ G : NodeChildVertexFieldAssignment n a cs, F G) =
      ∑ K : NodeChildVertexKindFieldAssignment n a cs,
        F ((nodeChildVertexKindFieldAssignmentEquivChildVertexFields
          n a cs) K) := by
  classical
  exact (Equiv.sum_comp
    (nodeChildVertexKindFieldAssignmentEquivChildVertexFields
      n a cs) F).symm

abbrev NodeChildRootFieldAssignment
    (n a : Nat) [NeZero n] (cs : List RTree) :=
  (i : ChildIdx cs) →
    NonRootFieldDomain n (RTree.node a cs)
        ((nonRootVertexNodeEquivChildVertex a cs).symm
        ((nodeChildVertexEquivKind cs).symm
          ⟨i, Sum.inl ()⟩)) → F2

abbrev NodeChildNonRootFieldAssignment
    (n a : Nat) [NeZero n] (cs : List RTree) :=
  (i : ChildIdx cs) → (v : NonRootVertex (childAt cs i)) →
    NonRootFieldDomain n (RTree.node a cs)
      ((nonRootVertexNodeEquivChildVertex a cs).symm
        ((nodeChildVertexEquivKind cs).symm
          ⟨i, Sum.inr v⟩)) → F2

abbrev NodeChildRootFieldDomain
    (n a : Nat) [NeZero n] (cs : List RTree) (i : ChildIdx cs) :=
  NonRootFieldDomain n (RTree.node a cs)
    ((nonRootVertexNodeEquivChildVertex a cs).symm
      ((nodeChildVertexEquivKind cs).symm ⟨i, Sum.inl ()⟩))

abbrev NodeChildNonRootFieldDomain
    (n a : Nat) [NeZero n] (cs : List RTree)
    (i : ChildIdx cs) (v : NonRootVertex (childAt cs i)) :=
  NonRootFieldDomain n (RTree.node a cs)
    ((nonRootVertexNodeEquivChildVertex a cs).symm
      ((nodeChildVertexEquivKind cs).symm ⟨i, Sum.inr v⟩))

abbrev NodeChildDataAt
    (n a : Nat) [NeZero n] (cs : List RTree) (i : ChildIdx cs) :=
  (NodeChildRootFieldDomain n a cs i → F2) ×
    ((v : NonRootVertex (childAt cs i)) →
      NodeChildNonRootFieldDomain n a cs i v → F2)

abbrev NodeChildDataFamily
    (n a : Nat) [NeZero n] (cs : List RTree) :=
  (i : ChildIdx cs) → NodeChildDataAt n a cs i

noncomputable def childRootNonRootFieldsEquivChildDataFamily
    (n a : Nat) [NeZero n] (cs : List RTree) :
    NodeChildRootFieldAssignment n a cs ×
        NodeChildNonRootFieldAssignment n a cs ≃
      NodeChildDataFamily n a cs where
  toFun P := fun i => (P.1 i, P.2 i)
  invFun H := (fun i => (H i).1, fun i => (H i).2)
  left_inv P := by
    cases P
    rfl
  right_inv H := by
    funext i
    cases h : H i with
    | mk R N =>
        simp [h]

noncomputable def nodeChildVertexKindFieldEquivRootNonRootFields
    (n a : Nat) [NeZero n] (cs : List RTree) :
    NodeChildVertexKindFieldAssignment n a cs ≃
      NodeChildRootFieldAssignment n a cs ×
        NodeChildNonRootFieldAssignment n a cs where
  toFun K :=
    (fun i d => K ⟨i, Sum.inl ()⟩ d,
      fun i v d => K ⟨i, Sum.inr v⟩ d)
  invFun P := fun k =>
    match k with
    | ⟨i, Sum.inl _⟩ => P.1 i
    | ⟨i, Sum.inr v⟩ => P.2 i v
  left_inv K := by
    funext k d
    cases k with
    | mk i s =>
        cases s with
        | inl u =>
            cases u
            rfl
        | inr v =>
            rfl
  right_inv P := by
    cases P with
    | mk R N =>
        rfl

theorem sum_childVertexKindFields_eq_sum_root_nonRootFields
    {n a : Nat} [NeZero n] (cs : List RTree)
    (F : NodeChildVertexKindFieldAssignment n a cs → ℤ) :
    (∑ K : NodeChildVertexKindFieldAssignment n a cs, F K) =
      ∑ P : NodeChildRootFieldAssignment n a cs ×
          NodeChildNonRootFieldAssignment n a cs,
        F ((nodeChildVertexKindFieldEquivRootNonRootFields
          n a cs).symm P) := by
  classical
  exact (Equiv.sum_comp
    (nodeChildVertexKindFieldEquivRootNonRootFields n a cs).symm F).symm

theorem sum_root_nonRootFields_eq_sum_childDataFamily
    {n a : Nat} [NeZero n] (cs : List RTree)
    (F :
      NodeChildRootFieldAssignment n a cs ×
        NodeChildNonRootFieldAssignment n a cs → ℤ) :
    (∑ P : NodeChildRootFieldAssignment n a cs ×
        NodeChildNonRootFieldAssignment n a cs, F P) =
      ∑ H : NodeChildDataFamily n a cs,
        F ((childRootNonRootFieldsEquivChildDataFamily n a cs).symm H) := by
  classical
  exact (Equiv.sum_comp
    (childRootNonRootFieldsEquivChildDataFamily n a cs).symm F).symm

theorem sum_childDataFamily_product
    {n a : Nat} [NeZero n] (cs : List RTree)
    (g : (i : ChildIdx cs) → NodeChildDataAt n a cs i → ℤ) :
    (∑ H : NodeChildDataFamily n a cs,
      ∏ i : ChildIdx cs, g i (H i)) =
      ∏ i : ChildIdx cs, ∑ h : NodeChildDataAt n a cs i, g i h := by
  classical
  simpa [NodeChildDataFamily] using
    (sum_pi_product_dep (ι := ChildIdx cs) (R := ℤ)
      (α := fun i : ChildIdx cs => NodeChildDataAt n a cs i) g)

noncomputable def nodeFieldFromChildRootNonRootFields
    {n a : Nat} [NeZero n] {cs : List RTree}
    (P : NodeChildRootFieldAssignment n a cs ×
        NodeChildNonRootFieldAssignment n a cs) :
    NodeNonRootFieldAssignment n a cs :=
  (nodeChildVertexFieldAssignmentEquivNodeField n a cs)
    ((nodeChildVertexKindFieldAssignmentEquivChildVertexFields n a cs)
      ((nodeChildVertexKindFieldEquivRootNonRootFields n a cs).symm P))

noncomputable def nodeFieldFromChildDataFamily
    {n a : Nat} [NeZero n] {cs : List RTree}
    (H : NodeChildDataFamily n a cs) :
    NodeNonRootFieldAssignment n a cs :=
  nodeFieldFromChildRootNonRootFields
    (n := n) (a := a) (cs := cs)
    ((childRootNonRootFieldsEquivChildDataFamily n a cs).symm H)

@[simp] theorem nodeFieldFromChildDataFamily_childRoot
    {n a : Nat} [NeZero n] {cs : List RTree}
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs)
    (d : NodeChildRootFieldDomain n a cs i) :
    nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H
      ((nonRootVertexNodeEquivChildVertex a cs).symm
        ((nodeChildVertexEquivKind cs).symm ⟨i, Sum.inl ()⟩)) d =
      (H i).1 d := by
  simp [nodeFieldFromChildDataFamily, nodeFieldFromChildRootNonRootFields,
    nodeChildVertexFieldAssignmentEquivNodeField,
    nodeChildVertexKindFieldAssignmentEquivChildVertexFields,
    nodeChildVertexKindFieldEquivRootNonRootFields,
    childRootNonRootFieldsEquivChildDataFamily]

@[simp] theorem nodeFieldFromChildDataFamily_childNonRoot
    {n a : Nat} [NeZero n] {cs : List RTree}
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs)
    (v : NonRootVertex (childAt cs i))
    (d : NodeChildNonRootFieldDomain n a cs i v) :
    nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H
      ((nonRootVertexNodeEquivChildVertex a cs).symm
        ((nodeChildVertexEquivKind cs).symm ⟨i, Sum.inr v⟩)) d =
      (H i).2 v d := by
  simp [nodeFieldFromChildDataFamily, nodeFieldFromChildRootNonRootFields,
    nodeChildVertexFieldAssignmentEquivNodeField,
    nodeChildVertexKindFieldAssignmentEquivChildVertexFields,
    nodeChildVertexKindFieldEquivRootNonRootFields,
    childRootNonRootFieldsEquivChildDataFamily]

@[simp] theorem nodeFieldFromChildDataFamily_childRootAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs)
    (d : NonRootFieldDomain n (RTree.node a cs)
        (childRootAtAsNonRootInNode (a := a) i)) :
    nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H
      (childRootAtAsNonRootInNode (a := a) i) d =
      (H i).1 (by
        simpa [NodeChildRootFieldDomain] using d) := by
  convert nodeFieldFromChildDataFamily_childRoot
    (n := n) (a := a) (cs := cs) H i
    (by simpa [NodeChildRootFieldDomain] using d) using 1

@[simp] theorem nodeFieldFromChildDataFamily_childNonRootAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs)
    (v : NonRootVertex (childAt cs i))
    (d : NonRootFieldDomain n (RTree.node a cs)
        (childNonRootVertexAtInNode (a := a) i v)) :
    nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H
      (childNonRootVertexAtInNode (a := a) i v) d =
      (H i).2 v (by
        simpa [NodeChildNonRootFieldDomain] using d) := by
  convert nodeFieldFromChildDataFamily_childNonRoot
    (n := n) (a := a) (cs := cs) H i v
    (by simpa [NodeChildNonRootFieldDomain] using d) using 1

@[simp] theorem nodeFieldFromChildDataFamily_childRoot_get?
    {n a : Nat} [NeZero n] {cs : List RTree}
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs)
    (d : NonRootFieldDomain n (RTree.node a cs)
        (childRootAsNonRootInNode (a := a)
          (idx := i.1) (cs := cs) (C := childAt cs i)
          (childAt_get?_eq_some cs i))) :
    nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H
      (childRootAsNonRootInNode (a := a)
        (idx := i.1) (cs := cs) (C := childAt cs i)
        (childAt_get?_eq_some cs i)) d =
      (H i).1 (by
        simpa [NodeChildRootFieldDomain, childRootAtAsNonRootInNode] using d) := by
  convert nodeFieldFromChildDataFamily_childRoot
    (n := n) (a := a) (cs := cs) H i
    (by
      simpa [NodeChildRootFieldDomain, childRootAtAsNonRootInNode]
        using d) using 1

@[simp] theorem nodeFieldFromChildDataFamily_childNonRoot_get?
    {n a : Nat} [NeZero n] {cs : List RTree}
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs)
    (v : NonRootVertex (childAt cs i))
    (d : NonRootFieldDomain n (RTree.node a cs)
        (childNonRootVertexInNode (a := a)
          (idx := i.1) (cs := cs) (C := childAt cs i)
          (childAt_get?_eq_some cs i) v)) :
    nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H
      (childNonRootVertexInNode (a := a)
        (idx := i.1) (cs := cs) (C := childAt cs i)
        (childAt_get?_eq_some cs i) v) d =
      (H i).2 v (by
        simpa [NodeChildNonRootFieldDomain, childNonRootVertexAtInNode]
          using d) := by
  convert nodeFieldFromChildDataFamily_childNonRoot
    (n := n) (a := a) (cs := cs) H i v
    (by
      simpa [NodeChildNonRootFieldDomain, childNonRootVertexAtInNode]
        using d) using 1

noncomputable def childDataFamilyWithAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) (h : NodeChildDataAt n a cs i) :
    NodeChildDataFamily n a cs :=
  fun j => by
    by_cases hji : j = i
    · subst j
      exact h
    · exact Classical.choice inferInstance

@[simp] theorem childDataFamilyWithAt_self
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) (h : NodeChildDataAt n a cs i) :
    childDataFamilyWithAt (n := n) (a := a) (cs := cs) i h i = h := by
  simp [childDataFamilyWithAt]

def finCastEquivOfEq {m k : Nat} (h : m = k) : Fin m ≃ Fin k where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv := by
    intro x
    cases h
    simp
  right_inv := by
    intro x
    cases h
    simp

def childRootFullCoordInNode {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) :
    Fin C.rootWeight ≃
      Fin (NonRootVertex.weight (childRootAsNonRootInNode (a := a) hget)) :=
  finCastEquivOfEq (childRootAsNonRootInNode_weight (a := a) hget).symm

def childRootCoordInNode {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) :
    Fin (C.rootWeight - 1) →
      Fin (NonRootVertex.weight (childRootAsNonRootInNode (a := a) hget)) :=
  fun j =>
    childRootFullCoordInNode (a := a) hget
      (Fin.castLE (Nat.sub_le C.rootWeight 1) j)

def childNonRootCoordInNode {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) (v : NonRootVertex C) :
    Fin (NonRootVertex.weight v) ≃
      Fin (NonRootVertex.weight (childNonRootVertexInNode (a := a) hget v)) :=
  finCastEquivOfEq (childNonRootVertexInNode_weight (a := a) hget v).symm

noncomputable def childRootFieldFromParent
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C)
    (rd : RootFieldDomain n (RTree.node a cs)) :
    RootFieldDomain n C :=
  fun v j =>
    rd (childNonRootVertexInNode (a := a) hget v)
      (childNonRootCoordInNode (a := a) hget v j)

noncomputable def childRootFieldAtFromParent
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (i : ChildIdx cs)
    (rd : RootFieldDomain n (RTree.node a cs)) :
    RootFieldDomain n (childAt cs i) :=
  childRootFieldFromParent (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i) rd

noncomputable def childSiteFromParent
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C)
    (site : NormalSite n (RTree.node a cs)) : NormalSite n C where
  rootCoord := fun j =>
    site.nonRootCoord (childRootAsNonRootInNode (a := a) hget)
      (childRootCoordInNode (a := a) hget j)
  nonRootCoord := childRootFieldFromParent (a := a) hget site.nonRootCoord

noncomputable def childSiteAtFromParent
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (i : ChildIdx cs)
    (site : NormalSite n (RTree.node a cs)) :
    NormalSite n (childAt cs i) :=
  childSiteFromParent (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i) site

@[simp] theorem childRootFieldFromParent_apply
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C)
    (rd : RootFieldDomain n (RTree.node a cs))
    (v : NonRootVertex C) (j : Fin (NonRootVertex.weight v)) :
    childRootFieldFromParent (a := a) hget rd v j =
      rd (childNonRootVertexInNode (a := a) hget v)
        (childNonRootCoordInNode (a := a) hget v j) := rfl

@[simp] theorem childRootFieldAtFromParent_apply
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (i : ChildIdx cs)
    (rd : RootFieldDomain n (RTree.node a cs))
    (v : NonRootVertex (childAt cs i))
    (j : Fin (NonRootVertex.weight v)) :
    childRootFieldAtFromParent (a := a) i rd v j =
      rd (childNonRootVertexAtInNode (a := a) i v)
        (childNonRootCoordInNode (a := a)
          (idx := i.1) (cs := cs) (C := childAt cs i)
          (childAt_get?_eq_some cs i) v j) := rfl

@[simp] theorem childSiteFromParent_rootCoord
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C)
    (site : NormalSite n (RTree.node a cs))
    (j : Fin (C.rootWeight - 1)) :
    (childSiteFromParent (a := a) hget site).rootCoord j =
      site.nonRootCoord (childRootAsNonRootInNode (a := a) hget)
        (childRootCoordInNode (a := a) hget j) := rfl

@[simp] theorem childSiteAtFromParent_rootCoord
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (i : ChildIdx cs)
    (site : NormalSite n (RTree.node a cs))
    (j : Fin ((childAt cs i).rootWeight - 1)) :
    (childSiteAtFromParent (a := a) i site).rootCoord j =
      site.nonRootCoord (childRootAtAsNonRootInNode (a := a) i)
        (childRootCoordInNode (a := a)
          (idx := i.1) (cs := cs) (C := childAt cs i)
          (childAt_get?_eq_some cs i) j) := rfl

@[simp] theorem childSiteFromParent_nonRootCoord
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C)
    (site : NormalSite n (RTree.node a cs))
    (v : NonRootVertex C) (j : Fin (NonRootVertex.weight v)) :
    (childSiteFromParent (a := a) hget site).nonRootCoord v j =
      site.nonRootCoord (childNonRootVertexInNode (a := a) hget v)
        (childNonRootCoordInNode (a := a) hget v j) := rfl

@[simp] theorem childSiteAtFromParent_nonRootCoord
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (i : ChildIdx cs)
    (site : NormalSite n (RTree.node a cs))
    (v : NonRootVertex (childAt cs i))
    (j : Fin (NonRootVertex.weight v)) :
    (childSiteAtFromParent (a := a) i site).nonRootCoord v j =
      site.nonRootCoord (childNonRootVertexAtInNode (a := a) i v)
        (childNonRootCoordInNode (a := a)
          (idx := i.1) (cs := cs) (C := childAt cs i)
          (childAt_get?_eq_some cs i) v j) := rfl

noncomputable def diagonal {n : Nat} [NeZero n] {T : RTree}
    (site : NormalSite n T) (v : NonRootVertex T) : ZMod n :=
  ∑ j : Fin (NonRootVertex.weight v), site.nonRootCoord v j

theorem diagonal_childSiteFromParent_nonRoot
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C)
    (site : NormalSite n (RTree.node a cs)) (v : NonRootVertex C) :
    diagonal (childSiteFromParent (a := a) hget site) v =
      diagonal site (childNonRootVertexInNode (a := a) hget v) := by
  classical
  unfold diagonal
  refine Fintype.sum_equiv
    (childNonRootCoordInNode (a := a) hget v)
    (fun j : Fin (NonRootVertex.weight v) =>
      site.nonRootCoord (childNonRootVertexInNode (a := a) hget v)
        (childNonRootCoordInNode (a := a) hget v j))
    (fun j :
      Fin (NonRootVertex.weight
        (childNonRootVertexInNode (a := a) hget v)) =>
      site.nonRootCoord (childNonRootVertexInNode (a := a) hget v) j)
    ?_
  intro j
  rfl

theorem diagonal_childSiteAtFromParent_nonRoot
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (i : ChildIdx cs)
    (site : NormalSite n (RTree.node a cs))
    (v : NonRootVertex (childAt cs i)) :
    diagonal (childSiteAtFromParent (a := a) i site) v =
      diagonal site (childNonRootVertexAtInNode (a := a) i v) :=
  diagonal_childSiteFromParent_nonRoot (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i) site v

noncomputable def nonRootDomainOfSite {n : Nat} [NeZero n] {T : RTree}
    (site : NormalSite n T) (v : NonRootVertex T)
    (shift : ZMod n) : NonRootFieldDomain n T v where
  rootCoord := site.rootCoord
  diagonal := diagonal site v + shift
  otherCoord := fun u => site.nonRootCoord u.1

noncomputable def ketAtVertex {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) (site : NormalSite n T) (v : Vertex T) : F2 :=
  if hv : v.1 = [] then
    A.rootField site.nonRootCoord
  else
    A.nodeField ⟨v, hv⟩ (nonRootDomainOfSite site ⟨v, hv⟩ 0)

noncomputable def braAtVertex {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) (site : NormalSite n T) (v : Vertex T) : F2 :=
  if hv : v.1 = [] then
    A.rootField site.nonRootCoord
  else
    A.nodeField ⟨v, hv⟩ (nonRootDomainOfSite site ⟨v, hv⟩ 1)

@[simp] theorem ketAtVertex_childRootInNode
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) :
    ketAtVertex A site (childVertexInNode (a := a) hget (Vertex.root C)) =
      A.nodeField (childRootAsNonRootInNode (a := a) hget)
        (nonRootDomainOfSite site (childRootAsNonRootInNode (a := a) hget) 0) := by
  simp [ketAtVertex, childRootAsNonRootInNode, childVertexInNode]

@[simp] theorem braAtVertex_childRootInNode
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) :
    braAtVertex A site (childVertexInNode (a := a) hget (Vertex.root C)) =
      A.nodeField (childRootAsNonRootInNode (a := a) hget)
        (nonRootDomainOfSite site (childRootAsNonRootInNode (a := a) hget) 1) := by
  simp [braAtVertex, childRootAsNonRootInNode, childVertexInNode]

@[simp] theorem ketAtVertex_childNonRootInNode
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) (v : NonRootVertex C) :
    ketAtVertex A site (childVertexInNode (a := a) hget v.1) =
      A.nodeField (childNonRootVertexInNode (a := a) hget v)
        (nonRootDomainOfSite site
          (childNonRootVertexInNode (a := a) hget v) 0) := by
  simp [ketAtVertex, childNonRootVertexInNode, childVertexInNode]

@[simp] theorem braAtVertex_childNonRootInNode
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) (v : NonRootVertex C) :
    braAtVertex A site (childVertexInNode (a := a) hget v.1) =
      A.nodeField (childNonRootVertexInNode (a := a) hget v)
        (nonRootDomainOfSite site
          (childNonRootVertexInNode (a := a) hget v) 1) := by
  simp [braAtVertex, childNonRootVertexInNode, childVertexInNode]

noncomputable def ketAtPath {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) (site : NormalSite n T) (p : List Nat) : F2 :=
  if hp : p ∈ RTree.addresses T then
    ketAtVertex A site ⟨p, hp⟩
  else
    0

noncomputable def braAtPath {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) (site : NormalSite n T) (p : List Nat) : F2 :=
  if hp : p ∈ RTree.addresses T then
    braAtVertex A site ⟨p, hp⟩
  else
    0

@[simp] theorem ketAtPath_root {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) (site : NormalSite n T) :
    ketAtPath A site [] = A.rootField site.nonRootCoord := by
  simp [ketAtPath, ketAtVertex]

@[simp] theorem braAtPath_root {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) (site : NormalSite n T) :
    braAtPath A site [] = A.rootField site.nonRootCoord := by
  simp [braAtPath, braAtVertex]

theorem ketAtPath_childAddress_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree} {p : List Nat}
    (hget : cs[idx]? = some C) (hp : p ∈ RTree.addresses C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) :
    ketAtPath A site (idx :: p) =
      ketAtVertex A site
        ⟨idx :: p,
          RTree.childAddress_mem_addresses_node_of_get?
            (a := a) hget hp⟩ := by
  have haddr :
      idx :: p ∈ RTree.addresses (RTree.node a cs) :=
    RTree.childAddress_mem_addresses_node_of_get?
      (a := a) hget hp
  unfold ketAtPath
  rw [dif_pos haddr]

theorem braAtPath_childAddress_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree} {p : List Nat}
    (hget : cs[idx]? = some C) (hp : p ∈ RTree.addresses C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) :
    braAtPath A site (idx :: p) =
      braAtVertex A site
        ⟨idx :: p,
          RTree.childAddress_mem_addresses_node_of_get?
            (a := a) hget hp⟩ := by
  have haddr :
      idx :: p ∈ RTree.addresses (RTree.node a cs) :=
    RTree.childAddress_mem_addresses_node_of_get?
      (a := a) hget hp
  unfold braAtPath
  rw [dif_pos haddr]

@[simp] theorem ketAtPath_childRoot_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) :
    ketAtPath A site [idx] =
      A.nodeField (childRootAsNonRootInNode (a := a) hget)
        (nonRootDomainOfSite site (childRootAsNonRootInNode (a := a) hget) 0) := by
  simpa using
    ketAtPath_childAddress_of_get? (a := a) (idx := idx)
      (C := C) (p := []) hget (RTree.nil_mem_addresses C) A site

@[simp] theorem braAtPath_childRoot_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) :
    braAtPath A site [idx] =
      A.nodeField (childRootAsNonRootInNode (a := a) hget)
        (nonRootDomainOfSite site (childRootAsNonRootInNode (a := a) hget) 1) := by
  simpa using
    braAtPath_childAddress_of_get? (a := a) (idx := idx)
      (C := C) (p := []) hget (RTree.nil_mem_addresses C) A site

@[simp] theorem ketAtPath_childNonRoot_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) (v : NonRootVertex C) :
    ketAtPath A site (idx :: v.1.1) =
      A.nodeField (childNonRootVertexInNode (a := a) hget v)
        (nonRootDomainOfSite site
          (childNonRootVertexInNode (a := a) hget v) 0) := by
  simpa using
    ketAtPath_childAddress_of_get? (a := a) (idx := idx)
      (C := C) (p := v.1.1) hget v.1.2 A site

@[simp] theorem braAtPath_childNonRoot_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) (v : NonRootVertex C) :
    braAtPath A site (idx :: v.1.1) =
      A.nodeField (childNonRootVertexInNode (a := a) hget v)
        (nonRootDomainOfSite site
          (childNonRootVertexInNode (a := a) hget v) 1) := by
  simpa using
    braAtPath_childAddress_of_get? (a := a) (idx := idx)
      (C := C) (p := v.1.1) hget v.1.2 A site

noncomputable def edgePhaseAtSite {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) (site : NormalSite n T)
    (e : List Nat × List Nat) : F2 :=
  ketAtPath A site e.1 * ketAtPath A site e.2
    + braAtPath A site e.1 * braAtPath A site e.2

theorem edgePhaseAtSite_child_vertices_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs))
    (u v : Vertex C) :
    edgePhaseAtSite A site (idx :: u.1, idx :: v.1) =
      ketAtVertex A site (childVertexInNode (a := a) hget u) *
        ketAtVertex A site (childVertexInNode (a := a) hget v) +
      braAtVertex A site (childVertexInNode (a := a) hget u) *
        braAtVertex A site (childVertexInNode (a := a) hget v) := by
  unfold edgePhaseAtSite
  rw [ketAtPath_childAddress_of_get? (a := a) (idx := idx)
      (C := C) (p := u.1) hget u.2 A site]
  rw [ketAtPath_childAddress_of_get? (a := a) (idx := idx)
      (C := C) (p := v.1) hget v.2 A site]
  rw [braAtPath_childAddress_of_get? (a := a) (idx := idx)
      (C := C) (p := u.1) hget u.2 A site]
  rw [braAtPath_childAddress_of_get? (a := a) (idx := idx)
      (C := C) (p := v.1) hget v.2 A site]
  simp [childVertexInNode]

theorem edgePhaseAtSite_prefixEdge_child_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs))
    {e : List Nat × List Nat} (he : e ∈ RTree.edgeList C) :
    edgePhaseAtSite A site (RTree.prefixEdge [idx] e) =
      ketAtVertex A site
          (childVertexInNode (a := a) hget
            ⟨e.1, RTree.edgeList_edge_left_mem_addresses C he⟩) *
        ketAtVertex A site
          (childVertexInNode (a := a) hget
            ⟨e.2, RTree.edgeList_edge_right_mem_addresses C he⟩) +
      braAtVertex A site
          (childVertexInNode (a := a) hget
            ⟨e.1, RTree.edgeList_edge_left_mem_addresses C he⟩) *
        braAtVertex A site
          (childVertexInNode (a := a) hget
            ⟨e.2, RTree.edgeList_edge_right_mem_addresses C he⟩) := by
  simpa [RTree.prefixEdge] using
    edgePhaseAtSite_child_vertices_of_get? (a := a) (idx := idx)
      (C := C) hget A site
      ⟨e.1, RTree.edgeList_edge_left_mem_addresses C he⟩
      ⟨e.2, RTree.edgeList_edge_right_mem_addresses C he⟩

theorem edgePhaseAtSite_prefixEdge_childAt
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (i : ChildIdx cs)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs))
    {e : List Nat × List Nat} (he : e ∈ RTree.edgeList (childAt cs i)) :
    edgePhaseAtSite A site (RTree.prefixEdge [i.1] e) =
      ketAtVertex A site
          (childVertexAtInNode (a := a) i
            ⟨e.1, RTree.edgeList_edge_left_mem_addresses
              (childAt cs i) he⟩) *
        ketAtVertex A site
          (childVertexAtInNode (a := a) i
            ⟨e.2, RTree.edgeList_edge_right_mem_addresses
              (childAt cs i) he⟩) +
      braAtVertex A site
          (childVertexAtInNode (a := a) i
            ⟨e.1, RTree.edgeList_edge_left_mem_addresses
              (childAt cs i) he⟩) *
        braAtVertex A site
          (childVertexAtInNode (a := a) i
            ⟨e.2, RTree.edgeList_edge_right_mem_addresses
              (childAt cs i) he⟩) :=
  edgePhaseAtSite_prefixEdge_child_of_get? (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i) A site he

theorem edgePhaseAtSite_boundary_childRoot_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) :
    edgePhaseAtSite A site ([], [idx]) =
      A.rootField site.nonRootCoord *
        A.nodeField (childRootAsNonRootInNode (a := a) hget)
          (nonRootDomainOfSite site
            (childRootAsNonRootInNode (a := a) hget) 0) +
      A.rootField site.nonRootCoord *
        A.nodeField (childRootAsNonRootInNode (a := a) hget)
          (nonRootDomainOfSite site
            (childRootAsNonRootInNode (a := a) hget) 1) := by
  unfold edgePhaseAtSite
  rw [ketAtPath_root, braAtPath_root]
  rw [ketAtPath_childRoot_of_get? (a := a) (idx := idx)
      (C := C) hget A site]
  rw [braAtPath_childRoot_of_get? (a := a) (idx := idx)
      (C := C) hget A site]

theorem edgePhaseAtSite_boundary_childRootAt
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (i : ChildIdx cs)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) :
    edgePhaseAtSite A site ([], [i.1]) =
      A.rootField site.nonRootCoord *
        A.nodeField (childRootAtAsNonRootInNode (a := a) i)
          (nonRootDomainOfSite site
            (childRootAtAsNonRootInNode (a := a) i) 0) +
      A.rootField site.nonRootCoord *
        A.nodeField (childRootAtAsNonRootInNode (a := a) i)
          (nonRootDomainOfSite site
            (childRootAtAsNonRootInNode (a := a) i) 1) :=
  edgePhaseAtSite_boundary_childRoot_of_get? (a := a)
    (idx := i.1) (cs := cs) (C := childAt cs i)
    (childAt_get?_eq_some cs i) A site

theorem edgePhaseAtSite_childRoot_childNonRoot_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) (v : NonRootVertex C) :
    edgePhaseAtSite A site ([idx], idx :: v.1.1) =
      A.nodeField (childRootAsNonRootInNode (a := a) hget)
          (nonRootDomainOfSite site
            (childRootAsNonRootInNode (a := a) hget) 0) *
        A.nodeField (childNonRootVertexInNode (a := a) hget v)
          (nonRootDomainOfSite site
            (childNonRootVertexInNode (a := a) hget v) 0) +
      A.nodeField (childRootAsNonRootInNode (a := a) hget)
          (nonRootDomainOfSite site
            (childRootAsNonRootInNode (a := a) hget) 1) *
        A.nodeField (childNonRootVertexInNode (a := a) hget v)
          (nonRootDomainOfSite site
            (childNonRootVertexInNode (a := a) hget v) 1) := by
  unfold edgePhaseAtSite
  rw [ketAtPath_childRoot_of_get? (a := a) (idx := idx)
      (C := C) hget A site]
  rw [ketAtPath_childNonRoot_of_get? (a := a) (idx := idx)
      (C := C) hget A site v]
  rw [braAtPath_childRoot_of_get? (a := a) (idx := idx)
      (C := C) hget A site]
  rw [braAtPath_childNonRoot_of_get? (a := a) (idx := idx)
      (C := C) hget A site v]

theorem edgePhaseAtSite_childNonRoot_childNonRoot_of_get?
    {n : Nat} [NeZero n] {a idx : Nat} {cs : List RTree}
    {C : RTree}
    (hget : cs[idx]? = some C)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs))
    (u v : NonRootVertex C) :
    edgePhaseAtSite A site (idx :: u.1.1, idx :: v.1.1) =
      A.nodeField (childNonRootVertexInNode (a := a) hget u)
          (nonRootDomainOfSite site
            (childNonRootVertexInNode (a := a) hget u) 0) *
        A.nodeField (childNonRootVertexInNode (a := a) hget v)
          (nonRootDomainOfSite site
            (childNonRootVertexInNode (a := a) hget v) 0) +
      A.nodeField (childNonRootVertexInNode (a := a) hget u)
          (nonRootDomainOfSite site
            (childNonRootVertexInNode (a := a) hget u) 1) *
        A.nodeField (childNonRootVertexInNode (a := a) hget v)
          (nonRootDomainOfSite site
            (childNonRootVertexInNode (a := a) hget v) 1) := by
  unfold edgePhaseAtSite
  rw [ketAtPath_childNonRoot_of_get? (a := a) (idx := idx)
      (C := C) hget A site u]
  rw [ketAtPath_childNonRoot_of_get? (a := a) (idx := idx)
      (C := C) hget A site v]
  rw [braAtPath_childNonRoot_of_get? (a := a) (idx := idx)
      (C := C) hget A site u]
  rw [braAtPath_childNonRoot_of_get? (a := a) (idx := idx)
      (C := C) hget A site v]

noncomputable def phaseAtSite {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignment n T) (site : NormalSite n T) : F2 :=
  (RTree.edgeList T).map (edgePhaseAtSite A site) |>.sum

noncomputable def totalPhase {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignment n T) : F2 :=
  ∑ site : NormalSite n T, phaseAtSite T A site

noncomputable def edgeListPhase {n : Nat} [NeZero n] (T : RTree)
    (edges : List (List Nat × List Nat)) (A : NormalAssignment n T) : F2 :=
  ∑ site : NormalSite n T, (edges.map (edgePhaseAtSite A site)).sum

@[simp] theorem edgeListPhase_nil
    {n : Nat} [NeZero n] (T : RTree) (A : NormalAssignment n T) :
    edgeListPhase T [] A = 0 := by
  simp [edgeListPhase]

theorem totalPhase_eq_edgeListPhase
    {n : Nat} [NeZero n] (T : RTree) (A : NormalAssignment n T) :
    totalPhase T A = edgeListPhase T (RTree.edgeList T) A := by
  rfl

theorem edgeListPhase_append
    {n : Nat} [NeZero n] (T : RTree)
    (left right : List (List Nat × List Nat))
    (A : NormalAssignment n T) :
    edgeListPhase T (left ++ right) A =
      edgeListPhase T left A + edgeListPhase T right A := by
  unfold edgeListPhase
  calc
    (∑ site : NormalSite n T,
        ((left ++ right).map (edgePhaseAtSite A site)).sum) =
        ∑ site : NormalSite n T,
          ((left.map (edgePhaseAtSite A site)).sum +
            (right.map (edgePhaseAtSite A site)).sum) := by
          simp [List.map_append]
    _ =
        (∑ site : NormalSite n T,
          (left.map (edgePhaseAtSite A site)).sum) +
          ∑ site : NormalSite n T,
            (right.map (edgePhaseAtSite A site)).sum := by
          rw [Finset.sum_add_distrib]

theorem edgeListPhase_edgeListFrom_eq_prefix
    {n : Nat} [NeZero n] {T : RTree}
    (parent : List Nat) (C : RTree) (A : NormalAssignment n T) :
    edgeListPhase T (RTree.edgeListFrom parent C) A =
      edgeListPhase T
        ((RTree.edgeList C).map (RTree.prefixEdge parent)) A := by
  rw [RTree.edgeListFrom_eq_edgeList_map_prefix]

theorem edgeListPhase_map_prefix_eq_sum_prefixed
    {n : Nat} [NeZero n] {T : RTree}
    (parent : List Nat) (C : RTree) (A : NormalAssignment n T) :
    edgeListPhase T
        ((RTree.edgeList C).map (RTree.prefixEdge parent)) A =
      ∑ site : NormalSite n T,
        ((RTree.edgeList C).map
          (fun e => edgePhaseAtSite A site (RTree.prefixEdge parent e))).sum := by
  unfold edgeListPhase
  simp [List.map_map, Function.comp_def]

theorem edgeListPhase_edgeListFrom_eq_sum_prefixed
    {n : Nat} [NeZero n] {T : RTree}
    (parent : List Nat) (C : RTree) (A : NormalAssignment n T) :
    edgeListPhase T (RTree.edgeListFrom parent C) A =
      ∑ site : NormalSite n T,
        ((RTree.edgeList C).map
          (fun e => edgePhaseAtSite A site (RTree.prefixEdge parent e))).sum := by
  rw [edgeListPhase_edgeListFrom_eq_prefix]
  exact edgeListPhase_map_prefix_eq_sum_prefixed parent C A

@[simp] theorem edgeListPhase_singleton
    {n : Nat} [NeZero n] (T : RTree)
    (e : List Nat × List Nat) (A : NormalAssignment n T) :
    edgeListPhase T [e] A =
      ∑ site : NormalSite n T, edgePhaseAtSite A site e := by
  simp [edgeListPhase]

noncomputable def indexedChildBoundaryPhase {n : Nat} [NeZero n]
    (T : RTree) (parent : List Nat) (start : Nat) (cs : List RTree)
    (A : NormalAssignment n T) : F2 :=
  edgeListPhase T (RTree.indexedChildBoundaryEdgesFrom parent start cs) A

noncomputable def indexedChildInternalPhase {n : Nat} [NeZero n]
    (T : RTree) (parent : List Nat) (start : Nat) (cs : List RTree)
    (A : NormalAssignment n T) : F2 :=
  edgeListPhase T (RTree.indexedChildInternalEdgesFrom parent start cs) A

@[simp] theorem indexedChildBoundaryPhase_nil
    {n : Nat} [NeZero n] (T : RTree) (parent : List Nat)
    (start : Nat) (A : NormalAssignment n T) :
    indexedChildBoundaryPhase T parent start [] A = 0 := by
  simp [indexedChildBoundaryPhase]

@[simp] theorem indexedChildInternalPhase_nil
    {n : Nat} [NeZero n] (T : RTree) (parent : List Nat)
    (start : Nat) (A : NormalAssignment n T) :
    indexedChildInternalPhase T parent start [] A = 0 := by
  simp [indexedChildInternalPhase]

theorem indexedChildBoundaryPhase_cons
    {n : Nat} [NeZero n] (T : RTree) (parent : List Nat)
    (start : Nat) (C : RTree) (rest : List RTree)
    (A : NormalAssignment n T) :
    indexedChildBoundaryPhase T parent start (C :: rest) A =
      edgeListPhase T [(parent, parent ++ [start])] A +
        indexedChildBoundaryPhase T parent (start + 1) rest A := by
  unfold indexedChildBoundaryPhase
  change
    edgeListPhase T
      ([(parent, parent ++ [start])] ++
        RTree.indexedChildBoundaryEdgesFrom parent (start + 1) rest) A =
      edgeListPhase T [(parent, parent ++ [start])] A +
        edgeListPhase T
          (RTree.indexedChildBoundaryEdgesFrom parent (start + 1) rest) A
  exact edgeListPhase_append T [(parent, parent ++ [start])]
    (RTree.indexedChildBoundaryEdgesFrom parent (start + 1) rest) A

theorem indexedChildInternalPhase_cons
    {n : Nat} [NeZero n] (T : RTree) (parent : List Nat)
    (start : Nat) (C : RTree) (rest : List RTree)
    (A : NormalAssignment n T) :
    indexedChildInternalPhase T parent start (C :: rest) A =
      edgeListPhase T
          ((RTree.edgeList C).map
            (RTree.prefixEdge (parent ++ [start]))) A +
        indexedChildInternalPhase T parent (start + 1) rest A := by
  unfold indexedChildInternalPhase
  change
    edgeListPhase T
      (RTree.edgeListFrom (parent ++ [start]) C ++
        RTree.indexedChildInternalEdgesFrom parent (start + 1) rest) A =
      edgeListPhase T
          ((RTree.edgeList C).map
            (RTree.prefixEdge (parent ++ [start]))) A +
        edgeListPhase T
          (RTree.indexedChildInternalEdgesFrom parent (start + 1) rest) A
  rw [edgeListPhase_append]
  rw [edgeListPhase_edgeListFrom_eq_prefix]

noncomputable def indexedChildBoundaryPhaseAt
    {n : Nat} [NeZero n] (T : RTree) (parent : List Nat)
    (start : Nat) (cs : List RTree) (i : ChildIdx cs)
    (A : NormalAssignment n T) : F2 :=
  edgeListPhase T [(parent, parent ++ [start + i.1])] A

noncomputable def indexedChildInternalPhaseAt
    {n : Nat} [NeZero n] (T : RTree) (parent : List Nat)
    (start : Nat) (cs : List RTree) (i : ChildIdx cs)
    (A : NormalAssignment n T) : F2 :=
  edgeListPhase T
    (RTree.edgeListFrom (parent ++ [start + i.1]) (childAt cs i)) A

noncomputable def indexedChildLocalPhaseAt
    {n : Nat} [NeZero n] (T : RTree) (parent : List Nat)
    (start : Nat) (cs : List RTree) (i : ChildIdx cs)
    (A : NormalAssignment n T) : F2 :=
  indexedChildBoundaryPhaseAt T parent start cs i A +
    indexedChildInternalPhaseAt T parent start cs i A

theorem indexedChildBoundaryPhase_eq_sum_phaseAt
    {n : Nat} [NeZero n] (T : RTree) (parent : List Nat)
    (start : Nat) :
    ∀ (cs : List RTree) (A : NormalAssignment n T),
      indexedChildBoundaryPhase T parent start cs A =
        ∑ i : ChildIdx cs,
          indexedChildBoundaryPhaseAt T parent start cs i A
  | [], A => by
      rw [indexedChildBoundaryPhase_nil]
      change 0 =
        ∑ i : Fin 0, indexedChildBoundaryPhaseAt T parent start [] i A
      simp
  | C :: rest, A => by
      rw [indexedChildBoundaryPhase_cons]
      change
        edgeListPhase T [(parent, parent ++ [start])] A +
            indexedChildBoundaryPhase T parent (start + 1) rest A =
          ∑ i : Fin (rest.length + 1),
            indexedChildBoundaryPhaseAt T parent start (C :: rest) i A
      have htail :=
        indexedChildBoundaryPhase_eq_sum_phaseAt
          T parent (start + 1) rest A
      calc
        edgeListPhase T [(parent, parent ++ [start])] A +
            indexedChildBoundaryPhase T parent (start + 1) rest A =
            edgeListPhase T [(parent, parent ++ [start])] A +
              ∑ i : ChildIdx rest,
                indexedChildBoundaryPhaseAt T parent (start + 1) rest i A := by
              rw [htail]
        _ =
            edgeListPhase T [(parent, parent ++ [start])] A +
              ∑ i : Fin rest.length,
                indexedChildBoundaryPhaseAt T parent start (C :: rest) i.succ A := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [indexedChildBoundaryPhaseAt, Nat.add_comm,
                Nat.add_left_comm]
        _ =
            ∑ i : Fin (rest.length + 1),
              indexedChildBoundaryPhaseAt T parent start (C :: rest) i A := by
              rw [Fin.sum_univ_succ]
              simp [indexedChildBoundaryPhaseAt]

theorem indexedChildInternalPhase_eq_sum_phaseAt
    {n : Nat} [NeZero n] (T : RTree) (parent : List Nat)
    (start : Nat) :
    ∀ (cs : List RTree) (A : NormalAssignment n T),
      indexedChildInternalPhase T parent start cs A =
        ∑ i : ChildIdx cs,
          indexedChildInternalPhaseAt T parent start cs i A
  | [], A => by
      rw [indexedChildInternalPhase_nil]
      change 0 =
        ∑ i : Fin 0, indexedChildInternalPhaseAt T parent start [] i A
      simp
  | C :: rest, A => by
      rw [indexedChildInternalPhase_cons]
      change
        edgeListPhase T
              ((RTree.edgeList C).map
                (RTree.prefixEdge (parent ++ [start]))) A +
            indexedChildInternalPhase T parent (start + 1) rest A =
          ∑ i : Fin (rest.length + 1),
            indexedChildInternalPhaseAt T parent start (C :: rest) i A
      have htail :=
        indexedChildInternalPhase_eq_sum_phaseAt
          T parent (start + 1) rest A
      calc
        edgeListPhase T
              ((RTree.edgeList C).map
                (RTree.prefixEdge (parent ++ [start]))) A +
            indexedChildInternalPhase T parent (start + 1) rest A =
            edgeListPhase T
                ((RTree.edgeList C).map
                  (RTree.prefixEdge (parent ++ [start]))) A +
              ∑ i : ChildIdx rest,
                indexedChildInternalPhaseAt T parent (start + 1) rest i A := by
              rw [htail]
        _ =
            edgeListPhase T
                ((RTree.edgeList C).map
                  (RTree.prefixEdge (parent ++ [start]))) A +
              ∑ i : Fin rest.length,
                indexedChildInternalPhaseAt T parent start (C :: rest) i.succ A := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [indexedChildInternalPhaseAt, Nat.add_comm,
                Nat.add_left_comm]
        _ =
            ∑ i : Fin (rest.length + 1),
              indexedChildInternalPhaseAt T parent start (C :: rest) i A := by
              rw [Fin.sum_univ_succ]
              simp [indexedChildInternalPhaseAt,
                edgeListPhase_edgeListFrom_eq_prefix,
                childAt, List.get_eq_getElem]

noncomputable def nodeBoundaryPhase {n : Nat} [NeZero n]
    (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) : F2 :=
  ∑ site : NormalSite n (RTree.node a cs),
    ((RTree.indexedChildBoundaryEdgesFrom [] 0 cs).map
      (edgePhaseAtSite A site)).sum

noncomputable def nodeInternalPhase {n : Nat} [NeZero n]
    (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) : F2 :=
  ∑ site : NormalSite n (RTree.node a cs),
    ((RTree.indexedChildInternalEdgesFrom [] 0 cs).map
      (edgePhaseAtSite A site)).sum

noncomputable def childBoundaryPhaseAt
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (i : ChildIdx cs)
    (A : NormalAssignment n (RTree.node a cs)) : F2 :=
  indexedChildBoundaryPhaseAt (RTree.node a cs) [] 0 cs i A

noncomputable def childInternalPhaseAt
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (i : ChildIdx cs)
    (A : NormalAssignment n (RTree.node a cs)) : F2 :=
  indexedChildInternalPhaseAt (RTree.node a cs) [] 0 cs i A

noncomputable def childLocalPhaseAt
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (i : ChildIdx cs)
    (A : NormalAssignment n (RTree.node a cs)) : F2 :=
  childBoundaryPhaseAt a cs i A + childInternalPhaseAt a cs i A

noncomputable def childBoundaryInternalContributionAt
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (i : ChildIdx cs)
    (A : NormalAssignment n (RTree.node a cs)) : ℤ :=
  bitSign (childBoundaryPhaseAt a cs i A) *
    bitSign (childInternalPhaseAt a cs i A)

theorem nodeBoundaryPhase_eq_sum_childBoundaryPhaseAt
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) :
    nodeBoundaryPhase a cs A =
      ∑ i : ChildIdx cs, childBoundaryPhaseAt a cs i A := by
  exact indexedChildBoundaryPhase_eq_sum_phaseAt
    (RTree.node a cs) [] 0 cs A

theorem nodeInternalPhase_eq_sum_childInternalPhaseAt
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) :
    nodeInternalPhase a cs A =
      ∑ i : ChildIdx cs, childInternalPhaseAt a cs i A := by
  exact indexedChildInternalPhase_eq_sum_phaseAt
    (RTree.node a cs) [] 0 cs A

theorem nodeBoundary_add_internal_eq_sum_childLocalPhaseAt
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) :
    nodeBoundaryPhase a cs A + nodeInternalPhase a cs A =
      ∑ i : ChildIdx cs, childLocalPhaseAt a cs i A := by
  rw [nodeBoundaryPhase_eq_sum_childBoundaryPhaseAt,
    nodeInternalPhase_eq_sum_childInternalPhaseAt]
  rw [← Finset.sum_add_distrib]
  rfl

theorem childBoundaryInternalContributionAt_eq_bitSign_localPhase
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (i : ChildIdx cs)
    (A : NormalAssignment n (RTree.node a cs)) :
    childBoundaryInternalContributionAt a cs i A =
      bitSign (childLocalPhaseAt a cs i A) := by
  unfold childBoundaryInternalContributionAt childLocalPhaseAt
  exact (bitSign_add _ _).symm

theorem phaseAtSite_node_eq_boundary_add_internal
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs))
    (site : NormalSite n (RTree.node a cs)) :
    phaseAtSite (RTree.node a cs) A site =
      ((RTree.indexedChildBoundaryEdgesFrom [] 0 cs).map
        (edgePhaseAtSite A site)).sum +
        ((RTree.indexedChildInternalEdgesFrom [] 0 cs).map
          (edgePhaseAtSite A site)).sum := by
  unfold phaseAtSite
  exact RTree.edgeList_node_map_sum_eq_boundary_add_internal
    (edgePhaseAtSite A site) a cs

theorem totalPhase_node_eq_boundary_add_internal
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) :
    totalPhase (RTree.node a cs) A =
      nodeBoundaryPhase a cs A + nodeInternalPhase a cs A := by
  unfold totalPhase nodeBoundaryPhase nodeInternalPhase
  calc
    (∑ site : NormalSite n (RTree.node a cs),
        phaseAtSite (RTree.node a cs) A site) =
        ∑ site : NormalSite n (RTree.node a cs),
          (((RTree.indexedChildBoundaryEdgesFrom [] 0 cs).map
            (edgePhaseAtSite A site)).sum +
            ((RTree.indexedChildInternalEdgesFrom [] 0 cs).map
              (edgePhaseAtSite A site)).sum) := by
          refine Finset.sum_congr rfl ?_
          intro site _
          exact phaseAtSite_node_eq_boundary_add_internal a cs A site
    _ =
        (∑ site : NormalSite n (RTree.node a cs),
          ((RTree.indexedChildBoundaryEdgesFrom [] 0 cs).map
            (edgePhaseAtSite A site)).sum) +
          ∑ site : NormalSite n (RTree.node a cs),
            ((RTree.indexedChildInternalEdgesFrom [] 0 cs).map
              (edgePhaseAtSite A site)).sum := by
          rw [Finset.sum_add_distrib]

noncomputable def weight {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignment n T) : ℤ :=
  bitSign (totalPhase T A)

noncomputable def signedSum (n : Nat) [NeZero n] (T : RTree) : ℤ :=
  ∑ A : NormalAssignment n T, weight T A

theorem weight_node_eq_boundary_mul_internal
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) :
    weight (RTree.node a cs) A =
      bitSign (nodeBoundaryPhase a cs A) *
        bitSign (nodeInternalPhase a cs A) := by
  unfold weight
  rw [totalPhase_node_eq_boundary_add_internal]
  exact bitSign_add _ _

noncomputable def boundaryInternalIntegrand
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) : ℤ :=
  bitSign (nodeBoundaryPhase a cs A) *
    bitSign (nodeInternalPhase a cs A)

theorem boundaryInternalIntegrand_eq_product_childContributions
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) :
    boundaryInternalIntegrand a cs A =
      ∏ i : ChildIdx cs, childBoundaryInternalContributionAt a cs i A := by
  classical
  calc
    boundaryInternalIntegrand a cs A =
        bitSign (nodeBoundaryPhase a cs A + nodeInternalPhase a cs A) := by
          unfold boundaryInternalIntegrand
          exact (bitSign_add _ _).symm
    _ = bitSign (∑ i : ChildIdx cs, childLocalPhaseAt a cs i A) := by
          rw [nodeBoundary_add_internal_eq_sum_childLocalPhaseAt]
    _ = ∏ i : ChildIdx cs, bitSign (childLocalPhaseAt a cs i A) := by
          exact (prod_bitSign_eq_bitSign_sum Finset.univ
            (fun i : ChildIdx cs => childLocalPhaseAt a cs i A)).symm
    _ = ∏ i : ChildIdx cs,
          childBoundaryInternalContributionAt a cs i A := by
          refine Finset.prod_congr rfl ?_
          intro i _
          exact
            (childBoundaryInternalContributionAt_eq_bitSign_localPhase
              a cs i A).symm

noncomputable def assembleNodeAssignment
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : NodeRootFieldAssignment n a cs)
    (N : NodeNonRootFieldAssignment n a cs) :
    NormalAssignment n (RTree.node a cs) where
  rootField := R
  nodeField := N

@[simp] theorem assembleNodeAssignment_rootField
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : NodeRootFieldAssignment n a cs)
    (N : NodeNonRootFieldAssignment n a cs) :
    (assembleNodeAssignment (a := a) (cs := cs) R N).rootField = R := rfl

@[simp] theorem assembleNodeAssignment_nodeField
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : NodeRootFieldAssignment n a cs)
    (N : NodeNonRootFieldAssignment n a cs) :
    (assembleNodeAssignment (a := a) (cs := cs) R N).nodeField = N := rfl

theorem ketAtVertex_childVertexAtInNode_childDataFamilyWithAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : NodeRootFieldAssignment n a cs)
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs)
    (site : NormalSite n (RTree.node a cs))
    (v : Vertex (childAt cs i)) :
    ketAtVertex
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H))
      site (childVertexAtInNode (a := a) i v) =
    ketAtVertex
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs)
          (childDataFamilyWithAt (n := n) (a := a) (cs := cs) i (H i))))
      site (childVertexAtInNode (a := a) i v) := by
  by_cases hroot : v.1 = []
  · have hv : v = Vertex.root (childAt cs i) := by
      apply Subtype.ext
      exact hroot
    subst v
    unfold childVertexAtInNode
    rw [ketAtVertex_childRootInNode (a := a)
        (idx := i.1) (cs := cs) (C := childAt cs i)
        (childAt_get?_eq_some cs i),
      ketAtVertex_childRootInNode (a := a)
        (idx := i.1) (cs := cs) (C := childAt cs i)
        (childAt_get?_eq_some cs i)]
    simp
  · let u : NonRootVertex (childAt cs i) := ⟨v, hroot⟩
    change ketAtVertex
      (assembleNodeAssignment R (nodeFieldFromChildDataFamily H)) site
        (childVertexAtInNode i u.1) =
      ketAtVertex
        (assembleNodeAssignment R
          (nodeFieldFromChildDataFamily (childDataFamilyWithAt i (H i))))
        site (childVertexAtInNode i u.1)
    unfold childVertexAtInNode
    rw [ketAtVertex_childNonRootInNode (a := a)
        (idx := i.1) (cs := cs) (C := childAt cs i)
        (childAt_get?_eq_some cs i),
      ketAtVertex_childNonRootInNode (a := a)
        (idx := i.1) (cs := cs) (C := childAt cs i)
        (childAt_get?_eq_some cs i)]
    simp

theorem braAtVertex_childVertexAtInNode_childDataFamilyWithAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : NodeRootFieldAssignment n a cs)
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs)
    (site : NormalSite n (RTree.node a cs))
    (v : Vertex (childAt cs i)) :
    braAtVertex
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H))
      site (childVertexAtInNode (a := a) i v) =
    braAtVertex
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs)
          (childDataFamilyWithAt (n := n) (a := a) (cs := cs) i (H i))))
      site (childVertexAtInNode (a := a) i v) := by
  by_cases hroot : v.1 = []
  · have hv : v = Vertex.root (childAt cs i) := by
      apply Subtype.ext
      exact hroot
    subst v
    unfold childVertexAtInNode
    rw [braAtVertex_childRootInNode (a := a)
        (idx := i.1) (cs := cs) (C := childAt cs i)
        (childAt_get?_eq_some cs i),
      braAtVertex_childRootInNode (a := a)
        (idx := i.1) (cs := cs) (C := childAt cs i)
        (childAt_get?_eq_some cs i)]
    simp
  · let u : NonRootVertex (childAt cs i) := ⟨v, hroot⟩
    change braAtVertex
      (assembleNodeAssignment R (nodeFieldFromChildDataFamily H)) site
        (childVertexAtInNode i u.1) =
      braAtVertex
        (assembleNodeAssignment R
          (nodeFieldFromChildDataFamily (childDataFamilyWithAt i (H i))))
        site (childVertexAtInNode i u.1)
    unfold childVertexAtInNode
    rw [braAtVertex_childNonRootInNode (a := a)
        (idx := i.1) (cs := cs) (C := childAt cs i)
        (childAt_get?_eq_some cs i),
      braAtVertex_childNonRootInNode (a := a)
        (idx := i.1) (cs := cs) (C := childAt cs i)
        (childAt_get?_eq_some cs i)]
    simp

theorem edgePhaseAtSite_prefixEdge_childAt_childDataFamilyWithAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : NodeRootFieldAssignment n a cs)
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs)
    (site : NormalSite n (RTree.node a cs))
    {e : List Nat × List Nat}
    (he : e ∈ RTree.edgeList (childAt cs i)) :
    edgePhaseAtSite
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H))
      site (RTree.prefixEdge [i.1] e) =
    edgePhaseAtSite
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs)
          (childDataFamilyWithAt (n := n) (a := a) (cs := cs) i (H i))))
      site (RTree.prefixEdge [i.1] e) := by
  rw [edgePhaseAtSite_prefixEdge_childAt (a := a) (cs := cs) i
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H))
      site he,
    edgePhaseAtSite_prefixEdge_childAt (a := a) (cs := cs) i
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs)
          (childDataFamilyWithAt (n := n) (a := a) (cs := cs) i (H i))))
      site he]
  let u : Vertex (childAt cs i) :=
    ⟨e.1, RTree.edgeList_edge_left_mem_addresses (childAt cs i) he⟩
  let v : Vertex (childAt cs i) :=
    ⟨e.2, RTree.edgeList_edge_right_mem_addresses (childAt cs i) he⟩
  have hku :=
    ketAtVertex_childVertexAtInNode_childDataFamilyWithAt
      (a := a) R H i site u
  have hkv :=
    ketAtVertex_childVertexAtInNode_childDataFamilyWithAt
      (a := a) R H i site v
  have hbu :=
    braAtVertex_childVertexAtInNode_childDataFamilyWithAt
      (a := a) R H i site u
  have hbv :=
    braAtVertex_childVertexAtInNode_childDataFamilyWithAt
      (a := a) R H i site v
  simpa [u, v] using congrArg₂ HAdd.hAdd
    (congrArg₂ HMul.hMul hku hkv) (congrArg₂ HMul.hMul hbu hbv)

theorem childBoundaryPhaseAt_childDataFamilyWithAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : NodeRootFieldAssignment n a cs)
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs) :
    childBoundaryPhaseAt a cs i
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H)) =
    childBoundaryPhaseAt a cs i
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs)
          (childDataFamilyWithAt (n := n) (a := a) (cs := cs) i (H i)))) := by
  unfold childBoundaryPhaseAt indexedChildBoundaryPhaseAt edgeListPhase
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, List.nil_append, Nat.zero_add]
  refine Finset.sum_congr rfl ?_
  intro site _
  rw [edgePhaseAtSite_boundary_childRootAt,
    edgePhaseAtSite_boundary_childRootAt]
  simp

theorem childInternalPhaseAt_childDataFamilyWithAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : NodeRootFieldAssignment n a cs)
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs) :
    childInternalPhaseAt a cs i
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H)) =
    childInternalPhaseAt a cs i
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs)
          (childDataFamilyWithAt (n := n) (a := a) (cs := cs) i (H i)))) := by
  let AH :=
    assembleNodeAssignment (a := a) (cs := cs) R
      (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H)
  let AHi :=
    assembleNodeAssignment (a := a) (cs := cs) R
      (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs)
        (childDataFamilyWithAt (n := n) (a := a) (cs := cs) i (H i)))
  unfold childInternalPhaseAt indexedChildInternalPhaseAt
  simp only [List.nil_append, Nat.zero_add]
  change
    edgeListPhase (RTree.node a cs)
        (RTree.edgeListFrom [i.1] (childAt cs i)) AH =
      edgeListPhase (RTree.node a cs)
        (RTree.edgeListFrom [i.1] (childAt cs i)) AHi
  rw [edgeListPhase_edgeListFrom_eq_sum_prefixed [i.1] (childAt cs i) AH,
    edgeListPhase_edgeListFrom_eq_sum_prefixed [i.1] (childAt cs i) AHi]
  refine Finset.sum_congr rfl ?_
  intro site _
  apply congrArg List.sum
  refine List.map_congr_left ?_
  intro e he
  exact edgePhaseAtSite_prefixEdge_childAt_childDataFamilyWithAt
    (a := a) R H i site he

theorem childBoundaryInternalContributionAt_childDataFamilyWithAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : NodeRootFieldAssignment n a cs)
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs) :
    childBoundaryInternalContributionAt a cs i
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H)) =
    childBoundaryInternalContributionAt a cs i
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs)
          (childDataFamilyWithAt (n := n) (a := a) (cs := cs) i (H i)))) := by
  unfold childBoundaryInternalContributionAt
  rw [childBoundaryPhaseAt_childDataFamilyWithAt R H i,
    childInternalPhaseAt_childDataFamilyWithAt R H i]

noncomputable def childBoundaryInternalContributionGivenRootDataAt
    {n a : Nat} [NeZero n] (cs : List RTree)
    (R : NodeRootFieldAssignment n a cs)
    (i : ChildIdx cs) (h : NodeChildDataAt n a cs i) : ℤ :=
  childBoundaryInternalContributionAt a cs i
    (assembleNodeAssignment (a := a) (cs := cs) R
      (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs)
        (childDataFamilyWithAt (n := n) (a := a) (cs := cs) i h)))

theorem childBoundaryInternalContributionAt_eq_givenRootDataAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : NodeRootFieldAssignment n a cs)
    (H : NodeChildDataFamily n a cs) (i : ChildIdx cs) :
    childBoundaryInternalContributionAt a cs i
      (assembleNodeAssignment (a := a) (cs := cs) R
        (nodeFieldFromChildDataFamily (n := n) (a := a) (cs := cs) H)) =
    childBoundaryInternalContributionGivenRootDataAt
      (n := n) (a := a) cs R i (H i) :=
  childBoundaryInternalContributionAt_childDataFamilyWithAt R H i

noncomputable def nodeFieldContributionGivenRoot
    {n a : Nat} [NeZero n] (cs : List RTree)
    (R : NodeRootFieldAssignment n a cs) : ℤ :=
  ∑ N : NodeNonRootFieldAssignment n a cs,
    boundaryInternalIntegrand a cs
      (assembleNodeAssignment (a := a) (cs := cs) R N)

theorem boundaryInternal_sum_eq_sum_root_nodeFieldContribution
    {n a : Nat} [NeZero n] (cs : List RTree) :
    (∑ A : NormalAssignment n (RTree.node a cs),
      boundaryInternalIntegrand a cs A) =
      ∑ R : NodeRootFieldAssignment n a cs,
        nodeFieldContributionGivenRoot (n := n) (a := a) cs R := by
  classical
  rw [sum_normalAssignment_node_eq_sum_root_nodeFields]
  rw [Fintype.sum_prod_type]
  rfl

theorem boundaryInternal_explicit_sum_eq_sum_root_nodeFieldContribution
    {n a : Nat} [NeZero n] (cs : List RTree) :
    (∑ A : NormalAssignment n (RTree.node a cs),
      bitSign (nodeBoundaryPhase a cs A) *
        bitSign (nodeInternalPhase a cs A)) =
      ∑ R : NodeRootFieldAssignment n a cs,
        nodeFieldContributionGivenRoot (n := n) (a := a) cs R := by
  exact boundaryInternal_sum_eq_sum_root_nodeFieldContribution
    (n := n) (a := a) cs

theorem nodeFieldContributionGivenRoot_eq_sum_childVertexFields
    {n a : Nat} [NeZero n] (cs : List RTree)
    (R : NodeRootFieldAssignment n a cs) :
    nodeFieldContributionGivenRoot (n := n) (a := a) cs R =
      ∑ G : NodeChildVertexFieldAssignment n a cs,
        boundaryInternalIntegrand a cs
          (assembleNodeAssignment (a := a) (cs := cs) R
            ((nodeChildVertexFieldAssignmentEquivNodeField n a cs) G)) := by
  classical
  unfold nodeFieldContributionGivenRoot
  exact sum_nodeFieldAssignment_eq_sum_childVertexFields
    (n := n) (a := a) cs
    (fun N : NodeNonRootFieldAssignment n a cs =>
      boundaryInternalIntegrand a cs
        (assembleNodeAssignment (a := a) (cs := cs) R N))

theorem nodeFieldContributionGivenRoot_eq_sum_childRoot_nonRootFields
    {n a : Nat} [NeZero n] (cs : List RTree)
    (R : NodeRootFieldAssignment n a cs) :
    nodeFieldContributionGivenRoot (n := n) (a := a) cs R =
      ∑ P : NodeChildRootFieldAssignment n a cs ×
          NodeChildNonRootFieldAssignment n a cs,
        boundaryInternalIntegrand a cs
          (assembleNodeAssignment (a := a) (cs := cs) R
            (nodeFieldFromChildRootNonRootFields
              (n := n) (a := a) (cs := cs) P)) := by
  classical
  rw [nodeFieldContributionGivenRoot_eq_sum_childVertexFields]
  rw [sum_childVertexFields_eq_sum_childVertexKindFields]
  rw [sum_childVertexKindFields_eq_sum_root_nonRootFields]
  rfl

theorem nodeFieldContributionGivenRoot_eq_sum_childDataFamily
    {n a : Nat} [NeZero n] (cs : List RTree)
    (R : NodeRootFieldAssignment n a cs) :
    nodeFieldContributionGivenRoot (n := n) (a := a) cs R =
      ∑ H : NodeChildDataFamily n a cs,
        boundaryInternalIntegrand a cs
          (assembleNodeAssignment (a := a) (cs := cs) R
            (nodeFieldFromChildDataFamily
              (n := n) (a := a) (cs := cs) H)) := by
  classical
  rw [nodeFieldContributionGivenRoot_eq_sum_childRoot_nonRootFields]
  exact sum_root_nonRootFields_eq_sum_childDataFamily
    (n := n) (a := a) cs
    (fun P : NodeChildRootFieldAssignment n a cs ×
        NodeChildNonRootFieldAssignment n a cs =>
      boundaryInternalIntegrand a cs
        (assembleNodeAssignment (a := a) (cs := cs) R
          (nodeFieldFromChildRootNonRootFields
            (n := n) (a := a) (cs := cs) P)))

theorem nodeFieldContributionGivenRoot_eq_sum_childDataFamily_product_childContributions
    {n a : Nat} [NeZero n] (cs : List RTree)
    (R : NodeRootFieldAssignment n a cs) :
    nodeFieldContributionGivenRoot (n := n) (a := a) cs R =
      ∑ H : NodeChildDataFamily n a cs,
        ∏ i : ChildIdx cs,
          childBoundaryInternalContributionAt a cs i
            (assembleNodeAssignment (a := a) (cs := cs) R
              (nodeFieldFromChildDataFamily
                (n := n) (a := a) (cs := cs) H)) := by
  classical
  rw [nodeFieldContributionGivenRoot_eq_sum_childDataFamily]
  refine Finset.sum_congr rfl ?_
  intro H _
  exact boundaryInternalIntegrand_eq_product_childContributions a cs
    (assembleNodeAssignment (a := a) (cs := cs) R
      (nodeFieldFromChildDataFamily
        (n := n) (a := a) (cs := cs) H))

theorem nodeFieldContributionGivenRoot_eq_product_child_sums_of_integrand_product
    {n a : Nat} [NeZero n] (cs : List RTree)
    (R : NodeRootFieldAssignment n a cs)
    (g : (i : ChildIdx cs) → NodeChildDataAt n a cs i → ℤ)
    (hprod :
      ∀ H : NodeChildDataFamily n a cs,
        boundaryInternalIntegrand a cs
          (assembleNodeAssignment (a := a) (cs := cs) R
            (nodeFieldFromChildDataFamily
              (n := n) (a := a) (cs := cs) H)) =
          ∏ i : ChildIdx cs, g i (H i)) :
    nodeFieldContributionGivenRoot (n := n) (a := a) cs R =
      ∏ i : ChildIdx cs, ∑ h : NodeChildDataAt n a cs i, g i h := by
  classical
  rw [nodeFieldContributionGivenRoot_eq_sum_childDataFamily]
  calc
    (∑ H : NodeChildDataFamily n a cs,
      boundaryInternalIntegrand a cs
        (assembleNodeAssignment (a := a) (cs := cs) R
          (nodeFieldFromChildDataFamily
            (n := n) (a := a) (cs := cs) H))) =
        ∑ H : NodeChildDataFamily n a cs,
          ∏ i : ChildIdx cs, g i (H i) := by
          refine Finset.sum_congr rfl ?_
          intro H _
          exact hprod H
    _ = ∏ i : ChildIdx cs, ∑ h : NodeChildDataAt n a cs i, g i h := by
          exact sum_childDataFamily_product (n := n) (a := a) cs g

theorem nodeFieldContributionGivenRoot_eq_product_child_sums
    {n a : Nat} [NeZero n] (cs : List RTree)
    (R : NodeRootFieldAssignment n a cs) :
    nodeFieldContributionGivenRoot (n := n) (a := a) cs R =
      ∏ i : ChildIdx cs,
        ∑ h : NodeChildDataAt n a cs i,
          childBoundaryInternalContributionGivenRootDataAt
            (n := n) (a := a) cs R i h := by
  classical
  refine
    nodeFieldContributionGivenRoot_eq_product_child_sums_of_integrand_product
      (n := n) (a := a) cs R
      (fun i h =>
        childBoundaryInternalContributionGivenRootDataAt
          (n := n) (a := a) cs R i h) ?_
  intro H
  rw [boundaryInternalIntegrand_eq_product_childContributions]
  refine Finset.prod_congr rfl ?_
  intro i _
  exact childBoundaryInternalContributionAt_eq_givenRootDataAt R H i

theorem boundaryInternal_explicit_sum_eq_sum_root_childRoot_nonRootFields
    {n a : Nat} [NeZero n] (cs : List RTree) :
    (∑ A : NormalAssignment n (RTree.node a cs),
      bitSign (nodeBoundaryPhase a cs A) *
        bitSign (nodeInternalPhase a cs A)) =
      ∑ R : NodeRootFieldAssignment n a cs,
        ∑ P : NodeChildRootFieldAssignment n a cs ×
            NodeChildNonRootFieldAssignment n a cs,
          boundaryInternalIntegrand a cs
            (assembleNodeAssignment (a := a) (cs := cs) R
              (nodeFieldFromChildRootNonRootFields
                (n := n) (a := a) (cs := cs) P)) := by
  classical
  rw [boundaryInternal_explicit_sum_eq_sum_root_nodeFieldContribution]
  refine Finset.sum_congr rfl ?_
  intro R _
  exact nodeFieldContributionGivenRoot_eq_sum_childRoot_nonRootFields
    (n := n) (a := a) cs R

theorem boundaryInternal_explicit_sum_eq_sum_root_childDataFamily
    {n a : Nat} [NeZero n] (cs : List RTree) :
    (∑ A : NormalAssignment n (RTree.node a cs),
      bitSign (nodeBoundaryPhase a cs A) *
        bitSign (nodeInternalPhase a cs A)) =
      ∑ R : NodeRootFieldAssignment n a cs,
        ∑ H : NodeChildDataFamily n a cs,
          boundaryInternalIntegrand a cs
            (assembleNodeAssignment (a := a) (cs := cs) R
              (nodeFieldFromChildDataFamily
                (n := n) (a := a) (cs := cs) H)) := by
  classical
  rw [boundaryInternal_explicit_sum_eq_sum_root_nodeFieldContribution]
  refine Finset.sum_congr rfl ?_
  intro R _
  exact nodeFieldContributionGivenRoot_eq_sum_childDataFamily
    (n := n) (a := a) cs R

theorem boundaryInternal_explicit_sum_eq_sum_root_childDataFamily_product_childContributions
    {n a : Nat} [NeZero n] (cs : List RTree) :
    (∑ A : NormalAssignment n (RTree.node a cs),
      bitSign (nodeBoundaryPhase a cs A) *
        bitSign (nodeInternalPhase a cs A)) =
      ∑ R : NodeRootFieldAssignment n a cs,
        ∑ H : NodeChildDataFamily n a cs,
          ∏ i : ChildIdx cs,
            childBoundaryInternalContributionAt a cs i
              (assembleNodeAssignment (a := a) (cs := cs) R
                (nodeFieldFromChildDataFamily
                  (n := n) (a := a) (cs := cs) H)) := by
  classical
  rw [boundaryInternal_explicit_sum_eq_sum_root_nodeFieldContribution]
  refine Finset.sum_congr rfl ?_
  intro R _
  exact
    nodeFieldContributionGivenRoot_eq_sum_childDataFamily_product_childContributions
      (n := n) (a := a) cs R

theorem boundaryInternal_explicit_sum_eq_sum_root_product_child_sums_of_integrand_product
    {n a : Nat} [NeZero n] (cs : List RTree)
    (g :
      NodeRootFieldAssignment n a cs →
        (i : ChildIdx cs) → NodeChildDataAt n a cs i → ℤ)
    (hprod :
      ∀ (R : NodeRootFieldAssignment n a cs)
        (H : NodeChildDataFamily n a cs),
        boundaryInternalIntegrand a cs
          (assembleNodeAssignment (a := a) (cs := cs) R
            (nodeFieldFromChildDataFamily
              (n := n) (a := a) (cs := cs) H)) =
          ∏ i : ChildIdx cs, g R i (H i)) :
    (∑ A : NormalAssignment n (RTree.node a cs),
      bitSign (nodeBoundaryPhase a cs A) *
        bitSign (nodeInternalPhase a cs A)) =
      ∑ R : NodeRootFieldAssignment n a cs,
        ∏ i : ChildIdx cs,
          ∑ h : NodeChildDataAt n a cs i, g R i h := by
  classical
  rw [boundaryInternal_explicit_sum_eq_sum_root_nodeFieldContribution]
  refine Finset.sum_congr rfl ?_
  intro R _
  exact
    nodeFieldContributionGivenRoot_eq_product_child_sums_of_integrand_product
      (n := n) (a := a) cs R (g R) (hprod R)

theorem boundaryInternal_explicit_sum_eq_sum_root_product_child_sums
    {n a : Nat} [NeZero n] (cs : List RTree) :
    (∑ A : NormalAssignment n (RTree.node a cs),
      bitSign (nodeBoundaryPhase a cs A) *
        bitSign (nodeInternalPhase a cs A)) =
      ∑ R : NodeRootFieldAssignment n a cs,
        ∏ i : ChildIdx cs,
          ∑ h : NodeChildDataAt n a cs i,
            childBoundaryInternalContributionGivenRootDataAt
              (n := n) (a := a) cs R i h := by
  classical
  rw [boundaryInternal_explicit_sum_eq_sum_root_nodeFieldContribution]
  refine Finset.sum_congr rfl ?_
  intro R _
  exact nodeFieldContributionGivenRoot_eq_product_child_sums
    (n := n) (a := a) cs R

theorem signedSum_node_eq_boundary_mul_internal_sum
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree) :
    signedSum n (RTree.node a cs) =
      ∑ A : NormalAssignment n (RTree.node a cs),
        bitSign (nodeBoundaryPhase a cs A) *
          bitSign (nodeInternalPhase a cs A) := by
  unfold signedSum
  refine Finset.sum_congr rfl ?_
  intro A _
  exact weight_node_eq_boundary_mul_internal a cs A

theorem nodeBoundaryPhase_eq_indexedChildBoundaryPhase
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) :
    nodeBoundaryPhase a cs A =
      indexedChildBoundaryPhase (RTree.node a cs) [] 0 cs A := by
  rfl

theorem nodeBoundaryPhase_cons
    {n : Nat} [NeZero n] (a : Nat) (C : RTree) (rest : List RTree)
    (A : NormalAssignment n (RTree.node a (C :: rest))) :
    nodeBoundaryPhase a (C :: rest) A =
      edgeListPhase (RTree.node a (C :: rest)) [([], [0])] A +
        indexedChildBoundaryPhase (RTree.node a (C :: rest)) [] 1 rest A := by
  unfold nodeBoundaryPhase indexedChildBoundaryPhase
  change
    edgeListPhase (RTree.node a (C :: rest))
      ([([], [0])] ++ RTree.indexedChildBoundaryEdgesFrom [] 1 rest) A =
      edgeListPhase (RTree.node a (C :: rest)) [([], [0])] A +
        edgeListPhase (RTree.node a (C :: rest))
          (RTree.indexedChildBoundaryEdgesFrom [] 1 rest) A
  exact edgeListPhase_append (RTree.node a (C :: rest))
    [([], [0])] (RTree.indexedChildBoundaryEdgesFrom [] 1 rest) A

theorem nodeBoundaryPhase_cons_head_expanded
    {n : Nat} [NeZero n] (a : Nat) (C : RTree) (rest : List RTree)
    (A : NormalAssignment n (RTree.node a (C :: rest))) :
    nodeBoundaryPhase a (C :: rest) A =
      (∑ site : NormalSite n (RTree.node a (C :: rest)),
        (A.rootField site.nonRootCoord *
          A.nodeField
            (childRootAsNonRootInNode
              (a := a) (idx := 0) (cs := C :: rest) (C := C) rfl)
            (nonRootDomainOfSite site
              (childRootAsNonRootInNode
                (a := a) (idx := 0) (cs := C :: rest) (C := C) rfl) 0) +
        A.rootField site.nonRootCoord *
          A.nodeField
            (childRootAsNonRootInNode
              (a := a) (idx := 0) (cs := C :: rest) (C := C) rfl)
            (nonRootDomainOfSite site
              (childRootAsNonRootInNode
                (a := a) (idx := 0) (cs := C :: rest) (C := C) rfl) 1))) +
        indexedChildBoundaryPhase (RTree.node a (C :: rest)) [] 1 rest A := by
  rw [nodeBoundaryPhase_cons]
  simp [edgePhaseAtSite_boundary_childRoot_of_get?]

theorem nodeInternalPhase_eq_indexedChildInternalPhase
    {n : Nat} [NeZero n] (a : Nat) (cs : List RTree)
    (A : NormalAssignment n (RTree.node a cs)) :
    nodeInternalPhase a cs A =
      indexedChildInternalPhase (RTree.node a cs) [] 0 cs A := by
  rfl

theorem nodeInternalPhase_cons
    {n : Nat} [NeZero n] (a : Nat) (C : RTree) (rest : List RTree)
    (A : NormalAssignment n (RTree.node a (C :: rest))) :
    nodeInternalPhase a (C :: rest) A =
      edgeListPhase (RTree.node a (C :: rest)) (RTree.edgeListFrom [0] C) A +
        edgeListPhase (RTree.node a (C :: rest))
          (RTree.indexedChildInternalEdgesFrom [] 1 rest) A := by
  unfold nodeInternalPhase
  change
    edgeListPhase (RTree.node a (C :: rest))
      (RTree.edgeListFrom [0] C ++
        RTree.indexedChildInternalEdgesFrom [] 1 rest) A =
      edgeListPhase (RTree.node a (C :: rest)) (RTree.edgeListFrom [0] C) A +
        edgeListPhase (RTree.node a (C :: rest))
          (RTree.indexedChildInternalEdgesFrom [] 1 rest) A
  exact edgeListPhase_append (RTree.node a (C :: rest))
    (RTree.edgeListFrom [0] C)
    (RTree.indexedChildInternalEdgesFrom [] 1 rest) A

theorem nodeInternalPhase_cons_eq_head_sum_prefixed_add_tail
    {n : Nat} [NeZero n] (a : Nat) (C : RTree) (rest : List RTree)
    (A : NormalAssignment n (RTree.node a (C :: rest))) :
    nodeInternalPhase a (C :: rest) A =
      (∑ site : NormalSite n (RTree.node a (C :: rest)),
        ((RTree.edgeList C).map
          (fun e => edgePhaseAtSite A site (RTree.prefixEdge [0] e))).sum) +
        edgeListPhase (RTree.node a (C :: rest))
          (RTree.indexedChildInternalEdgesFrom [] 1 rest) A := by
  rw [nodeInternalPhase_cons]
  rw [edgeListPhase_edgeListFrom_eq_sum_prefixed]

theorem nodeInternalPhase_single_child_eq_prefixed_child
    {n : Nat} [NeZero n] (a : Nat) (C : RTree)
    (A : NormalAssignment n (RTree.node a [C])) :
    nodeInternalPhase a [C] A =
      edgeListPhase (RTree.node a [C])
        ((RTree.edgeList C).map (RTree.prefixEdge [0])) A := by
  rw [nodeInternalPhase_cons]
  simp [edgeListPhase_edgeListFrom_eq_prefix]

theorem nodeInternalPhase_single_child_eq_sum_prefixed
    {n : Nat} [NeZero n] (a : Nat) (C : RTree)
    (A : NormalAssignment n (RTree.node a [C])) :
    nodeInternalPhase a [C] A =
      ∑ site : NormalSite n (RTree.node a [C]),
        ((RTree.edgeList C).map
          (fun e => edgePhaseAtSite A site (RTree.prefixEdge [0] e))).sum := by
  rw [nodeInternalPhase_single_child_eq_prefixed_child]
  exact edgeListPhase_map_prefix_eq_sum_prefixed [0] C A

@[simp] theorem ketAtVertex_root {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) (site : NormalSite n T) :
    ketAtVertex A site (Vertex.root T) = A.rootField site.nonRootCoord := by
  simp [ketAtVertex, Vertex.root]

@[simp] theorem braAtVertex_root {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) (site : NormalSite n T) :
    braAtVertex A site (Vertex.root T) = A.rootField site.nonRootCoord := by
  simp [braAtVertex, Vertex.root]

@[simp] theorem phaseAtSite_leaf {n a : Nat} [NeZero n]
    (A : NormalAssignment n (RTree.node a []))
    (site : NormalSite n (RTree.node a [])) :
    phaseAtSite (RTree.node a []) A site = 0 := by
  simp [phaseAtSite]

@[simp] theorem totalPhase_leaf {n a : Nat} [NeZero n]
    (A : NormalAssignment n (RTree.node a [])) :
    totalPhase (RTree.node a []) A = 0 := by
  simp [totalPhase]

private theorem nonRootVertex_leaf_false {a : Nat}
    (v : NonRootVertex (RTree.node a [])) : False := by
  have haddr : v.1.1 ∈ RTree.addresses (RTree.node a []) := v.1.2
  have hroot : v.1.1 = [] := by
    simpa only [RTree.addresses_node_nil, List.mem_singleton] using haddr
  exact v.2 hroot

noncomputable def emptyRootFieldDomainLeaf (n a : Nat) [NeZero n] :
    RootFieldDomain n (RTree.node a []) :=
  fun v => False.elim (nonRootVertex_leaf_false v)

noncomputable def normalAssignmentLeafEquiv (n a : Nat) [NeZero n] :
    NormalAssignment n (RTree.node a []) ≃ F2 where
  toFun A := A.rootField (emptyRootFieldDomainLeaf n a)
  invFun b :=
    { rootField := fun _ => b
      nodeField := fun v => False.elim (nonRootVertex_leaf_false v) }
  left_inv A := by
    cases A with
    | mk rootField nodeField =>
        change
          NormalAssignment.mk (fun _ => rootField (emptyRootFieldDomainLeaf n a))
              (fun v => False.elim (nonRootVertex_leaf_false v)) =
            NormalAssignment.mk rootField nodeField
        rw [NormalAssignment.mk.injEq]
        constructor
        · funext rd
          have hrd : rd = emptyRootFieldDomainLeaf n a := by
            funext v
            exact False.elim (nonRootVertex_leaf_false v)
          rw [hrd]
        · funext v dom
          exact False.elim (nonRootVertex_leaf_false v)
  right_inv b := rfl

theorem card_normalAssignment_leaf (n a : Nat) [NeZero n] :
    Fintype.card (NormalAssignment n (RTree.node a [])) = 2 := by
  classical
  calc
    Fintype.card (NormalAssignment n (RTree.node a [])) =
        Fintype.card F2 :=
      Fintype.card_congr (normalAssignmentLeafEquiv n a)
    _ = 2 := by simp [F2]

theorem signedSum_leaf (n a : Nat) [NeZero n] :
    signedSum n (RTree.node a []) = 2 := by
  classical
  calc
    signedSum n (RTree.node a []) =
        ∑ _A : NormalAssignment n (RTree.node a []), (1 : ℤ) := by
          refine Finset.sum_congr rfl ?_
          intro A _
          simp [weight]
    _ = 2 := by
          simp [card_normalAssignment_leaf n a]

theorem signedSum_leaf_eq_DeltaTreeModel (n a : Nat) [NeZero n] :
    signedSum n (RTree.node a []) =
      DeltaTreeModel n (RTree.node a []) := by
  rw [signedSum_leaf]
  simp [DeltaTreeModel, Xassign]

end RawNormal

end TreeGraph
