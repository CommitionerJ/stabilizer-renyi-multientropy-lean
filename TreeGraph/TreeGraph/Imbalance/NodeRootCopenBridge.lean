import TreeGraph.Imbalance.NodePackageMembership
import TreeGraph.Addresses

namespace TreeGraph
namespace Imbalance

abbrev NodeChildVertex (cs : List RTree) :=
  Sigma fun i : ChildIdx cs => Vertex (childAt cs i)

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

def childVertexAtAsNonRootInNode
    {a : Nat} {cs : List RTree}
    (p : NodeChildVertex cs) :
    NonRootVertex (RTree.node a cs) :=
  ⟨childVertexAtInNode (a := a) p.1 p.2, by
    simp [childVertexAtInNode, childVertexInNode]⟩

@[simp] theorem childVertexInNode_addr
    {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) (v : Vertex C) :
    (childVertexInNode (a := a) hget v).1 = idx :: v.1 :=
  rfl

@[simp] theorem childVertexAtInNode_addr
    {a : Nat} {cs : List RTree}
    (i : ChildIdx cs) (v : Vertex (childAt cs i)) :
    (childVertexAtInNode (a := a) i v).1 = i.1 :: v.1 :=
  rfl

@[simp] theorem childVertexAtAsNonRootInNode_addr
    {a : Nat} {cs : List RTree}
    (p : NodeChildVertex cs) :
    (childVertexAtAsNonRootInNode (a := a) p).1.1 =
      p.1.1 :: p.2.1 :=
  rfl

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

theorem childVertexAtAsNonRootInNode_weight
    {a : Nat} {cs : List RTree}
    (p : NodeChildVertex cs) :
    NonRootVertex.weight (childVertexAtAsNonRootInNode (a := a) p) =
      Vertex.weight p.2 := by
  change Vertex.weight (childVertexAtInNode (a := a) p.1 p.2) =
    Vertex.weight p.2
  exact childVertexAtInNode_weight p.1 p.2

theorem nonRootVertex_node_exists_nodeChildVertex
    {a : Nat} {cs : List RTree}
    (v : NonRootVertex (RTree.node a cs)) :
    ∃ p : NodeChildVertex cs,
      v.1 = childVertexAtInNode (a := a) p.1 p.2 := by
  rcases RTree.nonroot_address_mem_node_exists_childAt
      (a := a) (cs := cs) (p := v.1.1) v.1.2 v.2 with
    ⟨i, q, hp_eq, hq⟩
  refine ⟨⟨i, ⟨q, hq⟩⟩, ?_⟩
  apply Subtype.ext
  simpa [childVertexAtInNode, childVertexInNode] using hp_eq

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
          have hhead : i.1 = j.1 := (List.cons.inj haddr).1
          have htail : u.1 = v.1 := (List.cons.inj haddr).2
          have hij : i = j := Fin.ext hhead
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

theorem nonRootVertexNodeEquivChildVertex_weight
    {a : Nat} {cs : List RTree}
    (v : NonRootVertex (RTree.node a cs)) :
    NonRootVertex.weight v =
      Vertex.weight ((nonRootVertexNodeEquivChildVertex a cs v).2) := by
  let p := nonRootVertexNodeEquivChildVertex a cs v
  have hp :
      v = childVertexAtAsNonRootInNode (a := a) p := by
    exact ((nonRootVertexNodeEquivChildVertex a cs).left_inv v).symm
  calc
    NonRootVertex.weight v =
        NonRootVertex.weight (childVertexAtAsNonRootInNode (a := a) p) := by
      rw [hp]
    _ = Vertex.weight p.2 := childVertexAtAsNonRootInNode_weight p

def finCastEquivOfEqClean {m k : Nat} (h : m = k) : Fin m ≃ Fin k where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv j := by
    subst h
    rfl
  right_inv j := by
    subst h
    rfl

noncomputable def rootFieldDomainCleanEquivNodeChildVertex
    (n a : Nat) [NeZero n] (cs : List RTree) :
    RootFieldDomainClean n (RTree.node a cs) ≃
      ((p : NodeChildVertex cs) → Fin (Vertex.weight p.2) → Rep n) :=
  (Equiv.piCongrRight (fun v : NonRootVertex (RTree.node a cs) =>
    Equiv.arrowCongr
      (finCastEquivOfEqClean
        (nonRootVertexNodeEquivChildVertex_weight
          (a := a) (cs := cs) v))
      (Equiv.refl (Rep n)))).trans
    (Equiv.piCongrLeft
      (fun p : NodeChildVertex cs => Fin (Vertex.weight p.2) → Rep n)
      (nonRootVertexNodeEquivChildVertex a cs))

end Imbalance
end TreeGraph
