import TreeGraph.RTree

namespace TreeGraph

abbrev ChildIdx (cs : List RTree) := Fin cs.length

def childAt (cs : List RTree) (i : ChildIdx cs) : RTree :=
  cs.get i

theorem childAt_mem (cs : List RTree) (i : ChildIdx cs) :
    childAt cs i ∈ cs :=
  List.get_mem cs i

@[simp] theorem childAt_get?_eq_some (cs : List RTree) (i : ChildIdx cs) :
    cs[i.1]? = some (childAt cs i) := by
  rw [List.getElem?_eq_getElem i.2]
  simp [childAt, List.get_eq_getElem]

@[simp] theorem childAt_cons_zero (C : RTree) (cs : List RTree) :
    childAt (C :: cs) (0 : Fin (C :: cs).length) = C := by
  simp [childAt, List.get_eq_getElem]

@[simp] theorem childAt_cons_succ
    (C : RTree) (cs : List RTree) (i : ChildIdx cs) :
    childAt (C :: cs) i.succ = childAt cs i := by
  simp [childAt, List.get_eq_getElem]

namespace RTree

mutual
  private def addressesChildren : Nat → List RTree → List (List Nat)
    | _, [] => []
    | i, C :: rest =>
        (addresses C).map (fun p => i :: p) ++ addressesChildren (i + 1) rest

  def addresses : RTree → List (List Nat)
    | node _ cs => [] :: addressesChildren 0 cs
end

mutual
  private def edgeListChildren : List Nat → Nat → List RTree → List (List Nat × List Nat)
    | _, _, [] => []
    | parent, i, C :: rest =>
        let child := parent ++ [i]
        (parent, child) :: edgeListFrom child C ++ edgeListChildren parent (i + 1) rest

  def edgeListFrom (parent : List Nat) : RTree → List (List Nat × List Nat)
    | node _ cs => edgeListChildren parent 0 cs
end

def edgeList (T : RTree) : List (List Nat × List Nat) :=
  edgeListFrom [] T

def prefixEdge (parent : List Nat) (e : List Nat × List Nat) :
    List Nat × List Nat :=
  (parent ++ e.1, parent ++ e.2)

@[simp] theorem prefixEdge_nil (e : List Nat × List Nat) :
    prefixEdge [] e = e := by
  cases e
  simp [prefixEdge]

@[simp] theorem prefixEdge_comp
    (parent q : List Nat) (e : List Nat × List Nat) :
    prefixEdge parent (prefixEdge q e) =
      prefixEdge (parent ++ q) e := by
  cases e
  simp [prefixEdge, List.append_assoc]

def indexedChildEdgeListFrom (parent : List Nat) :
    Nat → List RTree → List (List Nat × List Nat)
  | _, [] => []
  | i, C :: rest =>
      let child := parent ++ [i]
      (parent, child) :: edgeListFrom child C ++
        indexedChildEdgeListFrom parent (i + 1) rest

def indexedChildBoundaryEdgesFrom (parent : List Nat) :
    Nat → List RTree → List (List Nat × List Nat)
  | _, [] => []
  | i, _ :: rest =>
      (parent, parent ++ [i]) ::
        indexedChildBoundaryEdgesFrom parent (i + 1) rest

def indexedChildInternalEdgesFrom (parent : List Nat) :
    Nat → List RTree → List (List Nat × List Nat)
  | _, [] => []
  | i, C :: rest =>
      edgeListFrom (parent ++ [i]) C ++
        indexedChildInternalEdgesFrom parent (i + 1) rest

private theorem edgeListChildren_eq_indexedChildEdgeListFrom
    (parent : List Nat) :
    ∀ (start : Nat) (cs : List RTree),
      edgeListChildren parent start cs =
        indexedChildEdgeListFrom parent start cs
  | _, [] => rfl
  | start, C :: rest => by
      simp [edgeListChildren, indexedChildEdgeListFrom,
        edgeListChildren_eq_indexedChildEdgeListFrom parent (start + 1) rest]

@[simp] theorem edgeListFrom_node
    (parent : List Nat) (a : Nat) (cs : List RTree) :
    edgeListFrom parent (node a cs) =
      indexedChildEdgeListFrom parent 0 cs := by
  exact edgeListChildren_eq_indexedChildEdgeListFrom parent 0 cs

@[simp] theorem indexedChildEdgeListFrom_nil
    (parent : List Nat) (start : Nat) :
    indexedChildEdgeListFrom parent start [] = [] := rfl

@[simp] theorem indexedChildEdgeListFrom_cons
    (parent : List Nat) (start : Nat) (C : RTree) (rest : List RTree) :
    indexedChildEdgeListFrom parent start (C :: rest) =
      let child := parent ++ [start]
      (parent, child) :: edgeListFrom child C ++
        indexedChildEdgeListFrom parent (start + 1) rest := rfl

@[simp] theorem indexedChildBoundaryEdgesFrom_nil
    (parent : List Nat) (start : Nat) :
    indexedChildBoundaryEdgesFrom parent start [] = [] := rfl

@[simp] theorem indexedChildBoundaryEdgesFrom_cons
    (parent : List Nat) (start : Nat) (C : RTree) (rest : List RTree) :
    indexedChildBoundaryEdgesFrom parent start (C :: rest) =
      (parent, parent ++ [start]) ::
        indexedChildBoundaryEdgesFrom parent (start + 1) rest := rfl

theorem indexedChildBoundaryEdgesFrom_map_sum_eq_sum_fin
    {M : Type} [AddCommMonoid M]
    (f : List Nat × List Nat → M)
    (parent : List Nat) (start : Nat) :
    ∀ cs : List RTree,
      ((indexedChildBoundaryEdgesFrom parent start cs).map f).sum =
        ∑ j : Fin cs.length, f (parent, parent ++ [start + j.1])
  | [] => by
      simp
  | C :: rest => by
      have ih :=
        indexedChildBoundaryEdgesFrom_map_sum_eq_sum_fin
          f parent (start + 1) rest
      simp only [indexedChildBoundaryEdgesFrom_cons, List.map_cons,
        List.sum_cons, List.length_cons]
      calc
        f (parent, parent ++ [start]) +
            ((indexedChildBoundaryEdgesFrom parent (start + 1) rest).map f).sum =
          f (parent, parent ++ [start]) +
            ∑ j : Fin rest.length,
              f (parent, parent ++ [start + 1 + j.1]) := by
              rw [ih]
        _ =
          ∑ j : Fin (rest.length + 1),
            f (parent, parent ++ [start + j.1]) := by
              rw [Fin.sum_univ_succ]
              simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem indexedChildInternalEdgesFrom_nil
    (parent : List Nat) (start : Nat) :
    indexedChildInternalEdgesFrom parent start [] = [] := rfl

@[simp] theorem indexedChildInternalEdgesFrom_cons
    (parent : List Nat) (start : Nat) (C : RTree) (rest : List RTree) :
    indexedChildInternalEdgesFrom parent start (C :: rest) =
      edgeListFrom (parent ++ [start]) C ++
        indexedChildInternalEdgesFrom parent (start + 1) rest := rfl

theorem indexedChildInternalEdgesFrom_map_sum_eq_sum_fin
    {M : Type} [AddCommMonoid M]
    (f : List Nat × List Nat → M)
    (parent : List Nat) (start : Nat) :
    ∀ cs : List RTree,
      ((indexedChildInternalEdgesFrom parent start cs).map f).sum =
        ∑ j : Fin cs.length,
          ((edgeListFrom (parent ++ [start + j.1]) (childAt cs j)).map f).sum
  | [] => by
      simp
  | C :: rest => by
      have ih :=
        indexedChildInternalEdgesFrom_map_sum_eq_sum_fin
          f parent (start + 1) rest
      simp only [indexedChildInternalEdgesFrom_cons, List.map_append,
        List.sum_append, List.length_cons]
      calc
        ((edgeListFrom (parent ++ [start]) C).map f).sum +
            ((indexedChildInternalEdgesFrom parent (start + 1) rest).map f).sum =
          ((edgeListFrom (parent ++ [start]) C).map f).sum +
            ∑ j : Fin rest.length,
              ((edgeListFrom (parent ++ [start + 1 + j.1])
                (childAt rest j)).map f).sum := by
              rw [ih]
        _ =
          ∑ j : Fin (rest.length + 1),
            ((edgeListFrom (parent ++ [start + j.1])
              (childAt (C :: rest) j)).map f).sum := by
              rw [Fin.sum_univ_succ]
              simp [childAt, List.get_eq_getElem, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm]

theorem indexedChildEdgeListFrom_map_sum_eq_boundary_add_internal
    {M : Type} [AddCommMonoid M]
    (f : List Nat × List Nat → M) :
    ∀ (parent : List Nat) (start : Nat) (cs : List RTree),
      ((indexedChildEdgeListFrom parent start cs).map f).sum =
        ((indexedChildBoundaryEdgesFrom parent start cs).map f).sum +
          ((indexedChildInternalEdgesFrom parent start cs).map f).sum
  | parent, start, [] => by
      simp
  | parent, start, C :: rest => by
      have ih :=
        indexedChildEdgeListFrom_map_sum_eq_boundary_add_internal
          f parent (start + 1) rest
      simp [ih, add_assoc, add_left_comm]

theorem edgeListFrom_node_map_sum_eq_boundary_add_internal
    {M : Type} [AddCommMonoid M]
    (f : List Nat × List Nat → M)
    (parent : List Nat) (a : Nat) (cs : List RTree) :
    ((edgeListFrom parent (node a cs)).map f).sum =
      ((indexedChildBoundaryEdgesFrom parent 0 cs).map f).sum +
        ((indexedChildInternalEdgesFrom parent 0 cs).map f).sum := by
  rw [edgeListFrom_node]
  exact indexedChildEdgeListFrom_map_sum_eq_boundary_add_internal
    f parent 0 cs

theorem edgeList_node_map_sum_eq_boundary_add_internal
    {M : Type} [AddCommMonoid M]
    (f : List Nat × List Nat → M) (a : Nat) (cs : List RTree) :
    ((edgeList (node a cs)).map f).sum =
      ((indexedChildBoundaryEdgesFrom [] 0 cs).map f).sum +
        ((indexedChildInternalEdgesFrom [] 0 cs).map f).sum := by
  change
    ((edgeListFrom [] (node a cs)).map f).sum =
      ((indexedChildBoundaryEdgesFrom [] 0 cs).map f).sum +
        ((indexedChildInternalEdgesFrom [] 0 cs).map f).sum
  exact edgeListFrom_node_map_sum_eq_boundary_add_internal f [] a cs

@[simp] theorem numVertices_pos (T : RTree) : 0 < RTree.numVertices T := by
  cases T with
  | node a cs =>
      simp [RTree.numVertices]

mutual
  theorem edgeListFrom_append_parent
      (parent q : List Nat) (T : RTree) :
      edgeListFrom (parent ++ q) T =
        (edgeListFrom q T).map (prefixEdge parent) := by
    cases T with
    | node a cs =>
        rw [edgeListFrom_node, edgeListFrom_node]
        exact indexedChildEdgeListFrom_append_parent parent q 0 cs

  theorem indexedChildEdgeListFrom_append_parent
      (parent q : List Nat) (start : Nat) (cs : List RTree) :
      indexedChildEdgeListFrom (parent ++ q) start cs =
        (indexedChildEdgeListFrom q start cs).map (prefixEdge parent) := by
    cases cs with
    | nil =>
        simp
    | cons C rest =>
        have hC := edgeListFrom_append_parent parent (q ++ [start]) C
        have hrest :=
          indexedChildEdgeListFrom_append_parent parent q (start + 1) rest
        simp [indexedChildEdgeListFrom, hC, hrest, List.map_append,
          prefixEdge, List.append_assoc]
end

theorem edgeListFrom_eq_edgeList_map_prefix
    (parent : List Nat) (T : RTree) :
    edgeListFrom parent T =
      (edgeList T).map (prefixEdge parent) := by
  simpa [edgeList] using
    edgeListFrom_append_parent parent [] T

mutual
  theorem edgeList_edge_mem_addresses
      (T : RTree) {e : List Nat × List Nat}
      (he : e ∈ edgeList T) :
      e.1 ∈ addresses T ∧ e.2 ∈ addresses T := by
    cases T with
    | node a cs =>
        unfold edgeList at he
        rw [edgeListFrom_node] at he
        simpa [addresses] using
          indexedChildEdgeListFrom_edge_mem_addressesChildren 0 cs he

  private theorem indexedChildEdgeListFrom_edge_mem_addressesChildren
      (start : Nat) :
      ∀ (cs : List RTree) {e : List Nat × List Nat},
        e ∈ indexedChildEdgeListFrom [] start cs →
          e.1 ∈ [] :: addressesChildren start cs ∧
            e.2 ∈ [] :: addressesChildren start cs
    | [], e, he => by
        simp at he
    | C :: rest, e, he => by
        simp [indexedChildEdgeListFrom] at he
        rcases he with he | he | he
        · subst e
          have hroot : [] ∈ addresses C := by
            cases C
            simp [addresses]
          constructor
          · simp
          · simp [addressesChildren, hroot]
        · rw [edgeListFrom_eq_edgeList_map_prefix] at he
          rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
          have hend := edgeList_edge_mem_addresses C he0
          simp [prefixEdge, addressesChildren, hend.1, hend.2]
        · have htail :=
            indexedChildEdgeListFrom_edge_mem_addressesChildren
              (start + 1) rest he
          constructor
          · rcases List.mem_cons.mp htail.1 with hroot | htailLeft
            · simp [hroot]
            · simp [addressesChildren, htailLeft]
          · rcases List.mem_cons.mp htail.2 with hroot | htailRight
            · simp [hroot]
            · simp [addressesChildren, htailRight]
end

theorem edgeList_edge_left_mem_addresses
    (T : RTree) {e : List Nat × List Nat}
    (he : e ∈ edgeList T) :
    e.1 ∈ addresses T :=
  (edgeList_edge_mem_addresses T he).1

theorem edgeList_edge_right_mem_addresses
    (T : RTree) {e : List Nat × List Nat}
    (he : e ∈ edgeList T) :
    e.2 ∈ addresses T :=
  (edgeList_edge_mem_addresses T he).2

@[simp] theorem edgeList_node
    (a : Nat) (cs : List RTree) :
    edgeList (node a cs) = indexedChildEdgeListFrom [] 0 cs := by
  simp [edgeList]

def subtreeAt? : RTree → List Nat → Option RTree
  | T, [] => some T
  | node _ cs, i :: rest =>
      match cs[i]? with
      | some C => subtreeAt? C rest
      | none => none

def weightAt (T : RTree) (p : List Nat) : Nat :=
  match subtreeAt? T p with
  | some U => U.rootWeight
  | none => 0

@[simp] theorem addresses_node (a : Nat) (cs : List RTree) :
    addresses (node a cs) = [] :: addressesChildren 0 cs := rfl

@[simp] theorem addresses_node_nil (a : Nat) :
    addresses (node a []) = [[]] := rfl

@[simp] theorem addresses_node_single_leaf (a b : Nat) :
    addresses (node a [node b []]) = [[], [0]] := rfl

@[simp] theorem addresses_node_two_leaf (a b c : Nat) :
    addresses (node a [node b [], node c []]) = [[], [0], [1]] := rfl

private theorem mem_addressesChildren_of_get?_mem :
    ∀ (cs : List RTree) (start idx : Nat) (C : RTree) (p : List Nat),
      cs[idx]? = some C →
      p ∈ addresses C →
      (start + idx) :: p ∈ addressesChildren start cs
  | [], start, idx, C, p, hget, hp => by
      cases idx <;> simp at hget
  | D :: rest, start, idx, C, p, hget, hp => by
      cases idx with
      | zero =>
          simp at hget
          subst C
          simp [addressesChildren, hp]
      | succ idx =>
          have htail :
              (start + 1 + idx) :: p ∈
                addressesChildren (start + 1) rest :=
            mem_addressesChildren_of_get?_mem
              rest (start + 1) idx C p hget hp
          have haddr :
              (start + (idx + 1)) :: p =
                (start + 1 + idx) :: p := by
            simp [Nat.add_comm, Nat.add_left_comm]
          simp [addressesChildren, haddr, htail]

theorem childAddress_mem_addresses_node_of_get?
    {a idx : Nat} {cs : List RTree} {C : RTree} {p : List Nat}
    (hget : cs[idx]? = some C) (hp : p ∈ addresses C) :
    idx :: p ∈ addresses (node a cs) := by
  have hchild :
      (0 + idx) :: p ∈ addressesChildren 0 cs :=
    mem_addressesChildren_of_get?_mem cs 0 idx C p hget hp
  simpa [addresses] using hchild

theorem childRoot_mem_addresses_node_of_get?
    {a idx : Nat} {cs : List RTree} {C : RTree}
    (hget : cs[idx]? = some C) :
    [idx] ∈ addresses (node a cs) := by
  exact childAddress_mem_addresses_node_of_get?
    (a := a) (idx := idx) (cs := cs) (C := C)
    (p := []) hget (by
      cases C
      simp [addresses])

theorem subtreeAt_childAddress_of_get?
    {idx : Nat} {cs : List RTree} {C U : RTree} {p : List Nat}
    (hget : cs[idx]? = some C) (hsub : subtreeAt? C p = some U) :
    subtreeAt? (node 0 cs) (idx :: p) = some U := by
  simp [subtreeAt?, hget, hsub]

theorem subtreeAt_childAddress_node_of_get?
    {a idx : Nat} {cs : List RTree} {C U : RTree} {p : List Nat}
    (hget : cs[idx]? = some C) (hsub : subtreeAt? C p = some U) :
    subtreeAt? (node a cs) (idx :: p) = some U := by
  simp [subtreeAt?, hget, hsub]

theorem weightAt_childAddress_of_get?
    {a idx : Nat} {cs : List RTree} {C : RTree} {p : List Nat}
    (hget : cs[idx]? = some C) :
    weightAt (node a cs) (idx :: p) = weightAt C p := by
  unfold weightAt
  cases hsub : subtreeAt? C p with
  | none =>
      simp [subtreeAt?, hget, hsub]
  | some U =>
      simp [subtreeAt?, hget, hsub]

@[simp] theorem edgeList_node_nil (a : Nat) :
    edgeList (node a []) = [] := rfl

@[simp] theorem edgeList_node_single_leaf (a b : Nat) :
    edgeList (node a [node b []]) = [([], [0])] := rfl

@[simp] theorem edgeList_node_two_leaf (a b c : Nat) :
    edgeList (node a [node b [], node c []]) = [([], [0]), ([], [1])] := rfl

@[simp] theorem subtreeAt_root (T : RTree) :
    subtreeAt? T [] = some T := by
  cases T
  rfl

@[simp] theorem weightAt_root (T : RTree) :
    weightAt T [] = T.rootWeight := by
  cases T
  rfl

@[simp] theorem nil_mem_addresses (T : RTree) :
    [] ∈ addresses T := by
  cases T
  simp [addresses]

private theorem mem_addressesChildren_exists_get? :
    ∀ (cs : List RTree) (start : Nat) {p : List Nat},
      p ∈ addressesChildren start cs →
        ∃ idx C q,
          p = (start + idx) :: q
            ∧ cs[idx]? = some C
            ∧ C ∈ cs
            ∧ q ∈ addresses C
  | [], start, p, hp => by
      simp [addressesChildren] at hp
  | C :: rest, start, p, hp => by
      simp [addressesChildren] at hp
      rcases hp with hp | hp
      · rcases hp with ⟨q, hq, hpq⟩
        refine ⟨0, C, q, ?_, ?_, ?_, hq⟩
        · simpa using hpq.symm
        · simp
        · simp
      · rcases mem_addressesChildren_exists_get? rest (start + 1) hp with
          ⟨idx, D, q, hp_eq, hget, hmem, hq⟩
        refine ⟨idx + 1, D, q, ?_, ?_, ?_, hq⟩
        · rw [hp_eq]
          simp [Nat.add_comm, Nat.add_left_comm]
        · simpa using hget
        · simp [hmem]

theorem nonroot_address_mem_node_exists_childAt
    {a : Nat} {cs : List RTree} {p : List Nat}
    (hp : p ∈ addresses (node a cs)) (hne : p ≠ []) :
    ∃ i : ChildIdx cs, ∃ q : List Nat,
      p = i.1 :: q ∧ q ∈ addresses (childAt cs i) := by
  have hp' : p ∈ [] :: addressesChildren 0 cs := by
    simpa [addresses] using hp
  rcases List.mem_cons.mp hp' with hp_root | hp_child
  · exact False.elim (hne hp_root)
  · rcases mem_addressesChildren_exists_get? cs 0 hp_child with
      ⟨idx, C, q, hp_eq, hget, _hmem, hq⟩
    rcases (List.getElem?_eq_some_iff.mp hget) with ⟨hidx, hgetElem⟩
    refine ⟨⟨idx, hidx⟩, q, ?_, ?_⟩
    · simpa using hp_eq
    · have hchild : childAt cs ⟨idx, hidx⟩ = C := by
        simp [childAt, List.get_eq_getElem, hgetElem]
      simpa [hchild] using hq

theorem weightAt_positive_of_mem_addresses {T : RTree}
    (hT : RTree.PositiveWeights T) {p : List Nat} (hp : p ∈ addresses T) :
    0 < weightAt T p := by
  induction p generalizing T with
  | nil =>
      cases T with
      | node a cs =>
          have hT' : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
            simpa [RTree.PositiveWeights] using hT
          exact hT'.1
  | cons i rest ih =>
      cases T with
      | node a cs =>
          have hT' : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
            simpa [RTree.PositiveWeights] using hT
          rcases hT' with ⟨ha, hcs⟩
          have hp_child : i :: rest ∈ addressesChildren 0 cs := by
            simpa [addresses] using hp
          rcases mem_addressesChildren_exists_get? cs 0 hp_child with
            ⟨idx, C, q, hp_eq, hget, hmem, hq⟩
          simp at hp_eq
          rcases hp_eq with ⟨hidx, hqeq⟩
          subst idx
          subst q
          have hC : RTree.PositiveWeights C := hcs C hmem
          simp [weightAt, subtreeAt?, hget]
          exact ih hC hq

end RTree

abbrev Vertex (T : RTree) := { p : List Nat // p ∈ RTree.addresses T }

instance (T : RTree) : Fintype (Vertex T) :=
  inferInstanceAs (Fintype { p : List Nat // p ∈ RTree.addresses T })

instance (T : RTree) : DecidableEq (Vertex T) :=
  inferInstance

namespace Vertex

def root (T : RTree) : Vertex T :=
  ⟨[], RTree.nil_mem_addresses T⟩

def isRoot {T : RTree} (v : Vertex T) : Prop :=
  v.1 = []

def weight {T : RTree} (v : Vertex T) : Nat :=
  RTree.weightAt T v.1

end Vertex

abbrev NonRootVertex (T : RTree) := { v : Vertex T // v.1 ≠ [] }

instance (T : RTree) : Fintype (NonRootVertex T) :=
  inferInstance

instance (T : RTree) : DecidableEq (NonRootVertex T) :=
  inferInstance

namespace NonRootVertex

def weight {T : RTree} (v : NonRootVertex T) : Nat :=
  Vertex.weight v.1

end NonRootVertex

end TreeGraph
