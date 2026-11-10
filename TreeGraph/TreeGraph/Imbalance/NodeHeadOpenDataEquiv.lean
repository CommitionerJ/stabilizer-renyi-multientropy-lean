import TreeGraph.Imbalance.NodeHeadOpenData
import TreeGraph.Imbalance.NodeHeadPhysicalReductionTheorem

namespace TreeGraph
namespace Imbalance

theorem headChildRootNonRootInParent_weight_eq_rootWeight
    {a : Nat} {C : RTree} {rest : List RTree} :
    NonRootVertex.weight
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) =
      C.rootWeight := by
  change Vertex.weight
      (headChildRootInParent (a := a) (C := C) (rest := rest)) = C.rootWeight
  unfold headChildRootInParent
  rw [headChildVertexInParent_weight]
  rfl

theorem parentNonRootCoordsHeadTailEquiv_symm_head_root
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (child : VertexCoordDomainClean n C)
    (tail : CoordsList n rest)
    (j : Fin C.rootWeight) :
    ((parentNonRootCoordsHeadTailEquiv n a C rest).symm (child, tail))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
      (Fin.cast
        (headChildRootNonRootInParent_weight_eq_rootWeight
          (a := a) (C := C) (rest := rest)).symm j) =
    child (Vertex.root C) j := by
  let p : NodeChildVertex (C :: rest) :=
    (nodeChildVertexConsEquiv C rest).symm (Sum.inl (Vertex.root C))
  let F : (s : Vertex C ⊕ NodeChildVertex rest) →
      Fin (nodeChildVertexSumWeight s) → Rep n :=
    (dependentSumPiEquivProd
      (fun s : Vertex C ⊕ NodeChildVertex rest =>
        Fin (nodeChildVertexSumWeight s) → Rep n)).symm
      (child, (nodeChildVertexCoordsEquivCoordsList n rest).symm tail)
  change ((rootFieldDomainCleanEquivNodeChildVertex n a (C :: rest)).symm
      ((nodeChildVertexCoordsEquivSum n C rest).symm F))
      (childVertexAtAsNonRootInNode (a := a) p)
      (Fin.cast (childVertexAtAsNonRootInNode_weight (a := a) p).symm
        (Fin.cast (nodeChildVertexConsEquiv_weight p).symm j)) =
    child (Vertex.root C) j
  rw [rootFieldDomainCleanEquivNodeChildVertex_symm_apply_child]
  rw [nodeChildVertexCoordsEquivSum_symm_inl]
  rfl

noncomputable def headRootParentDomainChildRootCopen
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))) :
    Copen n C :=
  (rootFieldDomainCleanEquivCopen n C)
    (fun v j =>
      dom.otherCoord
        ⟨headChildNonRootInParent (a := a) (C := C) (rest := rest) v, by
          simpa [headChildRootNonRootInParent, headChildNonRootInParent]
            using v.2⟩
        (Fin.cast
          (headChildNonRootInParent_weight
            (a := a) (C := C) (rest := rest) v).symm j))

noncomputable def headRootParentDomainTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))) :
    CoordsList n rest :=
  (nodeChildVertexCoordsEquivCoordsList n rest)
    (fun p j =>
      dom.otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i v =>
              simp [headChildRootNonRootInParent, headChildRootInParent,
                nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j))

theorem headRootParentDomainChildRootCopen_of_construct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest)
    (y : Copen n C) :
    headRootParentDomainChildRootCopen n a C rest
      (headChildRootDomainFromHeadIndexCopen n a C rest idx y) = y := by
  unfold headRootParentDomainChildRootCopen
    headChildRootDomainFromHeadIndexCopen
  let E := rootFieldDomainCleanEquivCopen n C
  let F : RootFieldDomainClean n C := fun v j =>
      (let childCoords := vertexCoordDomainFromBoundaryOpen n C y
       let parentCoords :=
        (parentNonRootCoordsHeadTailEquiv n a C rest).symm
          (childCoords, headChildIndexTail idx)
       ({ rootCoord := headChildIndexParentRoot idx
          diagonal := headChildIndexRootDiag idx
          otherCoord := fun u => parentCoords u.1 } :
          NonRootFieldDomainClean n (RTree.node a (C :: rest))
            (headChildRootNonRootInParent
              (a := a) (C := C) (rest := rest))).otherCoord
        ⟨headChildNonRootInParent (a := a) (C := C) (rest := rest) v, by
          simpa [headChildRootNonRootInParent, headChildNonRootInParent]
            using v.2⟩
        (Fin.cast
          (headChildNonRootInParent_weight
            (a := a) (C := C) (rest := rest) v).symm j))
  change E F = y
  have hF : F = E.symm y := by
    funext v j
    dsimp [F]
    calc
      ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
          (vertexCoordDomainFromBoundaryOpen n C y, headChildIndexTail idx))
          (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
          (Fin.cast
            (headChildNonRootInParent_weight
              (a := a) (C := C) (rest := rest) v).symm j) =
        vertexCoordDomainFromBoundaryOpen n C y v.1 j := by
          exact parentNonRootCoordsHeadTailEquiv_symm_head n a C rest
            (vertexCoordDomainFromBoundaryOpen n C y)
            (headChildIndexTail idx) v j
      _ = (E.symm y) v j := by
          exact vertexCoordDomainFromBoundaryOpen_apply_nonroot n C y v j
  rw [hF]
  exact E.right_inv y

theorem headRootParentDomainTail_of_construct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest)
    (y : Copen n C) :
    headRootParentDomainTail n a C rest
      (headChildRootDomainFromHeadIndexCopen n a C rest idx y) =
    headChildIndexTail idx := by
  unfold headRootParentDomainTail headChildRootDomainFromHeadIndexCopen
  let E := nodeChildVertexCoordsEquivCoordsList n rest
  let F : (p : NodeChildVertex rest) → Fin (Vertex.weight p.2) → Rep n :=
    fun p j =>
      (let childCoords := vertexCoordDomainFromBoundaryOpen n C y
       let parentCoords :=
        (parentNonRootCoordsHeadTailEquiv n a C rest).symm
          (childCoords, headChildIndexTail idx)
       ({ rootCoord := headChildIndexParentRoot idx
          diagonal := headChildIndexRootDiag idx
          otherCoord := fun u => parentCoords u.1 } :
          NonRootFieldDomainClean n (RTree.node a (C :: rest))
            (headChildRootNonRootInParent
              (a := a) (C := C) (rest := rest))).otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i v =>
              simp [headChildRootNonRootInParent, headChildRootInParent,
                nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j))
  change E F = headChildIndexTail idx
  have hF : F = E.symm (headChildIndexTail idx) := by
    funext p j
    dsimp [F]
    exact parentNonRootCoordsHeadTailEquiv_symm_tail n a C rest
      (vertexCoordDomainFromBoundaryOpen n C y) (headChildIndexTail idx) p j
  rw [hF]
  exact E.right_inv (headChildIndexTail idx)

noncomputable def headNonRootParentDomainChildRootBlock
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)) :
    Block n C.rootWeight :=
  fun j =>
    dom.otherCoord
      ⟨headChildRootNonRootInParent (a := a) (C := C) (rest := rest), by
        simpa [headChildRootNonRootInParent, headChildNonRootInParent,
          headChildRootInParent, eq_comm] using v.2⟩
      (Fin.cast
        (headChildRootNonRootInParent_weight_eq_rootWeight
          (a := a) (C := C) (rest := rest)).symm j)

noncomputable def headNonRootParentDomainTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)) :
    CoordsList n rest :=
  (nodeChildVertexCoordsEquivCoordsList n rest)
    (fun p j =>
      dom.otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [headChildNonRootInParent, nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j))

noncomputable def headNonRootParentDomainChildDomain
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)) :
    NonRootFieldDomainClean n C v :=
  let split :=
    blockSplitLastEquiv n C.rootWeight (rootWeight_pos_of_positiveWeights hC)
      (headNonRootParentDomainChildRootBlock n a C rest v dom)
  { rootCoord := split.1
    diagonal := dom.diagonal
    otherCoord := fun u j =>
      dom.otherCoord
        ⟨headChildNonRootInParent (a := a) (C := C) (rest := rest) u.1, by
          simpa [headChildNonRootInParent] using u.2⟩
        (Fin.cast
          (headChildNonRootInParent_weight
            (a := a) (C := C) (rest := rest) u.1).symm j) }

theorem headNonRootParentDomainTail_of_construct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    headNonRootParentDomainTail n a C rest v
      (parentHeadNonRootDomainFromChildDomain n a C rest hC idx v dom) =
    headChildIndexTail idx := by
  unfold headNonRootParentDomainTail parentHeadNonRootDomainFromChildDomain
  let E := nodeChildVertexCoordsEquivCoordsList n rest
  let F : (p : NodeChildVertex rest) → Fin (Vertex.weight p.2) → Rep n :=
    fun p j =>
      (let childCoords :=
        childVertexCoordFromHeadIndexChildDomain n a C rest hC idx v dom
       let parentCoords :=
        (parentNonRootCoordsHeadTailEquiv n a C rest).symm
          (childCoords, headChildIndexTail idx)
       ({ rootCoord := headChildIndexParentRoot idx
          diagonal := dom.diagonal
          otherCoord := fun u => parentCoords u.1 } :
          NonRootFieldDomainClean n (RTree.node a (C :: rest))
            (headChildNonRootInParent
              (a := a) (C := C) (rest := rest) v)).otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [headChildNonRootInParent, nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j))
  change E F = headChildIndexTail idx
  have hF : F = E.symm (headChildIndexTail idx) := by
    funext p j
    dsimp [F]
    exact parentNonRootCoordsHeadTailEquiv_symm_tail n a C rest
      (childVertexCoordFromHeadIndexChildDomain n a C rest hC idx v dom)
      (headChildIndexTail idx) p j
  rw [hF]
  exact E.right_inv (headChildIndexTail idx)

theorem headNonRootParentDomainChildRootBlock_of_construct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    headNonRootParentDomainChildRootBlock n a C rest v
      (parentHeadNonRootDomainFromChildDomain n a C rest hC idx v dom) =
    (blockSplitLastEquiv n C.rootWeight
      (rootWeight_pos_of_positiveWeights hC)).symm
        (dom.rootCoord, headChildIndexRootDiag idx) := by
  funext j
  unfold headNonRootParentDomainChildRootBlock
    parentHeadNonRootDomainFromChildDomain
  dsimp
  rw [parentNonRootCoordsHeadTailEquiv_symm_head_root]
  unfold childVertexCoordFromHeadIndexChildDomain
  simp [Vertex.root]

noncomputable def headRootParentDomainIndex
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))) :
    HeadChildIndex n a rest :=
  (dom.rootCoord, headRootParentDomainTail n a C rest dom, dom.diagonal)

theorem headRootParentDomainIndex_of_construct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest)
    (y : Copen n C) :
    headRootParentDomainIndex n a C rest
      (headChildRootDomainFromHeadIndexCopen n a C rest idx y) = idx := by
  cases idx with
  | mk q tailDiag =>
      cases tailDiag with
      | mk tail diag =>
          unfold headRootParentDomainIndex
          rw [headRootParentDomainTail_of_construct]
          simp [headChildRootDomainFromHeadIndexCopen, headChildIndexParentRoot,
            headChildIndexRootDiag, headChildIndexTail]

theorem headRootParentDomain_construct_extract_other_head_nonroot
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)))
    (v : NonRootVertex C)
    (j : Fin (NonRootVertex.weight v)) :
    (headChildRootDomainFromHeadIndexCopen n a C rest
      (headRootParentDomainIndex n a C rest dom)
      (headRootParentDomainChildRootCopen n a C rest dom)).otherCoord
        ⟨headChildNonRootInParent (a := a) (C := C) (rest := rest) v, by
          simp [headChildNonRootInParent, headChildVertexInParent,
            childVertexAtAsNonRootInNode, childVertexAtInNode, childVertexInNode,
            nodeChildVertexConsEquiv, castVertexOfEq, Vertex.root]
          exact v.2⟩
        (Fin.cast
          (headChildNonRootInParent_weight
            (a := a) (C := C) (rest := rest) v).symm j) =
    dom.otherCoord
        ⟨headChildNonRootInParent (a := a) (C := C) (rest := rest) v, by
          simpa [headChildRootNonRootInParent, headChildNonRootInParent,
            headChildRootInParent] using v.2⟩
        (Fin.cast
          (headChildNonRootInParent_weight
            (a := a) (C := C) (rest := rest) v).symm j) := by
  unfold headChildRootDomainFromHeadIndexCopen headRootParentDomainIndex
  dsimp
  rw [parentNonRootCoordsHeadTailEquiv_symm_head]
  rw [vertexCoordDomainFromBoundaryOpen_apply_nonroot]
  unfold headRootParentDomainChildRootCopen
  let E := rootFieldDomainCleanEquivCopen n C
  let F : RootFieldDomainClean n C := fun w k =>
    dom.otherCoord
      ⟨headChildNonRootInParent (a := a) (C := C) (rest := rest) w, by
        simpa [headChildRootNonRootInParent, headChildNonRootInParent,
          headChildRootInParent] using w.2⟩
      (Fin.cast
        (headChildNonRootInParent_weight
          (a := a) (C := C) (rest := rest) w).symm k)
  have hEF := E.left_inv F
  have hval := congrFun (congrFun hEF v) j
  simpa [E, F] using hval

theorem headRootParentDomain_construct_extract_other_tail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)))
    (p : NodeChildVertex rest)
    (j : Fin (Vertex.weight p.2)) :
    (headChildRootDomainFromHeadIndexCopen n a C rest
      (headRootParentDomainIndex n a C rest dom)
      (headRootParentDomainChildRootCopen n a C rest dom)).otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j) =
    dom.otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j) := by
  unfold headChildRootDomainFromHeadIndexCopen headRootParentDomainIndex
  change ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
      (vertexCoordDomainFromBoundaryOpen n C
          (headRootParentDomainChildRootCopen n a C rest dom),
        headRootParentDomainTail n a C rest dom)
      (childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)))
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j)) =
    dom.otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j)
  calc
    ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
      (vertexCoordDomainFromBoundaryOpen n C
          (headRootParentDomainChildRootCopen n a C rest dom),
        headRootParentDomainTail n a C rest dom)
      (childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)))
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j)) =
      ((nodeChildVertexCoordsEquivCoordsList n rest).symm
        (headRootParentDomainTail n a C rest dom)) p j := by
        convert parentNonRootCoordsHeadTailEquiv_symm_tail n a C rest
          (vertexCoordDomainFromBoundaryOpen n C
            (headRootParentDomainChildRootCopen n a C rest dom))
          (headRootParentDomainTail n a C rest dom) p j using 1
    _ = dom.otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j) := by
        unfold headRootParentDomainTail
        let E := nodeChildVertexCoordsEquivCoordsList n rest
        let F : (p : NodeChildVertex rest) →
            Fin (Vertex.weight p.2) → Rep n := fun p k =>
          dom.otherCoord
            ⟨childVertexAtAsNonRootInNode (a := a)
                ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
              cases p with
              | mk i w =>
                  simp [nodeChildVertexConsEquiv]⟩
            (Fin.cast (by
              rw [childVertexAtAsNonRootInNode_weight]
              exact (nodeChildVertexConsEquiv_weight
                ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) k)
        have hEF := E.left_inv F
        have hval := congrFun (congrFun hEF p) j
        simpa [E, F] using hval

theorem headRootParentDomain_construct_extract
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))) :
    headChildRootDomainFromHeadIndexCopen n a C rest
      (headRootParentDomainIndex n a C rest dom)
      (headRootParentDomainChildRootCopen n a C rest dom) =
    dom := by
  cases dom with
  | mk rootCoord diagonal otherCoord =>
      unfold headChildRootDomainFromHeadIndexCopen headRootParentDomainIndex
      change ({ rootCoord := rootCoord
                diagonal := diagonal
                otherCoord := fun u =>
                  ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
                    (vertexCoordDomainFromBoundaryOpen n C
                      (headRootParentDomainChildRootCopen n a C rest
                        ({ rootCoord := rootCoord,
                           diagonal := diagonal,
                           otherCoord := otherCoord } :
                          NonRootFieldDomainClean n (RTree.node a (C :: rest))
                            (headChildRootNonRootInParent
                              (a := a) (C := C) (rest := rest)))),
                     headRootParentDomainTail n a C rest
                        ({ rootCoord := rootCoord,
                           diagonal := diagonal,
                           otherCoord := otherCoord } :
                          NonRootFieldDomainClean n (RTree.node a (C :: rest))
                            (headChildRootNonRootInParent
                              (a := a) (C := C) (rest := rest))))) u.1 } :
        NonRootFieldDomainClean n (RTree.node a (C :: rest))
          (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))) =
        { rootCoord := rootCoord, diagonal := diagonal, otherCoord := otherCoord }
      rw [NonRootFieldDomainClean.mk.injEq]
      constructor
      · rfl
      constructor
      · rfl
      · funext u j
        let p := (nonRootVertexNodeEquivChildVertex a (C :: rest)) u.1
        have hu_from_p : childVertexAtAsNonRootInNode (a := a) p = u.1 := by
          dsimp [p]
          exact (nonRootVertexNodeEquivChildVertex a (C :: rest)).left_inv u.1
        cases hsum : (nodeChildVertexConsEquiv C rest) p with
        | inl v =>
            by_cases hvroot : v.1 = []
            · have hp :
                  p = (nodeChildVertexConsEquiv C rest).symm (Sum.inl v) := by
                exact (Equiv.apply_eq_iff_eq_symm_apply
                  (nodeChildVertexConsEquiv C rest)).mp hsum
              have hu_addr : u.1.1.1 = [0] := by
                rw [← hu_from_p, hp]
                dsimp [nodeChildVertexConsEquiv]
                simp
                exact hvroot
              exact False.elim
                (u.2 (by
                  simpa [headChildRootNonRootInParent, headChildRootInParent]
                    using hu_addr))
            · let vnr : NonRootVertex C := ⟨v, hvroot⟩
              have hp :
                  p = (nodeChildVertexConsEquiv C rest).symm (Sum.inl v) := by
                exact (Equiv.apply_eq_iff_eq_symm_apply
                  (nodeChildVertexConsEquiv C rest)).mp hsum
              have hu_eq :
                  u.1 =
                    headChildNonRootInParent
                      (a := a) (C := C) (rest := rest) vnr := by
                rw [← hu_from_p, hp]
                rfl
              cases u with
              | mk u hu =>
                  cases hu_eq
                  convert
                    headRootParentDomain_construct_extract_other_head_nonroot
                      n a C rest
                      ({ rootCoord := rootCoord, diagonal := diagonal, otherCoord := otherCoord } :
                        NonRootFieldDomainClean n (RTree.node a (C :: rest))
                          (headChildRootNonRootInParent
                            (a := a) (C := C) (rest := rest)))
                      vnr
                      (Fin.cast
                        (headChildNonRootInParent_weight
                          (a := a) (C := C) (rest := rest) vnr) j)
                    using 1
        | inr pTail =>
            have hp :
                p = (nodeChildVertexConsEquiv C rest).symm (Sum.inr pTail) := by
              exact (Equiv.apply_eq_iff_eq_symm_apply
                (nodeChildVertexConsEquiv C rest)).mp hsum
            have hu_eq :
                u.1 =
                  childVertexAtAsNonRootInNode (a := a)
                    ((nodeChildVertexConsEquiv C rest).symm (Sum.inr pTail)) := by
              rw [← hu_from_p, hp]
            cases u with
            | mk u hu =>
                cases hu_eq
                convert
                  headRootParentDomain_construct_extract_other_tail
                    n a C rest
                    ({ rootCoord := rootCoord, diagonal := diagonal, otherCoord := otherCoord } :
                      NonRootFieldDomainClean n (RTree.node a (C :: rest))
                        (headChildRootNonRootInParent
                          (a := a) (C := C) (rest := rest)))
                    pTail
                    (Fin.cast (by
                      change NonRootVertex.weight
                          (childVertexAtAsNonRootInNode (a := a)
                            ((nodeChildVertexConsEquiv C rest).symm
                              (Sum.inr pTail))) = Vertex.weight pTail.2
                      rw [childVertexAtAsNonRootInNode_weight]
                      exact (nodeChildVertexConsEquiv_weight
                        ((nodeChildVertexConsEquiv C rest).symm
                          (Sum.inr pTail))))
                      j)
                  using 1

noncomputable def headNonRootParentDomainIndex
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)) :
    HeadChildIndex n a rest :=
  let split :=
    blockSplitLastEquiv n C.rootWeight (rootWeight_pos_of_positiveWeights hC)
      (headNonRootParentDomainChildRootBlock n a C rest v dom)
  (dom.rootCoord, headNonRootParentDomainTail n a C rest v dom, split.2)

theorem headNonRootParentDomainIndex_of_construct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    headNonRootParentDomainIndex n a C rest hC v
      (parentHeadNonRootDomainFromChildDomain n a C rest hC idx v dom) =
    idx := by
  cases idx with
  | mk q tailDiag =>
      cases tailDiag with
      | mk tail diag =>
          unfold headNonRootParentDomainIndex
          rw [headNonRootParentDomainTail_of_construct]
          rw [headNonRootParentDomainChildRootBlock_of_construct]
          simp [parentHeadNonRootDomainFromChildDomain, headChildIndexParentRoot,
            headChildIndexRootDiag, headChildIndexTail]

theorem headNonRootParentDomainChildDomain_of_construct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    headNonRootParentDomainChildDomain n a C rest hC v
      (parentHeadNonRootDomainFromChildDomain n a C rest hC idx v dom) =
    dom := by
  cases dom with
  | mk rootCoord diagonal otherCoord =>
      unfold headNonRootParentDomainChildDomain
      rw [headNonRootParentDomainChildRootBlock_of_construct]
      simp [parentHeadNonRootDomainFromChildDomain]
      funext u j
      calc
        ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
            (childVertexCoordFromHeadIndexChildDomain n a C rest hC idx v
              { rootCoord := rootCoord
                diagonal := diagonal
                otherCoord := otherCoord },
              headChildIndexTail idx))
            (headChildNonRootInParent (a := a) (C := C) (rest := rest) u.1)
            (Fin.cast
              (headChildNonRootInParent_weight
                (a := a) (C := C) (rest := rest) u.1).symm j) =
          childVertexCoordFromHeadIndexChildDomain n a C rest hC idx v
              { rootCoord := rootCoord
                diagonal := diagonal
                otherCoord := otherCoord } u.1 j := by
            exact parentNonRootCoordsHeadTailEquiv_symm_head n a C rest
              (childVertexCoordFromHeadIndexChildDomain n a C rest hC idx v
                { rootCoord := rootCoord
                  diagonal := diagonal
                  otherCoord := otherCoord })
              (headChildIndexTail idx) u.1 j
        _ = otherCoord u j := by
            unfold childVertexCoordFromHeadIndexChildDomain
            simp [u.1.2, u.2]

theorem headNonRootParentDomain_construct_extract_other_root
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v))
    (j : Fin C.rootWeight) :
    (parentHeadNonRootDomainFromChildDomain n a C rest hC
      (headNonRootParentDomainIndex n a C rest hC v dom)
      v
      (headNonRootParentDomainChildDomain n a C rest hC v dom)).otherCoord
        ⟨headChildRootNonRootInParent (a := a) (C := C) (rest := rest), by
          simp [headChildRootNonRootInParent, headChildRootInParent,
            nodeChildVertexConsEquiv, Vertex.root, childVertexAtAsNonRootInNode,
            childVertexAtInNode, childVertexInNode, castVertexOfEq]
          exact v.2⟩
        (Fin.cast
          (headChildRootNonRootInParent_weight_eq_rootWeight
            (a := a) (C := C) (rest := rest)).symm j) =
    dom.otherCoord
        ⟨headChildRootNonRootInParent (a := a) (C := C) (rest := rest), by
          simpa [headChildRootNonRootInParent, headChildNonRootInParent,
            headChildRootInParent, eq_comm] using v.2⟩
        (Fin.cast
          (headChildRootNonRootInParent_weight_eq_rootWeight
            (a := a) (C := C) (rest := rest)).symm j) := by
  unfold parentHeadNonRootDomainFromChildDomain headNonRootParentDomainIndex
  dsimp
  rw [parentNonRootCoordsHeadTailEquiv_symm_head_root]
  unfold childVertexCoordFromHeadIndexChildDomain
  simp [Vertex.root]
  unfold headNonRootParentDomainChildDomain
  dsimp [headChildIndexRootDiag]
  let E := blockSplitLastEquiv n C.rootWeight
    (rootWeight_pos_of_positiveWeights hC)
  let block := headNonRootParentDomainChildRootBlock n a C rest v dom
  change E.symm (E block) j = block j
  exact congrFun (E.left_inv block) j

theorem headNonRootParentDomain_construct_extract_other_head_nonroot
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v))
    (u : OtherNonRootVertexClean C v)
    (j : Fin (NonRootVertex.weight u.1)) :
    (parentHeadNonRootDomainFromChildDomain n a C rest hC
      (headNonRootParentDomainIndex n a C rest hC v dom)
      v
      (headNonRootParentDomainChildDomain n a C rest hC v dom)).otherCoord
        ⟨headChildNonRootInParent (a := a) (C := C) (rest := rest) u.1, by
          simp [headChildNonRootInParent, headChildVertexInParent,
            childVertexAtAsNonRootInNode, childVertexAtInNode, childVertexInNode,
            nodeChildVertexConsEquiv, castVertexOfEq]
          exact u.2⟩
        (Fin.cast
          (headChildNonRootInParent_weight
            (a := a) (C := C) (rest := rest) u.1).symm j) =
    dom.otherCoord
        ⟨headChildNonRootInParent (a := a) (C := C) (rest := rest) u.1, by
          simpa [headChildNonRootInParent] using u.2⟩
        (Fin.cast
          (headChildNonRootInParent_weight
            (a := a) (C := C) (rest := rest) u.1).symm j) := by
  unfold parentHeadNonRootDomainFromChildDomain
  dsimp
  rw [parentNonRootCoordsHeadTailEquiv_symm_head]
  unfold childVertexCoordFromHeadIndexChildDomain
  simp [u.1.2, u.2]
  unfold headNonRootParentDomainChildDomain
  rfl

theorem headNonRootParentDomain_construct_extract_other_tail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v))
    (p : NodeChildVertex rest)
    (j : Fin (Vertex.weight p.2)) :
    (parentHeadNonRootDomainFromChildDomain n a C rest hC
      (headNonRootParentDomainIndex n a C rest hC v dom)
      v
      (headNonRootParentDomainChildDomain n a C rest hC v dom)).otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j) =
    dom.otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [headChildNonRootInParent, nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j) := by
  unfold parentHeadNonRootDomainFromChildDomain
  change ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
      (childVertexCoordFromHeadIndexChildDomain n a C rest hC
          (headNonRootParentDomainIndex n a C rest hC v dom)
          v (headNonRootParentDomainChildDomain n a C rest hC v dom),
        headNonRootParentDomainTail n a C rest v dom)
      (childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)))
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j)) =
    dom.otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [headChildNonRootInParent, nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j)
  calc
    ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
      (childVertexCoordFromHeadIndexChildDomain n a C rest hC
          (headNonRootParentDomainIndex n a C rest hC v dom)
          v (headNonRootParentDomainChildDomain n a C rest hC v dom),
        headNonRootParentDomainTail n a C rest v dom)
      (childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)))
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j)) =
      ((nodeChildVertexCoordsEquivCoordsList n rest).symm
        (headNonRootParentDomainTail n a C rest v dom)) p j := by
        convert parentNonRootCoordsHeadTailEquiv_symm_tail n a C rest
          (childVertexCoordFromHeadIndexChildDomain n a C rest hC
            (headNonRootParentDomainIndex n a C rest hC v dom)
            v (headNonRootParentDomainChildDomain n a C rest hC v dom))
          (headNonRootParentDomainTail n a C rest v dom) p j using 1
    _ = dom.otherCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [headChildNonRootInParent, nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j) := by
        unfold headNonRootParentDomainTail
        let E := nodeChildVertexCoordsEquivCoordsList n rest
        let F : (p : NodeChildVertex rest) →
            Fin (Vertex.weight p.2) → Rep n := fun p k =>
          dom.otherCoord
            ⟨childVertexAtAsNonRootInNode (a := a)
                ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
              cases p with
              | mk i w =>
                  simp [headChildNonRootInParent, nodeChildVertexConsEquiv]⟩
            (Fin.cast (by
              rw [childVertexAtAsNonRootInNode_weight]
              exact (nodeChildVertexConsEquiv_weight
                ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) k)
        have hEF := E.left_inv F
        have hval := congrFun (congrFun hEF p) j
        simpa [E, F] using hval

theorem headNonRootParentDomain_construct_extract
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)) :
    parentHeadNonRootDomainFromChildDomain n a C rest hC
      (headNonRootParentDomainIndex n a C rest hC v dom)
      v
      (headNonRootParentDomainChildDomain n a C rest hC v dom) =
    dom := by
  cases dom with
  | mk rootCoord diagonal otherCoord =>
      unfold parentHeadNonRootDomainFromChildDomain
      change ({ rootCoord := rootCoord
                diagonal := diagonal
                otherCoord := fun u =>
                  ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
                    (childVertexCoordFromHeadIndexChildDomain n a C rest hC
                      (headNonRootParentDomainIndex n a C rest hC v
                        ({ rootCoord := rootCoord,
                           diagonal := diagonal,
                           otherCoord := otherCoord } :
                          NonRootFieldDomainClean n (RTree.node a (C :: rest))
                            (headChildNonRootInParent
                              (a := a) (C := C) (rest := rest) v)))
                      v
                      (headNonRootParentDomainChildDomain n a C rest hC v
                        ({ rootCoord := rootCoord,
                           diagonal := diagonal,
                           otherCoord := otherCoord } :
                          NonRootFieldDomainClean n (RTree.node a (C :: rest))
                            (headChildNonRootInParent
                              (a := a) (C := C) (rest := rest) v))),
                     headNonRootParentDomainTail n a C rest v
                        ({ rootCoord := rootCoord,
                           diagonal := diagonal,
                           otherCoord := otherCoord } :
                          NonRootFieldDomainClean n (RTree.node a (C :: rest))
                            (headChildNonRootInParent
                              (a := a) (C := C) (rest := rest) v)))) u.1 } :
        NonRootFieldDomainClean n (RTree.node a (C :: rest))
          (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)) =
        { rootCoord := rootCoord, diagonal := diagonal, otherCoord := otherCoord }
      rw [NonRootFieldDomainClean.mk.injEq]
      constructor
      · rfl
      constructor
      · rfl
      · funext u j
        let p := (nonRootVertexNodeEquivChildVertex a (C :: rest)) u.1
        have hu_from_p : childVertexAtAsNonRootInNode (a := a) p = u.1 := by
          dsimp [p]
          exact (nonRootVertexNodeEquivChildVertex a (C :: rest)).left_inv u.1
        cases hsum : (nodeChildVertexConsEquiv C rest) p with
        | inl w =>
            by_cases hwroot : w.1 = []
            · have hp :
                  p = (nodeChildVertexConsEquiv C rest).symm (Sum.inl w) := by
                exact (Equiv.apply_eq_iff_eq_symm_apply
                  (nodeChildVertexConsEquiv C rest)).mp hsum
              have hw : w = Vertex.root C := by
                apply Subtype.ext
                exact hwroot
              subst w
              have hu_eq_root :
                  u.1 =
                    headChildRootNonRootInParent
                      (a := a) (C := C) (rest := rest) := by
                rw [← hu_from_p, hp]
                rfl
              cases u with
              | mk u hu =>
                  cases hu_eq_root
                  convert
                    headNonRootParentDomain_construct_extract_other_root
                      n a C rest hC v
                      ({ rootCoord := rootCoord, diagonal := diagonal, otherCoord := otherCoord } :
                        NonRootFieldDomainClean n (RTree.node a (C :: rest))
                          (headChildNonRootInParent
                            (a := a) (C := C) (rest := rest) v))
                      (Fin.cast
                        (headChildRootNonRootInParent_weight_eq_rootWeight
                          (a := a) (C := C) (rest := rest)) j)
                    using 1
            · let wnr : NonRootVertex C := ⟨w, hwroot⟩
              have hp :
                  p = (nodeChildVertexConsEquiv C rest).symm (Sum.inl w) := by
                exact (Equiv.apply_eq_iff_eq_symm_apply
                  (nodeChildVertexConsEquiv C rest)).mp hsum
              by_cases hsame : w.1 = v.1.1
              · have hu_eq_v :
                    u.1 =
                      headChildNonRootInParent
                        (a := a) (C := C) (rest := rest) v := by
                  have hw : w = v.1 := by
                    apply Subtype.ext
                    exact hsame
                  subst w
                  rw [← hu_from_p, hp]
                  rfl
                exact False.elim
                  (u.2 (by
                    exact congrArg (fun x : NonRootVertex
                      (RTree.node a (C :: rest)) => x.1.1) hu_eq_v))
              · let uChild : OtherNonRootVertexClean C v := ⟨wnr, hsame⟩
                have hu_eq :
                    u.1 =
                      headChildNonRootInParent
                        (a := a) (C := C) (rest := rest) wnr := by
                  rw [← hu_from_p, hp]
                  rfl
                cases u with
                | mk u hu =>
                    cases hu_eq
                    convert
                      headNonRootParentDomain_construct_extract_other_head_nonroot
                        n a C rest hC v
                        ({ rootCoord := rootCoord,
                           diagonal := diagonal,
                           otherCoord := otherCoord } :
                          NonRootFieldDomainClean n (RTree.node a (C :: rest))
                            (headChildNonRootInParent
                              (a := a) (C := C) (rest := rest) v))
                        uChild
                        (Fin.cast
                          (headChildNonRootInParent_weight
                            (a := a) (C := C) (rest := rest) wnr) j)
                      using 1
        | inr pTail =>
            have hp :
                p = (nodeChildVertexConsEquiv C rest).symm (Sum.inr pTail) := by
              exact (Equiv.apply_eq_iff_eq_symm_apply
                (nodeChildVertexConsEquiv C rest)).mp hsum
            have hu_eq :
                u.1 =
                  childVertexAtAsNonRootInNode (a := a)
                    ((nodeChildVertexConsEquiv C rest).symm (Sum.inr pTail)) := by
              rw [← hu_from_p, hp]
            cases u with
            | mk u hu =>
                cases hu_eq
                convert
                  headNonRootParentDomain_construct_extract_other_tail
                    n a C rest hC v
                    ({ rootCoord := rootCoord, diagonal := diagonal, otherCoord := otherCoord } :
                      NonRootFieldDomainClean n (RTree.node a (C :: rest))
                        (headChildNonRootInParent
                          (a := a) (C := C) (rest := rest) v))
                    pTail
                    (Fin.cast (by
                      change NonRootVertex.weight
                          (childVertexAtAsNonRootInNode (a := a)
                            ((nodeChildVertexConsEquiv C rest).symm
                              (Sum.inr pTail))) = Vertex.weight pTail.2
                      rw [childVertexAtAsNonRootInNode_weight]
                      exact (nodeChildVertexConsEquiv_weight
                        ((nodeChildVertexConsEquiv C rest).symm
                          (Sum.inr pTail))))
                      j)
                  using 1

noncomputable def headChildOpenDataToParentOpenHeadFields
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    HeadChildOpenData n a C rest → ParentOpenHeadFields n a C rest :=
  fun data v parentDom => by
    by_cases hroot : v.1 = []
    · have hv : v = Vertex.root C := by
        apply Subtype.ext
        exact hroot
      subst v
      exact
        P.rootCopenBridge.linearEquiv
          (data (headRootParentDomainIndex n a C rest parentDom)).1
          (headRootParentDomainChildRootCopen n a C rest parentDom)
    · let vnr : NonRootVertex C := ⟨v, hroot⟩
      exact
        ((data
          (headNonRootParentDomainIndex n a C rest hC vnr parentDom)).2).nodeField
          vnr
          (headNonRootParentDomainChildDomain n a C rest hC vnr parentDom)

theorem parentOpenHeadFieldsEquivHeadChildOpenData_symm_apply_root
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest) (y : Copen n C) :
    (headChildOpenDataToParentOpenHeadFields n a C rest hC P data)
      (Vertex.root C)
      (headChildRootDomainFromHeadIndexCopen n a C rest idx y)
    = P.rootCopenBridge.linearEquiv (data idx).1 y := by
  unfold headChildOpenDataToParentOpenHeadFields
  simp [Vertex.root]
  rw [headRootParentDomainIndex_of_construct]
  rw [headRootParentDomainChildRootCopen_of_construct]

theorem parentOpenHeadFieldsEquivHeadChildOpenData_symm_apply_nonroot
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    (headChildOpenDataToParentOpenHeadFields n a C rest hC P data)
      v.1
      (parentHeadNonRootDomainFromChildDomain n a C rest hC idx v dom)
    = ((data idx).2).nodeField v dom := by
  unfold headChildOpenDataToParentOpenHeadFields
  simp [v.2]
  rw [headNonRootParentDomainIndex_of_construct]
  rw [headNonRootParentDomainChildDomain_of_construct]

noncomputable def parentOpenHeadFieldsEquivHeadChildOpenData
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    ParentOpenHeadFields n a C rest ≃ HeadChildOpenData n a C rest where
  toFun := parentOpenHeadFieldsToHeadChildOpenData n a C rest hC P
  invFun := headChildOpenDataToParentOpenHeadFields n a C rest hC P
  left_inv := by
    intro head
    funext v dom
    unfold parentOpenHeadFieldsToHeadChildOpenData
      headChildOpenDataToParentOpenHeadFields
    by_cases hroot : v.1 = []
    · have hv : v = Vertex.root C := by
        apply Subtype.ext
        exact hroot
      subst v
      simp [Vertex.root]
      unfold headChildRootBoundaryFromParentOpenHead
      rw [headRootParentDomain_construct_extract]
      congr 1
    · let vnr : NonRootVertex C := ⟨v, hroot⟩
      simp [hroot]
      rw [headNonRootParentDomain_construct_extract]
  right_inv := by
    intro data
    funext idx
    apply Prod.ext
    · apply (P.rootCopenBridge.linearEquiv).injective
      rw [parentOpenHeadFieldsToHeadChildOpenData_root_boundary]
      funext y
      exact parentOpenHeadFieldsEquivHeadChildOpenData_symm_apply_root
        n a C rest hC P data idx y
    · rw [OpenNormalAssignmentClean.mk.injEq]
      funext v dom
      rw [parentOpenHeadFieldsToHeadChildOpenData_open_projection]
      exact parentOpenHeadFieldsEquivHeadChildOpenData_symm_apply_nonroot
        n a C rest hC P data idx v dom

noncomputable def parentHeadFieldsDataSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) : ℤ :=
  by
    classical
    let e := parentOpenHeadFieldsEquivHeadChildOpenData n a C rest hC P
    exact
      ∑ head : ParentOpenHeadFields n a C rest,
        headChildOpenDataInternalWeight n a C rest (e head) *
          chi (headChildOpenDataBoundaryExponent
            n a C rest hC P root (e head))

theorem parentHeadFieldsDataSignedSum_eq_headChildPhysicalSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    parentHeadFieldsDataSignedSum n a C rest hC P root =
      headChildPhysicalSignedSum n a C rest hC P root := by
  classical
  unfold parentHeadFieldsDataSignedSum headChildPhysicalSignedSum
    headChildOpenDataSignedSum
  let e := parentOpenHeadFieldsEquivHeadChildOpenData n a C rest hC P
  let F : HeadChildOpenData n a C rest → ℤ := fun data =>
    headChildOpenDataInternalWeight n a C rest data *
      chi (headChildOpenDataBoundaryExponent n a C rest hC P root data)
  change (∑ head : ParentOpenHeadFields n a C rest, F (e head)) =
    ∑ data : HeadChildOpenData n a C rest, F data
  exact Equiv.sum_comp e F

end Imbalance
end TreeGraph
