import TreeGraph.Imbalance.NodeTailPhaseProductEquiv
import TreeGraph.Imbalance.NodeTailOpenDataEquiv
import TreeGraph.Imbalance.NodeHeadProjectionBridge
import TreeGraph.Imbalance.NodePhaseEdgeSplit

namespace TreeGraph
namespace Imbalance

def blockCplusTailCoordsEquiv
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    Block n (a - 1) × (Cplus n C × CoordsList n rest) ≃
      Cplus n C × (Block n (a - 1) × CoordsList n rest) where
  toFun P := (P.2.1, (P.1, P.2.2))
  invFun P := (P.2.1, (P.1, P.2.2))
  left_inv P := by
    rcases P with ⟨rootCoord, p, tailCoord⟩
    rfl
  right_inv P := by
    rcases P with ⟨p, rootCoord, tailCoord⟩
    rfl

noncomputable def normalSiteClean_node_tailEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) :
    NormalSiteClean n (RTree.node a (C :: rest)) ≃
      Cplus n C × NormalSiteClean n (RTree.node a rest) :=
  (normalSiteCleanEquivRootNonRoot n (RTree.node a (C :: rest))).trans
    ((Equiv.prodCongr (Equiv.refl (Block n (a - 1)))
      (parentNonRootCoordsHeadTailEquiv n a C rest)).trans
      ((Equiv.prodCongr (Equiv.refl (Block n (a - 1)))
        (Equiv.prodCongr (vertexCoordDomainEquivCplus n C)
          (Equiv.refl (CoordsList n rest)))).trans
        ((blockCplusTailCoordsEquiv n a C rest).trans
          (Equiv.prodCongr (Equiv.refl (Cplus n C))
            ((normalSiteCleanEquivRootCopen n
              (RTree.node a rest)).symm)))))

theorem rootFieldDomainCleanEquivCopen_node_cons_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (rd : RootFieldDomainClean n (RTree.node a (C :: rest))) :
    rootFieldDomainCleanEquivCopen_node n a (C :: rest) rd =
      ((vertexCoordDomainEquivCplus n C)
          ((parentNonRootCoordsHeadTailEquiv n a C rest rd).1),
        (parentNonRootCoordsHeadTailEquiv n a C rest rd).2) := by
  rfl

theorem rootFieldCleanCopenBridge_linearEquiv_apply_domEquiv
    {n : Nat} [NeZero n] {T : RTree}
    (B : RootFieldCleanCopenBridge n T)
    (root : RootFieldAssignmentClean n T)
    (rd : RootFieldDomainClean n T) :
    B.linearEquiv root (B.domEquiv rd) = root rd := by
  unfold RootFieldCleanCopenBridge.linearEquiv
    rootFieldCleanLinearEquivBoundaryOfEquiv
  simp [precomposeLinearEquiv]

theorem normalSiteClean_node_tailEquiv_symm_rootCoord
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    ((normalSiteClean_node_tailEquiv n a C rest).symm
      (p, tailSite)).rootCoord = tailSite.rootCoord := by
  rfl

theorem normalSiteClean_node_tailEquiv_symm_headCplus
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    (vertexCoordDomainEquivCplus n C)
      ((parentNonRootCoordsHeadTailEquiv n a C rest)
        ((normalSiteClean_node_tailEquiv n a C rest).symm
          (p, tailSite)).nonRootCoord).1 = p := by
  change
    (vertexCoordDomainEquivCplus n C)
      ((parentNonRootCoordsHeadTailEquiv n a C rest)
        ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
          ((vertexCoordDomainEquivCplus n C).symm p,
            (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
              tailSite.nonRootCoord))).1 = p
  let P :=
    ((vertexCoordDomainEquivCplus n C).symm p,
      (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
        tailSite.nonRootCoord)
  have hP := (parentNonRootCoordsHeadTailEquiv n a C rest).right_inv P
  change
    (vertexCoordDomainEquivCplus n C)
      ((parentNonRootCoordsHeadTailEquiv n a C rest)
        ((parentNonRootCoordsHeadTailEquiv n a C rest).symm P)).1 = p
  calc
    (vertexCoordDomainEquivCplus n C)
        ((parentNonRootCoordsHeadTailEquiv n a C rest)
          ((parentNonRootCoordsHeadTailEquiv n a C rest).symm P)).1 =
        (vertexCoordDomainEquivCplus n C) P.1 := by
          exact
            congrArg
              (fun Q : VertexCoordDomainClean n C × CoordsList n rest =>
                (vertexCoordDomainEquivCplus n C) Q.1) hP
    _ = p := by
      exact (vertexCoordDomainEquivCplus n C).right_inv p

theorem normalSiteClean_node_tailEquiv_symm_tailCoords
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    ((parentNonRootCoordsHeadTailEquiv n a C rest)
        ((normalSiteClean_node_tailEquiv n a C rest).symm
          (p, tailSite)).nonRootCoord).2 =
      (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
        tailSite.nonRootCoord := by
  change
    ((parentNonRootCoordsHeadTailEquiv n a C rest)
        ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
          ((vertexCoordDomainEquivCplus n C).symm p,
            (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
              tailSite.nonRootCoord))).2 =
      (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
        tailSite.nonRootCoord
  let P :=
    ((vertexCoordDomainEquivCplus n C).symm p,
      (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
        tailSite.nonRootCoord)
  have hP :=
    congrArg Prod.snd
      ((parentNonRootCoordsHeadTailEquiv n a C rest).right_inv P)
  change
    ((parentNonRootCoordsHeadTailEquiv n a C rest)
        ((parentNonRootCoordsHeadTailEquiv n a C rest).symm P)).2 = P.2
  exact hP

theorem normalSiteClean_node_tailEquiv_symm_tailSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    { rootCoord :=
        ((normalSiteClean_node_tailEquiv n a C rest).symm
          (p, tailSite)).rootCoord
      nonRootCoord :=
        (rootFieldDomainCleanEquivCopen n (RTree.node a rest)).symm
          (((parentNonRootCoordsHeadTailEquiv n a C rest)
            ((normalSiteClean_node_tailEquiv n a C rest).symm
              (p, tailSite)).nonRootCoord).2) } =
      tailSite := by
  cases tailSite with
  | mk rootCoord nonRootCoord =>
      rw [NormalSiteClean.mk.injEq]
      constructor
      · rfl
      · rw [normalSiteClean_node_tailEquiv_symm_tailCoords]
        exact (rootFieldDomainCleanEquivCopen n (RTree.node a rest)).left_inv
          nonRootCoord

theorem normalSiteClean_node_tailEquiv_symm_parentCopen
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    (rootFieldDomainCleanEquivCopen n (RTree.node a (C :: rest)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)).nonRootCoord =
      (p,
        (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
          tailSite.nonRootCoord) := by
  change
    rootFieldDomainCleanEquivCopen_node n a (C :: rest)
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)).nonRootCoord =
      (p,
        (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
          tailSite.nonRootCoord)
  rw [rootFieldDomainCleanEquivCopen_node_cons_apply]
  apply Prod.ext
  · exact normalSiteClean_node_tailEquiv_symm_headCplus n a C rest p tailSite
  · exact normalSiteClean_node_tailEquiv_symm_tailCoords n a C rest p tailSite

theorem headParentRootBoundaryFieldFromRoot_apply_tailSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    headParentRootBoundaryFieldFromRoot n a C rest root
      (p, (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
        tailSite.nonRootCoord) =
    root ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)).nonRootCoord := by
  let rd :=
    ((normalSiteClean_node_tailEquiv n a C rest).symm
      (p, tailSite)).nonRootCoord
  change
    headParentRootBoundaryFieldFromRoot n a C rest root
      (p, (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
        tailSite.nonRootCoord) = root rd
  calc
    headParentRootBoundaryFieldFromRoot n a C rest root
        (p, (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
          tailSite.nonRootCoord) =
        headParentRootBoundaryFieldFromRoot n a C rest root
          ((rootFieldDomainCleanEquivCopen n
            (RTree.node a (C :: rest))) rd) := by
          exact congrArg
            (headParentRootBoundaryFieldFromRoot n a C rest root)
            (normalSiteClean_node_tailEquiv_symm_parentCopen
              n a C rest p tailSite).symm
    _ = root rd := by
          simpa [headParentRootBoundaryFieldFromRoot,
            RootFieldCleanCopenBridge.node, RootFieldCleanCopenBridge.ofTree] using
            rootFieldCleanCopenBridge_linearEquiv_apply_domEquiv
              (RootFieldCleanCopenBridge.node n a (C :: rest)) root rd

theorem tailRootFieldFromHeadCplus_eval_tailSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    root ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)).nonRootCoord =
      (tailRootFieldFromHeadCplus n a C rest root p)
        tailSite.nonRootCoord := by
  let tailCopen :=
    (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
      tailSite.nonRootCoord
  have hparent :
      headParentRootBoundaryFieldFromRoot n a C rest root
        (p, tailCopen) =
      root ((normalSiteClean_node_tailEquiv n a C rest).symm
          (p, tailSite)).nonRootCoord := by
    exact headParentRootBoundaryFieldFromRoot_apply_tailSite
      n a C rest root p tailSite
  have hboundary :
      (RootFieldCleanCopenBridge.node n a rest).linearEquiv
          (tailRootFieldFromHeadCplus n a C rest root p) tailCopen =
        headParentRootBoundaryFieldFromRoot n a C rest root
          (p, tailCopen) := by
    exact congrFun
      (tailRootFieldFromHeadCplus_boundary n a C rest root p) tailCopen
  have htail :
      (RootFieldCleanCopenBridge.node n a rest).linearEquiv
          (tailRootFieldFromHeadCplus n a C rest root p) tailCopen =
        (tailRootFieldFromHeadCplus n a C rest root p)
          tailSite.nonRootCoord := by
    change
      (RootFieldCleanCopenBridge.node n a rest).linearEquiv
          (tailRootFieldFromHeadCplus n a C rest root p)
          ((RootFieldCleanCopenBridge.node n a rest).domEquiv
            tailSite.nonRootCoord) =
        (tailRootFieldFromHeadCplus n a C rest root p)
          tailSite.nonRootCoord
    exact
      rootFieldCleanCopenBridge_linearEquiv_apply_domEquiv
        (RootFieldCleanCopenBridge.node n a rest)
        (tailRootFieldFromHeadCplus n a C rest root p)
        tailSite.nonRootCoord
  calc
    root ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)).nonRootCoord =
        headParentRootBoundaryFieldFromRoot n a C rest root
          (p, tailCopen) := hparent.symm
    _ =
        (RootFieldCleanCopenBridge.node n a rest).linearEquiv
          (tailRootFieldFromHeadCplus n a C rest root p) tailCopen := hboundary.symm
    _ =
        (tailRootFieldFromHeadCplus n a C rest root p)
          tailSite.nonRootCoord := htail

private theorem eqRec_heq_proofDependent
    {α : Sort u} {a : α}
    {motive : (b : α) → a = b → Sort v}
    (p : motive a rfl) {b : α} (h : a = b) :
    Eq.rec (motive := motive) p h ≍ p := by
  cases h
  exact HEq.rfl

private theorem arrowCongr_finCastEquivOfEqClean_heq
    {n m k : Nat} [NeZero n] (h : m = k)
    (f : Fin m → Rep n) :
    ((finCastEquivOfEqClean h).arrowCongr (Equiv.refl (Rep n))) f ≍ f := by
  cases h
  rfl

private theorem finCast_heq_self {m k : Nat} (h : m = k) (j : Fin m) :
    j ≍ Fin.cast h j := by
  cases h
  rfl

theorem parentNonRootCoordsHeadTailEquiv_symm_head_vertex
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (child : VertexCoordDomainClean n C)
    (tail : CoordsList n rest)
    (v : Vertex C)
    (j : Fin (Vertex.weight v)) :
    ((parentNonRootCoordsHeadTailEquiv n a C rest).symm (child, tail))
      (childVertexAtAsNonRootInNode (a := a)
        ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v)))
      (Fin.cast
        (childVertexAtAsNonRootInNode_weight
          (a := a) ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))).symm
        (Fin.cast
          (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))).symm j)) =
    child v j := by
  let p : NodeChildVertex (C :: rest) :=
    (nodeChildVertexConsEquiv C rest).symm (Sum.inl v)
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
    child v j
  rw [rootFieldDomainCleanEquivNodeChildVertex_symm_apply_child]
  rw [nodeChildVertexCoordsEquivSum_symm_inl]
  rfl

theorem tailParentOtherCoordEquiv_parentCoords_fst
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (child : VertexCoordDomainClean n C)
    (tailCoords : CoordsList n rest)
    (q : NodeChildVertex rest) :
    (tailParentOtherCoordEquiv n a C rest q
      (fun u : OtherNonRootVertexClean (RTree.node a (C :: rest))
          (tailParentTargetVertex a C rest q) =>
        ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
          (child, tailCoords)) u.1)).1 = child := by
  funext v j
  dsimp [tailParentOtherCoordEquiv]
  simp [Equiv.piCongrRight_apply, Equiv.piCongrLeft_apply,
    dependentSumPiEquivProd]
  convert parentNonRootCoordsHeadTailEquiv_symm_head_vertex
    n a C rest child tailCoords v j using 2
  · apply eq_of_heq
    refine HEq.trans (eqRec_heq_proofDependent _ _) ?_
    simpa [tailParentOtherVertexEquiv, tailParentOtherVertexEquivChildSubtype,
      tailParentChildSubtypeEquivSumSubtype, tailSumSubtypeEquiv,
      tailLocalChildSubtypeEquivOtherVertex] using
      arrowCongr_finCastEquivOfEqClean_heq
        (n := n)
        (tailParentOtherVertexEquiv_weight a C rest q
          ((tailParentOtherVertexEquiv a C rest q).symm (Sum.inl v)))
        ((parentNonRootCoordsHeadTailEquiv n a C rest).symm (child, tailCoords)
          (((tailParentOtherVertexEquiv a C rest q).symm (Sum.inl v)).1))

theorem tailParentOtherCoordEquiv_parentCoords_snd
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (child : VertexCoordDomainClean n C)
    (tailCoords : CoordsList n rest)
    (q : NodeChildVertex rest) :
    (tailParentOtherCoordEquiv n a C rest q
      (fun u : OtherNonRootVertexClean (RTree.node a (C :: rest))
          (tailParentTargetVertex a C rest q) =>
        ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
          (child, tailCoords)) u.1)).2 =
      (fun uTail : OtherNonRootVertexClean (RTree.node a rest)
        (tailLocalTargetVertex a rest q) =>
        ((rootFieldDomainCleanEquivCopen_node n a rest).symm tailCoords)
          uTail.1) := by
  funext uTail j
  dsimp [tailParentOtherCoordEquiv]
  simp [Equiv.piCongrRight_apply, Equiv.piCongrLeft_apply,
    dependentSumPiEquivProd]
  let pTail := (nonRootVertexNodeEquivChildVertex a rest) uTail.1
  let jTail : Fin (Vertex.weight pTail.2) :=
    Fin.cast
      (nonRootVertexNodeEquivChildVertex_weight
        (a := a) (cs := rest) uTail.1) j
  have hparent :=
    parentNonRootCoordsHeadTailEquiv_symm_tail
      n a C rest child tailCoords pTail jTail
  convert hparent using 2
  · apply eq_of_heq
    refine heq_of_eq (congr_heq ?_ ?_)
    · refine HEq.trans (eqRec_heq_proofDependent _ _) ?_
      simpa [tailParentOtherVertexEquiv, tailParentOtherVertexEquivChildSubtype,
        tailParentChildSubtypeEquivSumSubtype, tailSumSubtypeEquiv,
        tailLocalChildSubtypeEquivOtherVertex, pTail] using
        arrowCongr_finCastEquivOfEqClean_heq
          (n := n)
          (tailParentOtherVertexEquiv_weight a C rest q
            ((tailParentOtherVertexEquiv a C rest q).symm (Sum.inr uTail)))
          ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
            (child, tailCoords)
            (((tailParentOtherVertexEquiv a C rest q).symm
              (Sum.inr uTail)).1))
    · simp [jTail, pTail]
      exact finCast_heq_self
        (congrArg NonRootVertex.weight
          ((nonRootVertexNodeEquivChildVertex a rest).left_inv
            uTail.1).symm) j

theorem tailParentOtherCoordEquiv_parentCoords
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (child : VertexCoordDomainClean n C)
    (tailCoords : CoordsList n rest)
    (q : NodeChildVertex rest) :
    tailParentOtherCoordEquiv n a C rest q
      (fun u : OtherNonRootVertexClean (RTree.node a (C :: rest))
          (tailParentTargetVertex a C rest q) =>
        ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
          (child, tailCoords)) u.1) =
    (child,
      fun uTail : OtherNonRootVertexClean (RTree.node a rest)
          (tailLocalTargetVertex a rest q) =>
        ((rootFieldDomainCleanEquivCopen_node n a rest).symm tailCoords)
          uTail.1) := by
  apply Prod.ext
  · exact tailParentOtherCoordEquiv_parentCoords_fst
      n a C rest child tailCoords q
  · exact tailParentOtherCoordEquiv_parentCoords_snd
      n a C rest child tailCoords q

theorem normalSiteClean_node_tailEquiv_symm_nonRootCoord
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    ((normalSiteClean_node_tailEquiv n a C rest).symm
      (p, tailSite)).nonRootCoord =
      (parentNonRootCoordsHeadTailEquiv n a C rest).symm
        ((vertexCoordDomainEquivCplus n C).symm p,
          (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
            tailSite.nonRootCoord) := by
  let E := parentNonRootCoordsHeadTailEquiv n a C rest
  let parentSite :=
    (normalSiteClean_node_tailEquiv n a C rest).symm (p, tailSite)
  let P : VertexCoordDomainClean n C × CoordsList n rest :=
    ((vertexCoordDomainEquivCplus n C).symm p,
      (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
        tailSite.nonRootCoord)
  have hpair : E parentSite.nonRootCoord = P := by
    apply Prod.ext
    · apply (vertexCoordDomainEquivCplus n C).injective
      dsimp [P]
      rw [normalSiteClean_node_tailEquiv_symm_headCplus]
      exact ((vertexCoordDomainEquivCplus n C).right_inv p).symm
    · dsimp [P]
      exact normalSiteClean_node_tailEquiv_symm_tailCoords
        n a C rest p tailSite
  calc
    parentSite.nonRootCoord = E.symm (E parentSite.nonRootCoord) := by
      exact (E.left_inv parentSite.nonRootCoord).symm
    _ = E.symm P := by
      rw [hpair]

theorem tailParentTargetVertex_weight_eq_tailLocalTargetVertex_weight
    (a : Nat) (C : RTree) (rest : List RTree)
    (q : NodeChildVertex rest) :
    NonRootVertex.weight (tailParentTargetVertex a C rest q) =
      NonRootVertex.weight (tailLocalTargetVertex a rest q) := by
  simp [tailParentTargetVertex, tailLocalTargetVertex]
  rw [childVertexAtAsNonRootInNode_weight]
  rw [childVertexAtAsNonRootInNode_weight]
  exact nodeChildVertexConsEquiv_weight
    ((nodeChildVertexConsEquiv C rest).symm (Sum.inr q))

theorem tailParentTarget_sum_parentCoords_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (child : VertexCoordDomainClean n C)
    (tailCoords : CoordsList n rest)
    (q : NodeChildVertex rest) :
    (∑ jp : Fin (NonRootVertex.weight
        (tailParentTargetVertex a C rest q)),
      ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
        (child, tailCoords)) (tailParentTargetVertex a C rest q) jp) =
    (∑ jl : Fin (NonRootVertex.weight
        (tailLocalTargetVertex a rest q)),
      ((rootFieldDomainCleanEquivCopen_node n a rest).symm tailCoords)
        (tailLocalTargetVertex a rest q) jl) := by
  let parentChild : NodeChildVertex (C :: rest) :=
    (nodeChildVertexConsEquiv C rest).symm (Sum.inr q)
  let hTarget : NonRootVertex.weight (tailParentTargetVertex a C rest q) =
      Vertex.weight parentChild.2 := by
    dsimp [tailParentTargetVertex, parentChild]
    rw [childVertexAtAsNonRootInNode_weight]
  let hCons : Vertex.weight parentChild.2 = Vertex.weight q.2 := by
    dsimp [parentChild]
    exact nodeChildVertexConsEquiv_weight
      ((nodeChildVertexConsEquiv C rest).symm (Sum.inr q))
  let eParent : Fin (Vertex.weight q.2) ≃
      Fin (NonRootVertex.weight (tailParentTargetVertex a C rest q)) :=
    finCastEquivOfEqClean (hCons.symm.trans hTarget.symm)
  let hLocal : NonRootVertex.weight (tailLocalTargetVertex a rest q) =
      Vertex.weight q.2 := by
    dsimp [tailLocalTargetVertex]
    rw [childVertexAtAsNonRootInNode_weight]
  let eLocal : Fin (Vertex.weight q.2) ≃
      Fin (NonRootVertex.weight (tailLocalTargetVertex a rest q)) :=
    finCastEquivOfEqClean hLocal.symm
  calc
    (∑ jp : Fin (NonRootVertex.weight
        (tailParentTargetVertex a C rest q)),
      ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
        (child, tailCoords)) (tailParentTargetVertex a C rest q) jp) =
      ∑ j : Fin (Vertex.weight q.2),
        ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
          (child, tailCoords)) (tailParentTargetVertex a C rest q)
          (eParent j) := by
        exact
          (Equiv.sum_comp eParent
            (fun jp : Fin (NonRootVertex.weight
                (tailParentTargetVertex a C rest q)) =>
              ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
                (child, tailCoords)) (tailParentTargetVertex a C rest q) jp)).symm
    _ = ∑ j : Fin (Vertex.weight q.2),
        ((nodeChildVertexCoordsEquivCoordsList n rest).symm tailCoords)
          q j := by
        refine Finset.sum_congr rfl ?_
        intro j _
        dsimp [eParent, tailParentTargetVertex, parentChild]
        convert parentNonRootCoordsHeadTailEquiv_symm_tail
          n a C rest child tailCoords q j using 1
    _ = ∑ jl : Fin (NonRootVertex.weight
        (tailLocalTargetVertex a rest q)),
        ((rootFieldDomainCleanEquivCopen_node n a rest).symm tailCoords)
          (tailLocalTargetVertex a rest q) jl := by
        calc
          (∑ j : Fin (Vertex.weight q.2),
            ((nodeChildVertexCoordsEquivCoordsList n rest).symm
              tailCoords) q j) =
            ∑ j : Fin (Vertex.weight q.2),
              ((rootFieldDomainCleanEquivCopen_node n a rest).symm tailCoords)
                (tailLocalTargetVertex a rest q) (eLocal j) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              dsimp [eLocal, tailLocalTargetVertex,
                rootFieldDomainCleanEquivCopen_node]
              exact
                (rootFieldDomainCleanEquivNodeChildVertex_symm_apply_child
                  n a rest
                  ((nodeChildVertexCoordsEquivCoordsList n rest).symm
                    tailCoords) q j).symm
          _ = ∑ jl : Fin (NonRootVertex.weight
              (tailLocalTargetVertex a rest q)),
              ((rootFieldDomainCleanEquivCopen_node n a rest).symm tailCoords)
                (tailLocalTargetVertex a rest q) jl := by
              exact Equiv.sum_comp eLocal
                (fun jl : Fin (NonRootVertex.weight
                    (tailLocalTargetVertex a rest q)) =>
                  ((rootFieldDomainCleanEquivCopen_node n a rest).symm
                    tailCoords) (tailLocalTargetVertex a rest q) jl)

theorem tailParentTarget_diagonal_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (p : Cplus n C)
    (q : NodeChildVertex rest)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    diagonalClean
      ((normalSiteClean_node_tailEquiv n a C rest).symm (p, tailSite))
      (tailParentTargetVertex a C rest q) =
    diagonalClean tailSite (tailLocalTargetVertex a rest q) := by
  unfold diagonalClean
  rw [normalSiteClean_node_tailEquiv_symm_nonRootCoord]
  calc
    (∑ j : Fin (NonRootVertex.weight
        (tailParentTargetVertex a C rest q)),
      ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
        ((vertexCoordDomainEquivCplus n C).symm p,
          (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
            tailSite.nonRootCoord))
        (tailParentTargetVertex a C rest q) j) =
      ∑ j : Fin (NonRootVertex.weight (tailLocalTargetVertex a rest q)),
        ((rootFieldDomainCleanEquivCopen_node n a rest).symm
          ((rootFieldDomainCleanEquivCopen n (RTree.node a rest))
            tailSite.nonRootCoord))
          (tailLocalTargetVertex a rest q) j := by
        exact tailParentTarget_sum_parentCoords_eq_local
          n a C rest ((vertexCoordDomainEquivCplus n C).symm p)
          ((rootFieldDomainCleanEquivCopen n (RTree.node a rest))
            tailSite.nonRootCoord) q
    _ =
      ∑ j : Fin (NonRootVertex.weight (tailLocalTargetVertex a rest q)),
        tailSite.nonRootCoord (tailLocalTargetVertex a rest q) j := by
        change
          (∑ j : Fin (NonRootVertex.weight (tailLocalTargetVertex a rest q)),
            ((rootFieldDomainCleanEquivCopen_node n a rest).symm
              ((rootFieldDomainCleanEquivCopen_node n a rest)
                tailSite.nonRootCoord))
              (tailLocalTargetVertex a rest q) j) =
            ∑ j : Fin (NonRootVertex.weight (tailLocalTargetVertex a rest q)),
              tailSite.nonRootCoord (tailLocalTargetVertex a rest q) j
        refine Finset.sum_congr rfl ?_
        intro j _
        exact congrFun
          (congrFun
            ((rootFieldDomainCleanEquivCopen_node n a rest).left_inv
              tailSite.nonRootCoord)
            (tailLocalTargetVertex a rest q)) j

theorem tail_nonRootDomainOfSite_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (p : Cplus n C)
    (q : NodeChildVertex rest)
    (tailSite : NormalSiteClean n (RTree.node a rest))
    (s : Rep n) :
    nonRootDomainOfSiteClean
      ((normalSiteClean_node_tailEquiv n a C rest).symm (p, tailSite))
      (tailParentTargetVertex a C rest q) s =
    (tailParentFieldDomainEquivCplusLocal n a C rest q).symm
      (p,
        nonRootDomainOfSiteClean tailSite
          (tailLocalTargetVertex a rest q) s) := by
  let parentSite :=
    (normalSiteClean_node_tailEquiv n a C rest).symm (p, tailSite)
  let childCoords := (vertexCoordDomainEquivCplus n C).symm p
  let tailCoords :=
    (rootFieldDomainCleanEquivCopen n (RTree.node a rest))
      tailSite.nonRootCoord
  apply (tailParentFieldDomainEquivCplusLocal n a C rest q).injective
  rw [Equiv.apply_symm_apply]
  dsimp [tailParentFieldDomainEquivCplusLocal, tailParentFieldDomainRawEquiv,
    nonRootDomainOfSiteClean]
  apply Prod.ext
  · dsimp [parentSite, childCoords, tailCoords]
    rw [normalSiteClean_node_tailEquiv_symm_nonRootCoord]
    rw [tailParentOtherCoordEquiv_parentCoords_fst]
    exact (vertexCoordDomainEquivCplus n C).right_inv p
  · rw [NonRootFieldDomainClean.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · exact normalSiteClean_node_tailEquiv_symm_rootCoord
        n a C rest p tailSite
    · exact congrArg (fun x : Rep n => x + s)
        (tailParentTarget_diagonal_eq_local n a C rest p q tailSite)
    · funext uTail j
      dsimp [parentSite, childCoords, tailCoords]
      rw [normalSiteClean_node_tailEquiv_symm_nonRootCoord]
      rw [tailParentOtherCoordEquiv_parentCoords_snd]
      change
        ((rootFieldDomainCleanEquivCopen_node n a rest).symm
          ((rootFieldDomainCleanEquivCopen_node n a rest)
            tailSite.nonRootCoord)) uTail.1 j =
          tailSite.nonRootCoord uTail.1 j
      exact congrFun
        (congrFun
          ((rootFieldDomainCleanEquivCopen_node n a rest).left_inv
            tailSite.nonRootCoord) uTail.1) j

theorem parent_tail_childField_eq_local_tail_childField
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (q : NodeChildVertex rest)
    (localDom :
      NonRootFieldDomainClean n (RTree.node a rest)
        (childVertexAtAsNonRootInNode (a := a) q)) :
    ((openNormalAssignmentCleanEquivHeadTail n a C rest)
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))).2 q
      ((tailParentFieldDomainEquivCplusLocal n a C rest q).symm
        (p, localDom)) =
    ((openNormalAssignmentCleanEquivParentOpenByChild n a rest)
      ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      q localDom := by
  calc
    ((openNormalAssignmentCleanEquivHeadTail n a C rest)
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))).2 q
      ((tailParentFieldDomainEquivCplusLocal n a C rest q).symm
        (p, localDom)) =
        tail q
          ((tailParentFieldDomainEquivCplusLocal n a C rest q).symm
            (p, localDom)) := by
          exact openNormalAssignmentCleanEquivHeadTail_symm_apply_tail
            n a C rest head tail q
            ((tailParentFieldDomainEquivCplusLocal n a C rest q).symm
              (p, localDom))
    _ =
        ((openNormalAssignmentCleanEquivParentOpenByChild n a rest)
          ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
          q localDom := by
          exact
            (parentOpenTailFieldsEquivTailOpenByCplus_apply
              n a C rest tail p q localDom).symm

theorem parent_tail_nodeField_eq_local_tail_nodeField
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (q : NodeChildVertex rest)
    (localDom :
      NonRootFieldDomainClean n (RTree.node a rest)
        (childVertexAtAsNonRootInNode (a := a) q)) :
    ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)).nodeField
      (tailParentTargetVertex a C rest q)
      ((tailParentFieldDomainEquivCplusLocal n a C rest q).symm
        (p, localDom)) =
    ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p).nodeField
      (tailLocalTargetVertex a rest q)
      localDom := by
  let Aopen :=
    (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)
  let parentChild := (nodeChildVertexConsEquiv C rest).symm (Sum.inr q)
  let parentDom :=
    (tailParentFieldDomainEquivCplusLocal n a C rest q).symm
      (p, localDom)
  let localOpen :=
    (parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p
  change
    Aopen.nodeField (childVertexAtAsNonRootInNode (a := a) parentChild)
        parentDom =
      localOpen.nodeField (childVertexAtAsNonRootInNode (a := a) q)
        localDom
  calc
    Aopen.nodeField (childVertexAtAsNonRootInNode (a := a) parentChild)
        parentDom =
        ((openNormalAssignmentCleanEquivParentOpenByChild n a (C :: rest))
          Aopen) parentChild parentDom := by
          exact
            (openNormalAssignmentCleanEquivParentOpenByChild_apply
              n a (C :: rest) Aopen parentChild parentDom).symm
    _ =
        ((openNormalAssignmentCleanEquivHeadTail n a C rest) Aopen).2 q
          parentDom := by
          rfl
    _ =
        ((openNormalAssignmentCleanEquivParentOpenByChild n a rest)
          localOpen) q localDom := by
          exact parent_tail_childField_eq_local_tail_childField
            n a C rest head tail p q localDom
    _ =
        localOpen.nodeField (childVertexAtAsNonRootInNode (a := a) q)
          localDom := by
          exact openNormalAssignmentCleanEquivParentOpenByChild_apply
            n a rest localOpen q localDom

theorem tail_rootKetAtPath_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    ketAtPathClean
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) [] =
    ketAtPathClean
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      tailSite [] := by
  unfold ketAtPathClean
  simp [ketAtVertexClean]
  dsimp [closeOpenNormalAssignmentClean]
  exact tailRootFieldFromHeadCplus_eval_tailSite
    n a C rest root p tailSite

theorem tail_rootBraAtPath_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    braAtPathClean
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) [] =
    braAtPathClean
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      tailSite [] := by
  unfold braAtPathClean
  simp [braAtVertexClean]
  dsimp [closeOpenNormalAssignmentClean]
  exact tailRootFieldFromHeadCplus_eval_tailSite
    n a C rest root p tailSite

theorem tail_childKetAtPath_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest))
    (j : Fin rest.length)
    (v : Vertex (childAt rest j)) :
    ketAtPathClean
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) (j.succ.1 :: v.1) =
    ketAtPathClean
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      tailSite (j.1 :: v.1) := by
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  let B :=
    closeOpenNormalAssignmentClean
      (tailRootFieldFromHeadCplus n a C rest root p)
      ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p)
  let q : NodeChildVertex rest := ⟨j, v⟩
  have hparentMem :
      j.succ.1 :: v.1 ∈ RTree.addresses (RTree.node a (C :: rest)) := by
    have hget := childAt_get?_eq_some (C :: rest) j.succ
    rw [childAt_cons_succ] at hget
    exact RTree.childAddress_mem_addresses_node_of_get? (a := a) hget v.2
  have hlocalMem :
      j.1 :: v.1 ∈ RTree.addresses (RTree.node a rest) := by
    exact RTree.childAddress_mem_addresses_node_of_get? (a := a)
      (childAt_get?_eq_some rest j) v.2
  let vParent : NonRootVertex (RTree.node a (C :: rest)) :=
    ⟨⟨j.succ.1 :: v.1, hparentMem⟩, by simp⟩
  let vLocal : NonRootVertex (RTree.node a rest) :=
    ⟨⟨j.1 :: v.1, hlocalMem⟩, by simp⟩
  have hvParent : vParent = tailParentTargetVertex a C rest q := by
    apply Subtype.ext
    apply Subtype.ext
    change (j.1 + 1) :: v.1 = (j.1 + 1) :: v.1
    rfl
  have hvLocal : vLocal = tailLocalTargetVertex a rest q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  change
    ketAtPathClean A ((normalSiteClean_node_tailEquiv n a C rest).symm
      (p, tailSite)) (j.succ.1 :: v.1) =
    ketAtPathClean B tailSite (j.1 :: v.1)
  unfold ketAtPathClean
  rw [dif_pos hparentMem, dif_pos hlocalMem]
  change
    ketAtVertexClean A
      ((normalSiteClean_node_tailEquiv n a C rest).symm (p, tailSite))
      vParent =
    ketAtVertexClean B tailSite vLocal
  rw [hvParent, hvLocal]
  simp [ketAtVertexClean]
  dsimp [A, B, closeOpenNormalAssignmentClean]
  rw [tail_nonRootDomainOfSite_eq_local]
  exact parent_tail_nodeField_eq_local_tail_nodeField
    n a C rest head tail p q
    (nonRootDomainOfSiteClean tailSite (tailLocalTargetVertex a rest q) 0)

theorem tail_childBraAtPath_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest))
    (j : Fin rest.length)
    (v : Vertex (childAt rest j)) :
    braAtPathClean
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) (j.succ.1 :: v.1) =
    braAtPathClean
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      tailSite (j.1 :: v.1) := by
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  let B :=
    closeOpenNormalAssignmentClean
      (tailRootFieldFromHeadCplus n a C rest root p)
      ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p)
  let q : NodeChildVertex rest := ⟨j, v⟩
  have hparentMem :
      j.succ.1 :: v.1 ∈ RTree.addresses (RTree.node a (C :: rest)) := by
    have hget := childAt_get?_eq_some (C :: rest) j.succ
    rw [childAt_cons_succ] at hget
    exact RTree.childAddress_mem_addresses_node_of_get? (a := a) hget v.2
  have hlocalMem :
      j.1 :: v.1 ∈ RTree.addresses (RTree.node a rest) := by
    exact RTree.childAddress_mem_addresses_node_of_get? (a := a)
      (childAt_get?_eq_some rest j) v.2
  let vParent : NonRootVertex (RTree.node a (C :: rest)) :=
    ⟨⟨j.succ.1 :: v.1, hparentMem⟩, by simp⟩
  let vLocal : NonRootVertex (RTree.node a rest) :=
    ⟨⟨j.1 :: v.1, hlocalMem⟩, by simp⟩
  have hvParent : vParent = tailParentTargetVertex a C rest q := by
    apply Subtype.ext
    apply Subtype.ext
    change (j.1 + 1) :: v.1 = (j.1 + 1) :: v.1
    rfl
  have hvLocal : vLocal = tailLocalTargetVertex a rest q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  change
    braAtPathClean A ((normalSiteClean_node_tailEquiv n a C rest).symm
      (p, tailSite)) (j.succ.1 :: v.1) =
    braAtPathClean B tailSite (j.1 :: v.1)
  unfold braAtPathClean
  rw [dif_pos hparentMem, dif_pos hlocalMem]
  change
    braAtVertexClean A
      ((normalSiteClean_node_tailEquiv n a C rest).symm (p, tailSite))
      vParent =
    braAtVertexClean B tailSite vLocal
  rw [hvParent, hvLocal]
  simp [braAtVertexClean]
  dsimp [A, B, closeOpenNormalAssignmentClean]
  rw [tail_nonRootDomainOfSite_eq_local]
  exact parent_tail_nodeField_eq_local_tail_nodeField
    n a C rest head tail p q
    (nonRootDomainOfSiteClean tailSite (tailLocalTargetVertex a rest q) 1)

theorem tail_childBoundaryPhaseAtSite_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest))
    (j : Fin rest.length) :
    childBoundaryPhaseAtSiteClean_node
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) j.succ =
    childBoundaryPhaseAtSiteClean_node
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      tailSite j := by
  unfold childBoundaryPhaseAtSiteClean_node edgePhaseAtSiteClean
  have hkRoot :=
    tail_rootKetAtPath_eq_local n a C rest root head tail p tailSite
  have hkChild :
      ketAtPathClean
        (closeOpenNormalAssignmentClean root
          ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
            (head, tail)))
        ((normalSiteClean_node_tailEquiv n a C rest).symm
          (p, tailSite)) [j.succ.1] =
      ketAtPathClean
        (closeOpenNormalAssignmentClean
          (tailRootFieldFromHeadCplus n a C rest root p)
          ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
        tailSite [j.1] := by
    simpa [Vertex.root] using
      tail_childKetAtPath_eq_local n a C rest root head tail p tailSite
        j (Vertex.root (childAt rest j))
  have hbRoot :=
    tail_rootBraAtPath_eq_local n a C rest root head tail p tailSite
  have hbChild :
      braAtPathClean
        (closeOpenNormalAssignmentClean root
          ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
            (head, tail)))
        ((normalSiteClean_node_tailEquiv n a C rest).symm
          (p, tailSite)) [j.succ.1] =
      braAtPathClean
        (closeOpenNormalAssignmentClean
          (tailRootFieldFromHeadCplus n a C rest root p)
          ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
        tailSite [j.1] := by
    simpa [Vertex.root] using
      tail_childBraAtPath_eq_local n a C rest root head tail p tailSite
        j (Vertex.root (childAt rest j))
  rw [hkRoot, hkChild, hbRoot, hbChild]

theorem tail_childEdgePhase_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest))
    (j : Fin rest.length)
    (e : List Nat × List Nat)
    (he : e ∈ RTree.edgeList (childAt rest j)) :
    edgePhaseAtSiteClean
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) (RTree.prefixEdge [j.succ.1] e) =
    edgePhaseAtSiteClean
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      tailSite (RTree.prefixEdge [j.1] e) := by
  cases e with
  | mk u v =>
      have hu : u ∈ RTree.addresses (childAt rest j) :=
        RTree.edgeList_edge_left_mem_addresses (childAt rest j) he
      have hv : v ∈ RTree.addresses (childAt rest j) :=
        RTree.edgeList_edge_right_mem_addresses (childAt rest j) he
      simp [RTree.prefixEdge, edgePhaseAtSiteClean]
      have hku :
          ketAtPathClean
            (closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
                (head, tail)))
            ((normalSiteClean_node_tailEquiv n a C rest).symm
              (p, tailSite)) ((j.1 + 1) :: u) =
          ketAtPathClean
            (closeOpenNormalAssignmentClean
              (tailRootFieldFromHeadCplus n a C rest root p)
              ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
            tailSite (j.1 :: u) := by
        simpa using
          tail_childKetAtPath_eq_local n a C rest root head tail p tailSite
            j ⟨u, hu⟩
      have hkv :
          ketAtPathClean
            (closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
                (head, tail)))
            ((normalSiteClean_node_tailEquiv n a C rest).symm
              (p, tailSite)) ((j.1 + 1) :: v) =
          ketAtPathClean
            (closeOpenNormalAssignmentClean
              (tailRootFieldFromHeadCplus n a C rest root p)
              ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
            tailSite (j.1 :: v) := by
        simpa using
          tail_childKetAtPath_eq_local n a C rest root head tail p tailSite
            j ⟨v, hv⟩
      have hbu :
          braAtPathClean
            (closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
                (head, tail)))
            ((normalSiteClean_node_tailEquiv n a C rest).symm
              (p, tailSite)) ((j.1 + 1) :: u) =
          braAtPathClean
            (closeOpenNormalAssignmentClean
              (tailRootFieldFromHeadCplus n a C rest root p)
              ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
            tailSite (j.1 :: u) := by
        simpa using
          tail_childBraAtPath_eq_local n a C rest root head tail p tailSite
            j ⟨u, hu⟩
      have hbv :
          braAtPathClean
            (closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
                (head, tail)))
            ((normalSiteClean_node_tailEquiv n a C rest).symm
              (p, tailSite)) ((j.1 + 1) :: v) =
          braAtPathClean
            (closeOpenNormalAssignmentClean
              (tailRootFieldFromHeadCplus n a C rest root p)
              ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
            tailSite (j.1 :: v) := by
        simpa using
          tail_childBraAtPath_eq_local n a C rest root head tail p tailSite
            j ⟨v, hv⟩
      rw [hku, hkv, hbu, hbv]

theorem tail_childInternalPhaseAtSite_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest))
    (j : Fin rest.length) :
    childInternalPhaseAtSiteClean_node
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) j.succ =
    childInternalPhaseAtSiteClean_node
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      tailSite j := by
  unfold childInternalPhaseAtSiteClean_node
  rw [childAt_cons_succ]
  have hparent :
      RTree.edgeListFrom [j.succ.1] (childAt rest j) =
        (RTree.edgeList (childAt rest j)).map
          (RTree.prefixEdge [j.succ.1]) := by
    simpa [RTree.edgeList] using
      (RTree.edgeListFrom_append_parent [j.succ.1] [] (childAt rest j))
  have hlocal :
      RTree.edgeListFrom [j.1] (childAt rest j) =
        (RTree.edgeList (childAt rest j)).map
          (RTree.prefixEdge [j.1]) := by
    simpa [RTree.edgeList] using
      (RTree.edgeListFrom_append_parent [j.1] [] (childAt rest j))
  rw [hparent, hlocal]
  simp [List.map_map, Function.comp_def]
  rw [List.map_congr_left]
  intro e he
  exact tail_childEdgePhase_eq_local
    n a C rest root head tail p tailSite j e he

theorem tailBoundaryPhaseAtTailSite_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    tailBoundaryPhaseAtSiteClean_node C rest
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) =
    boundaryPhaseAtSiteClean_node
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      tailSite := by
  rw [boundaryPhaseAtSiteClean_node_eq_sum_child n a rest]
  unfold tailBoundaryPhaseAtSiteClean_node
  refine Finset.sum_congr rfl ?_
  intro j _
  exact tail_childBoundaryPhaseAtSite_eq_local
    n a C rest root head tail p tailSite j

theorem tailInternalPhaseAtTailSite_eq_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    tailInternalPhaseAtSiteClean_node C rest
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) =
    internalPhaseAtSiteClean_node
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      tailSite := by
  rw [internalPhaseAtSiteClean_node_eq_sum_child n a rest]
  unfold tailInternalPhaseAtSiteClean_node
  refine Finset.sum_congr rfl ?_
  intro j _
  exact tail_childInternalPhaseAtSite_eq_local
    n a C rest root head tail p tailSite j

theorem tailPhaseAtTailSite_eq_tailLocalPhase
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (p : Cplus n C)
    (tailSite : NormalSiteClean n (RTree.node a rest)) :
    tailBoundaryPhaseAtSiteClean_node C rest
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) +
    tailInternalPhaseAtSiteClean_node C rest
      (closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)))
      ((normalSiteClean_node_tailEquiv n a C rest).symm
        (p, tailSite)) =
    phaseAtSiteClean (RTree.node a rest)
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
      tailSite := by
  rw [tailBoundaryPhaseAtTailSite_eq_local]
  rw [tailInternalPhaseAtTailSite_eq_local]
  exact (phaseAtSiteClean_node_eq_boundary_add_internal n a rest
    (closeOpenNormalAssignmentClean
      (tailRootFieldFromHeadCplus n a C rest root p)
      ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))
    tailSite).symm

theorem totalTailPhaseClean_node_eq_sum_tail_totalPhase_of_site
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (B : Cplus n C → NormalAssignmentClean n (RTree.node a rest))
    (hsite :
      ∀ p : Cplus n C,
        ∀ tailSite : NormalSiteClean n (RTree.node a rest),
          tailBoundaryPhaseAtSiteClean_node C rest A
              ((normalSiteClean_node_tailEquiv n a C rest).symm
                (p, tailSite)) +
            tailInternalPhaseAtSiteClean_node C rest A
              ((normalSiteClean_node_tailEquiv n a C rest).symm
                (p, tailSite)) =
            phaseAtSiteClean (RTree.node a rest) (B p) tailSite) :
    totalTailPhaseClean_node n a C rest A =
      ∑ p : Cplus n C,
        totalPhaseClean (RTree.node a rest) (B p) := by
  classical
  unfold totalTailPhaseClean_node totalTailBoundaryPhaseClean_node
    totalTailInternalPhaseClean_node totalPhaseClean
  rw [← Finset.sum_add_distrib]
  let e := normalSiteClean_node_tailEquiv n a C rest
  let f : NormalSiteClean n (RTree.node a (C :: rest)) → F2 :=
    fun site =>
      tailBoundaryPhaseAtSiteClean_node C rest A site +
        tailInternalPhaseAtSiteClean_node C rest A site
  let g : Cplus n C × NormalSiteClean n (RTree.node a rest) → F2 :=
    fun P => f (e.symm P)
  calc
    (∑ site : NormalSiteClean n (RTree.node a (C :: rest)), f site) =
        ∑ P : Cplus n C × NormalSiteClean n (RTree.node a rest), g P := by
          exact
            (Equiv.sum_comp e.symm
              f).symm
    _ =
        ∑ p : Cplus n C,
          ∑ tailSite : NormalSiteClean n (RTree.node a rest),
            g (p, tailSite) := by
          exact Fintype.sum_prod_type g
    _ =
        ∑ p : Cplus n C,
          ∑ tailSite : NormalSiteClean n (RTree.node a rest),
            phaseAtSiteClean (RTree.node a rest) (B p) tailSite := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro tailSite _
          exact hsite p tailSite

theorem parentTailPhaseSiteProductAtHeadTail_eq_tailOpenProductAtCplus_of_site
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (hsite :
      ∀ p : Cplus n C,
        ∀ tailSite : NormalSiteClean n (RTree.node a rest),
          let A :=
            closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
                (head, tail))
          let B :=
            closeOpenNormalAssignmentClean
              (tailRootFieldFromHeadCplus n a C rest root p)
              ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p)
          tailBoundaryPhaseAtSiteClean_node C rest A
              ((normalSiteClean_node_tailEquiv n a C rest).symm
                (p, tailSite)) +
            tailInternalPhaseAtSiteClean_node C rest A
              ((normalSiteClean_node_tailEquiv n a C rest).symm
                (p, tailSite)) =
            phaseAtSiteClean (RTree.node a rest) B tailSite) :
    parentTailPhaseSiteProductAtHeadTail n a C rest root head tail =
      tailOpenProductAtCplus n a C rest root tail := by
  classical
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  let B : Cplus n C → NormalAssignmentClean n (RTree.node a rest) :=
    fun p =>
      closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p)
  have htotal :
      totalTailPhaseClean_node n a C rest A =
        ∑ p : Cplus n C,
          totalPhaseClean (RTree.node a rest) (B p) := by
    refine totalTailPhaseClean_node_eq_sum_tail_totalPhase_of_site
      n a C rest A B ?_
    intro p tailSite
    exact hsite p tailSite
  calc
    parentTailPhaseSiteProductAtHeadTail n a C rest root head tail =
        chi (totalTailPhaseClean_node n a C rest A) := by
          exact
            (chi_totalTailPhaseClean_node_eq_parentTailPhaseSiteProductAtHeadTail
              n a C rest root head tail).symm
    _ =
        chi (∑ p : Cplus n C,
          totalPhaseClean (RTree.node a rest) (B p)) := by
          rw [htotal]
    _ =
        ∏ p : Cplus n C,
          chi (totalPhaseClean (RTree.node a rest) (B p)) := by
          rw [chi_sum_univ_apply]
    _ = tailOpenProductAtCplus n a C rest root tail := by
          rfl

theorem parentTailPhaseSiteProductAtHeadTail_eq_tailOpenProductAtCplus
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) :
    parentTailPhaseSiteProductAtHeadTail n a C rest root head tail =
      tailOpenProductAtCplus n a C rest root tail := by
  refine parentTailPhaseSiteProductAtHeadTail_eq_tailOpenProductAtCplus_of_site
    n a C rest root head tail ?_
  intro p tailSite
  exact tailPhaseAtTailSite_eq_tailLocalPhase
    n a C rest root head tail p tailSite

theorem parentOpenTailPhaseSignedSumAtHead_eq_prod_tailOpenAtCplus
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) :
    parentOpenTailPhaseSignedSumAtHead n a C rest root head =
      ∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p) := by
  refine parentOpenTailPhaseSignedSumAtHead_eq_prod_tailOpenAtCplus_of_phaseProduct
    n a C rest root head ?_
  intro tail
  exact parentTailPhaseSiteProductAtHeadTail_eq_tailOpenProductAtCplus
    n a C rest root head tail

end Imbalance
end TreeGraph
