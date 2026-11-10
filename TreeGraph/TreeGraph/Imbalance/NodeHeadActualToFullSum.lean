import TreeGraph.Imbalance.NodeHeadSiteShear
import TreeGraph.Imbalance.NodeHeadSumReduction
import TreeGraph.Imbalance.NodeHeadBoundaryCyclic

namespace TreeGraph
namespace Imbalance

theorem nonRootFieldDomainClean_ext_apply
    {n : Nat} [NeZero n] {T : RTree} {v : NonRootVertex T}
    {D E : NonRootFieldDomainClean n T v}
    (hroot : D.rootCoord = E.rootCoord)
    (hdiag : D.diagonal = E.diagonal)
    (hother : ∀ u j, D.otherCoord u j = E.otherCoord u j) :
    D = E := by
  cases D with
  | mk rootCoord diagonal otherCoord =>
      cases E with
      | mk rootCoord' diagonal' otherCoord' =>
          simp only at hroot hdiag hother
          rw [NonRootFieldDomainClean.mk.injEq]
          exact ⟨hroot, hdiag, funext (fun u => funext (hother u))⟩

theorem openNormalAssignmentCleanEquivHeadTail_symm_nodeField_head_root
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))) :
    ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)).nodeField
        (headChildRootNonRootInParent
          (a := a) (C := C) (rest := rest)) dom =
      head (Vertex.root C) dom := by
  unfold openNormalAssignmentCleanEquivHeadTail
  change
    (((openNormalAssignmentCleanEquivParentOpenByChild n a
          (C :: rest)).symm
      ((parentOpenByChildConsEquiv n a C rest).symm
        (head, tail))).nodeField
        (childVertexAtAsNonRootInNode (a := a)
          ((nodeChildVertexConsEquiv C rest).symm
            (Sum.inl (Vertex.root C)))) dom) =
      head (Vertex.root C) dom
  rw [openNormalAssignmentCleanEquivParentOpenByChild_symm_nodeField]
  simp [parentOpenByChildConsEquiv, parentOpenByChildConsEquivSum,
    dependentSumPiEquivProd]

theorem openNormalAssignmentCleanEquivHeadTail_symm_nodeField_head_vertex
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (v : Vertex C)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (childVertexAtAsNonRootInNode (a := a)
        ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v)))) :
    ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)).nodeField
        (childVertexAtAsNonRootInNode (a := a)
          ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))) dom =
      head v dom := by
  unfold openNormalAssignmentCleanEquivHeadTail
  change
    (((openNormalAssignmentCleanEquivParentOpenByChild n a
          (C :: rest)).symm
      ((parentOpenByChildConsEquiv n a C rest).symm
        (head, tail))).nodeField
        (childVertexAtAsNonRootInNode (a := a)
          ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))) dom) =
      head v dom
  rw [openNormalAssignmentCleanEquivParentOpenByChild_symm_nodeField]
  simp [parentOpenByChildConsEquiv, parentOpenByChildConsEquivSum,
    dependentSumPiEquivProd]

theorem openNormalAssignmentCleanEquivHeadTail_symm_nodeField_head_nonroot
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)) :
    ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)).nodeField
        (headChildNonRootInParent (a := a) (C := C) (rest := rest) v) dom =
      head v.1 dom := by
  change
    ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)).nodeField
        (childVertexAtAsNonRootInNode (a := a)
          ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v.1))) dom =
      head v.1 dom
  exact openNormalAssignmentCleanEquivHeadTail_symm_nodeField_head_vertex
    n a C rest head tail v.1 dom

theorem headChildRootBoundaryFieldFromParent_headChildOpenData
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (q : Block n (a - 1))
    (tailIdx : CoordsList n rest)
    (s : Rep n) (y : Copen n C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    headChildRootBoundaryFieldFromParent n a C rest hC Aopen q tailIdx s y =
      P.rootCopenBridge.linearEquiv (data (q, tailIdx, s)).1 y := by
  intro head Aopen
  unfold headChildRootBoundaryFieldFromParent
  rw [openNormalAssignmentCleanEquivHeadTail_symm_nodeField_head_root]
  change head (Vertex.root C)
      (headChildRootDomainFromHeadIndexCopen
        n a C rest (q, tailIdx, s) y) =
    P.rootCopenBridge.linearEquiv (data (q, tailIdx, s)).1 y
  exact parentOpenHeadFieldsEquivHeadChildOpenData_symm_apply_root
    n a C rest hC P data (q, tailIdx, s) y

theorem headBoundaryOpenPairingDataExpressionAtSite_headDiagIndex_data
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let y := (rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord
    headBoundaryOpenPairingDataExpressionAtSite
        n a C rest hC root Aopen site =
      headBoundaryParentRootKet (closeOpenNormalAssignmentClean root Aopen)
          site *
        P.rootCopenBridge.linearEquiv
          (data
            (headChildIndexParentRoot idx,
              headChildIndexTail idx,
              headChildIndexRootDiag idx)).1 y +
      headBoundaryParentRootBra (closeOpenNormalAssignmentClean root Aopen)
          site *
        P.rootCopenBridge.linearEquiv
          (data
            (headChildIndexParentRoot idx,
              headChildIndexTail idx,
              headChildIndexRootDiag idx + 1)).1 y := by
  intro head Aopen site y
  rw [headBoundaryOpenPairingDataExpressionAtSite_headDiagIndexEquiv_symm]
  rw [headChildRootBoundaryFieldFromParent_headChildOpenData
    n a C rest hC P data tail
    (headChildIndexParentRoot idx) (headChildIndexTail idx)
    (headChildIndexRootDiag idx) y]
  rw [headChildRootBoundaryFieldFromParent_headChildOpenData
    n a C rest hC P data tail
    (headChildIndexParentRoot idx) (headChildIndexTail idx)
    (headChildIndexRootDiag idx + 1) y]

theorem headBoundaryOpenPairingDataExpressionAtSite_headDiagIndex_data_parentRoot_mul
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let y := (rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord
    headBoundaryOpenPairingDataExpressionAtSite
        n a C rest hC root Aopen site =
      headBoundaryParentRootKet (closeOpenNormalAssignmentClean root Aopen)
          site *
        (P.rootCopenBridge.linearEquiv
            (data
              (headChildIndexParentRoot idx,
                headChildIndexTail idx,
                headChildIndexRootDiag idx)).1 y +
          P.rootCopenBridge.linearEquiv
            (data
              (headChildIndexParentRoot idx,
                headChildIndexTail idx,
                headChildIndexRootDiag idx + 1)).1 y) := by
  intro head Aopen site y
  rw [headBoundaryOpenPairingDataExpressionAtSite_headDiagIndex_data]
  rw [← headBoundaryParentRootKet_eq_parentRootBra n a C rest]
  rw [← mul_add]

theorem headBoundaryExtraRootCoord_eq_childFull_fst
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryExtraRootCoord n a C rest hC site =
      (vertexCoordDomainEquivExtraSite n C hC
        ((parentNonRootCoordsHeadTailEquiv n a C rest)
          site.nonRootCoord).1).1 := by
  unfold headBoundaryExtraRootCoord headChildSiteContextOfParent
    normalSiteClean_node_headEquiv
  change (((parentSiteHeadChildComponentsEquiv n a C rest hC)
    (((Equiv.refl (Block n (a - 1))).prodCongr
      (parentNonRootCoordsHeadTailEquiv n a C rest))
        ((normalSiteCleanEquivRootNonRoot n (RTree.node a (C :: rest)))
          site))).1).2.1 =
      (vertexCoordDomainEquivExtraSite n C hC
        ((parentNonRootCoordsHeadTailEquiv n a C rest)
          site.nonRootCoord).1).1
  simp [normalSiteCleanEquivRootNonRoot,
    parentSiteHeadChildComponentsEquiv]

theorem vertexCoordDomainEquivCplus_headDiagIndexEquiv_symm_node
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n (RTree.node b ds)) :
    (vertexCoordDomainEquivCplus n (RTree.node b ds))
      ((parentNonRootCoordsHeadTailEquiv n a (RTree.node b ds) rest)
        (((normalSiteClean_node_headDiagIndexEquiv
          n a (RTree.node b ds) rest hC).symm
            (idx, childSite)).nonRootCoord)).1 =
      (((blockSplitDiagEquiv n b
            (rootWeight_pos_of_positiveWeights hC)).symm
          (childSite.rootCoord, headChildIndexRootDiag idx)),
        (rootFieldDomainCleanEquivCopen n (RTree.node b ds))
          childSite.nonRootCoord) := by
  let site :=
    (normalSiteClean_node_headDiagIndexEquiv
      n a (RTree.node b ds) rest hC).symm (idx, childSite)
  change
    (vertexCoordDomainEquivCplus n (RTree.node b ds))
      ((parentNonRootCoordsHeadTailEquiv n a (RTree.node b ds) rest)
        site.nonRootCoord).1 = _
  let childFull :=
    ((parentNonRootCoordsHeadTailEquiv n a (RTree.node b ds) rest)
      site.nonRootCoord).1
  have hextra0 :=
    headBoundaryExtraRootCoord_eq_childFull_fst
      n a (RTree.node b ds) rest hC site
  have hsite0 :=
    headChildLocalSiteOfParent_eq_childFull_snd
      n a (RTree.node b ds) rest hC site
  have hextra1 :=
    headBoundaryExtraRootCoord_headDiagIndexEquiv_symm
      n a (RTree.node b ds) rest hC idx childSite
  have hsite1 :=
    headChildLocalSiteOfParent_headDiagIndexEquiv_symm
      n a (RTree.node b ds) rest hC idx childSite
  have hfst :
      (vertexCoordDomainEquivExtraSite
        n (RTree.node b ds) hC childFull).1 =
        headChildIndexRootDiag idx -
          ∑ i : Fin ((RTree.node b ds).rootWeight - 1),
            childSite.rootCoord i := by
    dsimp [childFull]
    rw [← hextra0]
    exact hextra1
  have hsnd :
      (vertexCoordDomainEquivExtraSite
        n (RTree.node b ds) hC childFull).2 = childSite := by
    dsimp [childFull]
    rw [← hsite0]
    exact hsite1
  have hpair :
      vertexCoordDomainEquivExtraSite
          n (RTree.node b ds) hC childFull =
        (headChildIndexRootDiag idx -
            ∑ i : Fin ((RTree.node b ds).rootWeight - 1),
              childSite.rootCoord i,
          childSite) := by
    exact Prod.ext hfst hsnd
  have hcplus0 := congrArg
    (fun P =>
      (splitFullRootOpenEquivExtraSite
        n b ds (rootWeight_pos_of_positiveWeights hC)).symm P)
    hpair
  dsimp [vertexCoordDomainEquivExtraSite] at hcplus0
  have hconj :
      ((vertexCoordDomainEquivCplus n (RTree.node b ds))
          childFull).1 =
          (blockSplitLastEquiv n b
            (rootWeight_pos_of_positiveWeights hC)).symm
            (childSite.rootCoord,
              headChildIndexRootDiag idx -
                ∑ i, childSite.rootCoord i) ∧
        (rootFieldDomainCleanEquivCopen_node n b ds).symm
            (((vertexCoordDomainEquivCplus n (RTree.node b ds))
              childFull).2) =
          childSite.nonRootCoord := by
    simpa [splitFullRootOpenEquivExtraSite,
      rootFieldDomainCleanEquivCopen, blockSplitDiagEquiv,
      blockLastToDiagPairEquiv, headChildIndexRootDiag] using hcplus0
  have h2 :
      ((vertexCoordDomainEquivCplus n (RTree.node b ds))
          childFull).2 =
        (rootFieldDomainCleanEquivCopen_node n b ds)
          childSite.nonRootCoord := by
    have hh :=
      congrArg (rootFieldDomainCleanEquivCopen_node n b ds) hconj.2
    simpa using hh
  have hcplus :
      (vertexCoordDomainEquivCplus n (RTree.node b ds)) childFull =
        ((blockSplitLastEquiv n b
            (rootWeight_pos_of_positiveWeights hC)).symm
          (childSite.rootCoord,
            headChildIndexRootDiag idx -
              ∑ i, childSite.rootCoord i),
        (rootFieldDomainCleanEquivCopen_node n b ds)
          childSite.nonRootCoord) := by
    exact Prod.ext hconj.1 h2
  simpa [childFull, rootFieldDomainCleanEquivCopen,
    blockSplitDiagEquiv, blockLastToDiagPairEquiv,
    headChildIndexRootDiag] using hcplus

theorem rootFieldDomainCleanEquivCopen_headDiagIndexEquiv_symm_node
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n (RTree.node b ds)) :
    (rootFieldDomainCleanEquivCopen_node
        n a (RTree.node b ds :: rest))
      (((normalSiteClean_node_headDiagIndexEquiv
        n a (RTree.node b ds) rest hC).symm
          (idx, childSite)).nonRootCoord) =
      ((((blockSplitDiagEquiv n b
            (rootWeight_pos_of_positiveWeights hC)).symm
          (childSite.rootCoord, headChildIndexRootDiag idx)),
        (rootFieldDomainCleanEquivCopen n (RTree.node b ds))
          childSite.nonRootCoord),
        headChildIndexTail idx) := by
  let site :=
    (normalSiteClean_node_headDiagIndexEquiv
      n a (RTree.node b ds) rest hC).symm (idx, childSite)
  change
    (rootFieldDomainCleanEquivCopen_node
        n a (RTree.node b ds :: rest)) site.nonRootCoord = _
  change
    ((vertexCoordDomainEquivCplus n (RTree.node b ds))
        ((parentNonRootCoordsHeadTailEquiv
          n a (RTree.node b ds) rest) site.nonRootCoord).1,
      ((parentNonRootCoordsHeadTailEquiv
        n a (RTree.node b ds) rest) site.nonRootCoord).2) = _
  apply Prod.ext
  · exact vertexCoordDomainEquivCplus_headDiagIndexEquiv_symm_node
      n a b ds rest hC idx childSite
  · have htail0 :=
      headBoundaryTailCoords_eq_parentNonRootCoordsHeadTailEquiv_snd
        n a (RTree.node b ds) rest hC site
    have htail1 :=
      headBoundaryTailCoords_headDiagIndexEquiv_symm
        n a (RTree.node b ds) rest hC idx childSite
    rw [← htail0]
    exact htail1

theorem headBoundaryParentRootKet_headDiagIndexEquiv_symm_node
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (head : ParentOpenHeadFields n a (RTree.node b ds) rest)
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n (RTree.node b ds)) :
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail
        n a (RTree.node b ds) rest).symm (head, tail)
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a (RTree.node b ds) rest hC).symm (idx, childSite)
    headBoundaryParentRootKet
        (closeOpenNormalAssignmentClean root Aopen) site =
      headParentRootBoundaryFieldFromRoot
        n a (RTree.node b ds) rest root
        ((((blockSplitDiagEquiv n b
            (rootWeight_pos_of_positiveWeights hC)).symm
          (childSite.rootCoord, headChildIndexRootDiag idx)),
          (rootFieldDomainCleanEquivCopen n (RTree.node b ds))
            childSite.nonRootCoord),
          headChildIndexTail idx) := by
  intro Aopen site
  rw [headBoundaryParentRootKet_eq_boundaryField_at_site]
  rw [rootFieldDomainCleanEquivCopen_headDiagIndexEquiv_symm_node]
  rfl

theorem sum_normalSiteClean_node_eq_sum_root_copen
    (n b : Nat) [NeZero n] (ds : List RTree)
    (f : NormalSiteClean n (RTree.node b ds) → F2) :
    (∑ site : NormalSiteClean n (RTree.node b ds), f site) =
      ∑ u : Block n (b - 1),
        ∑ y : Copen n (RTree.node b ds),
          f { rootCoord := u
              nonRootCoord :=
                (rootFieldDomainCleanEquivCopen
                  n (RTree.node b ds)).symm y } := by
  classical
  let e := normalSiteCleanEquivRootCopen n (RTree.node b ds)
  calc
    (∑ site : NormalSiteClean n (RTree.node b ds), f site) =
        ∑ P : Block n (b - 1) × Copen n (RTree.node b ds),
          f (e.symm P) := by
          exact (Equiv.sum_comp e.symm f).symm
    _ =
        ∑ u : Block n (b - 1),
          ∑ y : Copen n (RTree.node b ds),
            f { rootCoord := u
                nonRootCoord :=
                  (rootFieldDomainCleanEquivCopen
                    n (RTree.node b ds)).symm y } := by
          rw [Fintype.sum_prod_type]
          rfl

theorem headBoundaryOpenPairingDataExpressionAtHeadDiagIndex_sum_node
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (data : HeadChildOpenData n a (RTree.node b ds) rest)
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest)
    (idx : HeadChildIndex n a rest) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a (RTree.node b ds) rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail
        n a (RTree.node b ds) rest).symm (head, tail)
    (∑ childSite : NormalSiteClean n (RTree.node b ds),
      headBoundaryOpenPairingDataExpressionAtSite
        n a (RTree.node b ds) rest hC root Aopen
        ((normalSiteClean_node_headDiagIndexEquiv
          n a (RTree.node b ds) rest hC).symm (idx, childSite))) =
      ∑ u : Block n (b - 1),
        ∑ y : Copen n (RTree.node b ds),
          headParentRootBoundaryFieldFromRoot
            n a (RTree.node b ds) rest root
            ((((blockSplitDiagEquiv n b
                (rootWeight_pos_of_positiveWeights hC)).symm
              (u, headChildIndexRootDiag idx)), y),
              headChildIndexTail idx) *
            (P.rootCopenBridge.linearEquiv
                (data idx).1 y +
              P.rootCopenBridge.linearEquiv
                (data (headChildIndexParentRoot idx,
                  headChildIndexTail idx,
                  headChildIndexRootDiag idx + 1)).1 y) := by
  intro head Aopen
  let f : NormalSiteClean n (RTree.node b ds) → F2 :=
    fun childSite =>
      headBoundaryOpenPairingDataExpressionAtSite
        n a (RTree.node b ds) rest hC root Aopen
        ((normalSiteClean_node_headDiagIndexEquiv
          n a (RTree.node b ds) rest hC).symm (idx, childSite))
  change (∑ childSite : NormalSiteClean n (RTree.node b ds),
    f childSite) = _
  rw [sum_normalSiteClean_node_eq_sum_root_copen]
  refine Finset.sum_congr rfl ?_
  intro u _
  refine Finset.sum_congr rfl ?_
  intro y _
  dsimp [f]
  rw [headBoundaryOpenPairingDataExpressionAtSite_headDiagIndex_data_parentRoot_mul]
  rw [headBoundaryParentRootKet_headDiagIndexEquiv_symm_node]
  simp only [rootFieldDomainCleanEquivCopen]
  generalize hY :
      (rootFieldDomainCleanEquivCopen_node n b ds)
        ((rootFieldDomainCleanEquivCopen_node n b ds).symm y) = Y
  have hYeq : Y = y := by
    rw [← hY]
    exact (rootFieldDomainCleanEquivCopen_node n b ds).right_inv y
  subst Y
  simp [headChildIndexParentRoot, headChildIndexTail,
    headChildIndexRootDiag]

theorem sum_root_copen_mul_add_eq_pairing
    {U Y : Type} [Fintype U] [Fintype Y]
    (A : U → Y → F2) (μ ν : Y → F2) :
    (∑ u : U, ∑ y : Y, A u y * (μ y + ν y)) =
      (∑ y : Y, μ y * ∑ u : U, A u y) +
        (∑ y : Y, ν y * ∑ u : U, A u y) := by
  classical
  rw [Finset.sum_comm]
  simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_comm]

set_option maxHeartbeats 800000 in
-- Expanding both `PiFull` terms creates large dependent sums; after the
-- reindexing, the remaining equality is definitional.
theorem headBoundaryOpenPairingDataExpressionAtHeadDiagIndex_sum_eq_RFull_node
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (data : HeadChildOpenData n a (RTree.node b ds) rest)
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest)
    (idx : HeadChildIndex n a rest) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a (RTree.node b ds) rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail
        n a (RTree.node b ds) rest).symm (head, tail)
    (∑ childSite : NormalSiteClean n (RTree.node b ds),
      headBoundaryOpenPairingDataExpressionAtSite
        n a (RTree.node b ds) rest hC root Aopen
        ((normalSiteClean_node_headDiagIndexEquiv
          n a (RTree.node b ds) rest hC).symm (idx, childSite))) =
      headChildRFull n (RTree.node b ds) hC
        (headParentRootBranchFieldFromRoot
          n a (RTree.node b ds) rest root
          (headChildIndexTail idx))
        (headChildIndexRootDiag idx)
        (P.rootCopenBridge.linearEquiv (data idx).1) +
      headChildRFull n (RTree.node b ds) hC
        (headParentRootBranchFieldFromRoot
          n a (RTree.node b ds) rest root
          (headChildIndexTail idx))
        (headChildIndexRootDiag idx)
        (P.rootCopenBridge.linearEquiv
          (data (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx + 1)).1) := by
  intro head Aopen
  rw [headBoundaryOpenPairingDataExpressionAtHeadDiagIndex_sum_node]
  rw [headChildRFull_node_apply]
  rw [PiFull_apply_eq_sum_blockSplitDiag]
  rw [PiFull_apply_eq_sum_blockSplitDiag]
  unfold headParentRootBranchFieldFromRoot
  simp only [boundaryHeadSliceLinearEquiv_apply]
  rw [sum_root_copen_mul_add_eq_pairing]
  simp only [RTree.rootWeight]
  rfl

noncomputable def parentActualHeadDiagBoundaryExponentAtTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (data : HeadChildOpenData n a C rest) : F2 :=
  let head :=
    (parentOpenHeadFieldsEquivHeadChildOpenData
      n a C rest hC P).symm data
  let Aopen :=
    (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)
  ∑ idx : HeadChildIndex n a rest,
    ∑ childSite : NormalSiteClean n C,
      headBoundaryOpenPairingDataExpressionAtSite
        n a C rest hC root Aopen
        ((normalSiteClean_node_headDiagIndexEquiv
          n a C rest hC).symm (idx, childSite))

theorem parentActualHeadDiagBoundaryExponentAtTail_eq_cyclicPairing_node
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest)
    (data : HeadChildOpenData n a (RTree.node b ds) rest) :
    parentActualHeadDiagBoundaryExponentAtTail
        n a (RTree.node b ds) rest hC P root tail data =
      ∑ q : Block n (a - 1),
        ∑ tailIdx : CoordsList n rest,
          ∑ s : Rep n,
            (headChildRFull n (RTree.node b ds) hC
                (headParentRootBranchFieldFromRoot
                  n a (RTree.node b ds) rest root tailIdx) s
                (P.rootCopenBridge.linearEquiv
                  (data (q, tailIdx, s)).1) +
              headChildRFull n (RTree.node b ds) hC
                (headParentRootBranchFieldFromRoot
                  n a (RTree.node b ds) rest root tailIdx) s
                (P.rootCopenBridge.linearEquiv
                  (data (q, tailIdx, s + (1 : Rep n))).1)) := by
  classical
  unfold parentActualHeadDiagBoundaryExponentAtTail
  change
    (∑ idx : Block n (a - 1) × CoordsList n rest × Rep n,
      ∑ childSite : NormalSiteClean n (RTree.node b ds),
        headBoundaryOpenPairingDataExpressionAtSite
          n a (RTree.node b ds) rest hC root
          ((openNormalAssignmentCleanEquivHeadTail
            n a (RTree.node b ds) rest).symm
            ((parentOpenHeadFieldsEquivHeadChildOpenData
              n a (RTree.node b ds) rest hC P).symm data, tail))
          ((normalSiteClean_node_headDiagIndexEquiv
            n a (RTree.node b ds) rest hC).symm (idx, childSite))) = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro tailIdx _
  refine Finset.sum_congr rfl ?_
  intro s _
  exact
    headBoundaryOpenPairingDataExpressionAtHeadDiagIndex_sum_eq_RFull_node
      n a b ds rest hC P root data tail (q, tailIdx, s)

theorem parentActualHeadDiagBoundaryExponentAtTail_eq_fullBoundary_rootSucc_node
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest)
    (data : HeadChildOpenData n a (RTree.node b ds) rest) :
    parentActualHeadDiagBoundaryExponentAtTail
        n a (RTree.node b ds) rest hC P root tail data =
      headChildOpenDataFullBoundaryExponent
        n a (RTree.node b ds) rest hC P root
        (headChildOpenDataRootSuccEquiv
          n a (RTree.node b ds) rest data) := by
  rw [parentActualHeadDiagBoundaryExponentAtTail_eq_cyclicPairing_node]
  rw [headChildOpenDataFullBoundaryExponent_rootSucc_eq_cyclicPairing]

noncomputable def parentActualHeadDiagInternalExponentAtTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (data : HeadChildOpenData n a C rest) : F2 :=
  let head :=
    (parentOpenHeadFieldsEquivHeadChildOpenData
      n a C rest hC P).symm data
  let Aopen :=
    (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)
  ∑ idx : HeadChildIndex n a rest,
    ∑ childSite : NormalSiteClean n C,
      headInternalPhaseAtSiteClean_node C rest
        (closeOpenNormalAssignmentClean root Aopen)
        ((normalSiteClean_node_headDiagIndexEquiv
          n a C rest hC).symm (idx, childSite))

noncomputable def parentActualHeadDataWeightAtTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (data : HeadChildOpenData n a C rest) : ℤ :=
  ∏ idx : HeadChildIndex n a rest,
    ∏ childSite : NormalSiteClean n C,
      chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
        n a C rest hC root
        ((parentOpenHeadFieldsEquivHeadChildOpenData
          n a C rest hC P).symm data)
        tail idx childSite)

noncomputable def parentActualHeadDiagDataWeightAtTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (data : HeadChildOpenData n a C rest) : ℤ :=
  ∏ idx : HeadChildIndex n a rest,
    ∏ childSite : NormalSiteClean n C,
      chi (parentHeadDiagDataInternalPhaseAtHeadIndexChildSite
        n a C rest hC root
        ((parentOpenHeadFieldsEquivHeadChildOpenData
          n a C rest hC P).symm data)
        tail idx childSite)

noncomputable def parentActualHeadDataSignedSumAtTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest) : ℤ :=
  ∑ data : HeadChildOpenData n a C rest,
    parentActualHeadDataWeightAtTail n a C rest hC P root tail data

noncomputable def parentActualHeadDiagDataSignedSumAtTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest) : ℤ :=
  ∑ data : HeadChildOpenData n a C rest,
    parentActualHeadDiagDataWeightAtTail n a C rest hC P root tail data

theorem parentActualHeadDataWeightAtTail_eq_siteShearProduct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (data : HeadChildOpenData n a C rest) :
    parentActualHeadDataWeightAtTail n a C rest hC P root tail data =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
            n a C rest hC root
            ((parentOpenHeadFieldsEquivHeadChildOpenData
              n a C rest hC P).symm data)
            tail
            (((headIndexChildSiteLastToDiagEquiv
              n a C rest).symm (idx, childSite)).1)
            (((headIndexChildSiteLastToDiagEquiv
              n a C rest).symm (idx, childSite)).2)) := by
  unfold parentActualHeadDataWeightAtTail
  exact prod_headIndex_childSite_eq_prod_lastToDiag_symm_apply
    n a C rest
    (fun idx childSite =>
      chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
        n a C rest hC root
        ((parentOpenHeadFieldsEquivHeadChildOpenData
          n a C rest hC P).symm data)
        tail idx childSite))

theorem parentHeadDiagDataInternalPhase_eq_lastShearPhase
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    parentHeadDiagDataInternalPhaseAtHeadIndexChildSite
        n a C rest hC root head tail idx childSite =
      parentHeadDataInternalPhaseAtHeadIndexChildSite
        n a C rest hC root head tail
        (((headIndexChildSiteLastToDiagEquiv
          n a C rest).symm (idx, childSite)).1)
        (((headIndexChildSiteLastToDiagEquiv
          n a C rest).symm (idx, childSite)).2) := by
  rfl

theorem parentActualHeadDataWeightAtTail_eq_diagDataWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (data : HeadChildOpenData n a C rest) :
    parentActualHeadDataWeightAtTail n a C rest hC P root tail data =
      parentActualHeadDiagDataWeightAtTail
        n a C rest hC P root tail data := by
  rw [parentActualHeadDataWeightAtTail_eq_siteShearProduct]
  unfold parentActualHeadDiagDataWeightAtTail
  exact Finset.prod_congr rfl (by
    intro idx _
    exact Finset.prod_congr rfl (by
      intro childSite _
      rw [parentHeadDiagDataInternalPhase_eq_lastShearPhase]))

theorem parentActualHeadDiagDataWeightAtTail_eq_internal_mul_boundary
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (data : HeadChildOpenData n a C rest) :
    parentActualHeadDiagDataWeightAtTail n a C rest hC P root tail data =
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headInternalPhaseAtSiteClean_node C rest
            (closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail
                n a C rest).symm
                ((parentOpenHeadFieldsEquivHeadChildOpenData
                  n a C rest hC P).symm data, tail)))
            ((normalSiteClean_node_headDiagIndexEquiv
              n a C rest hC).symm (idx, childSite)))) *
        chi (parentActualHeadDiagBoundaryExponentAtTail
          n a C rest hC P root tail data) := by
  classical
  let head :=
    (parentOpenHeadFieldsEquivHeadChildOpenData
      n a C rest hC P).symm data
  let Aopen :=
    (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)
  let A := closeOpenNormalAssignmentClean root Aopen
  let B : HeadChildIndex n a rest → NormalSiteClean n C → F2 :=
    fun idx childSite =>
      headBoundaryOpenPairingDataExpressionAtSite
        n a C rest hC root Aopen
        ((normalSiteClean_node_headDiagIndexEquiv
          n a C rest hC).symm (idx, childSite))
  let I : HeadChildIndex n a rest → NormalSiteClean n C → F2 :=
    fun idx childSite =>
      headInternalPhaseAtSiteClean_node C rest A
        ((normalSiteClean_node_headDiagIndexEquiv
          n a C rest hC).symm (idx, childSite))
  have hboundary :
      chi (parentActualHeadDiagBoundaryExponentAtTail
          n a C rest hC P root tail data) =
        ∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C, chi (B idx childSite) := by
    unfold parentActualHeadDiagBoundaryExponentAtTail
    change chi (∑ idx : HeadChildIndex n a rest,
      ∑ childSite : NormalSiteClean n C, B idx childSite) = _
    rw [chi_sum_univ_apply]
    refine Finset.prod_congr rfl ?_
    intro idx _
    rw [chi_sum_univ_apply]
  have hsplit :
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (B idx childSite + I idx childSite)) =
        (∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C, chi (B idx childSite)) *
          (∏ idx : HeadChildIndex n a rest,
            ∏ childSite : NormalSiteClean n C, chi (I idx childSite)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro idx _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro childSite _
    rw [chi_add]
  unfold parentActualHeadDiagDataWeightAtTail
  change
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (B idx childSite + I idx childSite)) =
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C, chi (I idx childSite)) *
        chi (parentActualHeadDiagBoundaryExponentAtTail
          n a C rest hC P root tail data)
  rw [hsplit, hboundary, mul_comm]

theorem parentActualHeadDiagDataWeightAtTail_eq_fullWeight_rootSucc_node_of_internal
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest)
    (data : HeadChildOpenData n a (RTree.node b ds) rest)
    (hinternal :
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n (RTree.node b ds),
          chi (headInternalPhaseAtSiteClean_node (RTree.node b ds) rest
            (closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail
                n a (RTree.node b ds) rest).symm
                ((parentOpenHeadFieldsEquivHeadChildOpenData
                  n a (RTree.node b ds) rest hC P).symm data, tail)))
            ((normalSiteClean_node_headDiagIndexEquiv
              n a (RTree.node b ds) rest hC).symm (idx, childSite)))) =
        headChildOpenDataInternalWeight
          n a (RTree.node b ds) rest data) :
    parentActualHeadDiagDataWeightAtTail
        n a (RTree.node b ds) rest hC P root tail data =
      headChildOpenDataFullWeight
        n a (RTree.node b ds) rest hC P root
        (headChildOpenDataRootSuccEquiv
          n a (RTree.node b ds) rest data) := by
  rw [parentActualHeadDiagDataWeightAtTail_eq_internal_mul_boundary]
  rw [hinternal]
  unfold headChildOpenDataFullWeight
  rw [headChildOpenDataInternalWeight_rootSucc]
  rw [parentActualHeadDiagBoundaryExponentAtTail_eq_fullBoundary_rootSucc_node]

theorem parentActualHeadDiagDataWeightAtTail_eq_fullProductWeight_rootSucc_node_of_internal
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest)
    (data : HeadChildOpenData n a (RTree.node b ds) rest)
    (hinternal :
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n (RTree.node b ds),
          chi (headInternalPhaseAtSiteClean_node (RTree.node b ds) rest
            (closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail
                n a (RTree.node b ds) rest).symm
                ((parentOpenHeadFieldsEquivHeadChildOpenData
                  n a (RTree.node b ds) rest hC P).symm data, tail)))
            ((normalSiteClean_node_headDiagIndexEquiv
              n a (RTree.node b ds) rest hC).symm (idx, childSite)))) =
        headChildOpenDataInternalWeight
          n a (RTree.node b ds) rest data) :
    parentActualHeadDiagDataWeightAtTail
        n a (RTree.node b ds) rest hC P root tail data =
      headChildOpenDataFullProductWeight
        n a (RTree.node b ds) rest hC P root
        (headChildOpenDataRootSuccEquiv
          n a (RTree.node b ds) rest data) := by
  rw [← headChildOpenDataFullWeight_eq_prod_index]
  exact
    parentActualHeadDiagDataWeightAtTail_eq_fullWeight_rootSucc_node_of_internal
      n a b ds rest hC P root tail data hinternal

theorem parentActualHeadDataSignedSumAtTail_eq_diagDataSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest) :
    parentActualHeadDataSignedSumAtTail n a C rest hC P root tail =
      parentActualHeadDiagDataSignedSumAtTail
        n a C rest hC P root tail := by
  classical
  unfold parentActualHeadDataSignedSumAtTail
    parentActualHeadDiagDataSignedSumAtTail
  exact Finset.sum_congr rfl (by
    intro data _
    exact parentActualHeadDataWeightAtTail_eq_diagDataWeight
      n a C rest hC P root tail data)

theorem parentActualHeadPhaseSignedSumAtTail_eq_dataSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      parentActualHeadDataSignedSumAtTail n a C rest hC P root tail := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_sum_dataInternalPhase]
  rfl

theorem parentActualHeadPhaseSignedSumAtTail_eq_diagDataSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      parentActualHeadDiagDataSignedSumAtTail
        n a C rest hC P root tail := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_dataSignedSum]
  exact parentActualHeadDataSignedSumAtTail_eq_diagDataSignedSum
    n a C rest hC P root tail

theorem headChildOpenDataFullSignedSum_eq_sum_productWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataFullSignedSum n a C rest hC P root =
      ∑ data : HeadChildOpenData n a C rest,
        headChildOpenDataFullProductWeight n a C rest hC P root data := by
  classical
  unfold headChildOpenDataFullSignedSum
  refine Finset.sum_congr rfl ?_
  intro data _
  exact headChildOpenDataFullWeight_eq_prod_index n a C rest hC P root data

theorem parentActualHeadDataSignedSumAtTail_eq_fullSignedSum_of_equiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataFullProductWeight n a C rest hC P root (e data)) :
    parentActualHeadDataSignedSumAtTail n a C rest hC P root tail =
      headChildOpenDataFullSignedSum n a C rest hC P root := by
  classical
  unfold parentActualHeadDataSignedSumAtTail
  rw [headChildOpenDataFullSignedSum_eq_sum_productWeight]
  let F : HeadChildOpenData n a C rest → ℤ := fun data =>
    headChildOpenDataFullProductWeight n a C rest hC P root data
  calc
    (∑ data : HeadChildOpenData n a C rest,
        parentActualHeadDataWeightAtTail n a C rest hC P root tail data) =
        ∑ data : HeadChildOpenData n a C rest, F (e data) := by
          refine Finset.sum_congr rfl ?_
          intro data _
          exact hweight data
    _ = ∑ data : HeadChildOpenData n a C rest, F data := by
          exact Equiv.sum_comp e F

theorem parentActualHeadDiagDataSignedSumAtTail_eq_fullSignedSum_of_equiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDiagDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataFullProductWeight n a C rest hC P root (e data)) :
    parentActualHeadDiagDataSignedSumAtTail n a C rest hC P root tail =
      headChildOpenDataFullSignedSum n a C rest hC P root := by
  classical
  unfold parentActualHeadDiagDataSignedSumAtTail
  rw [headChildOpenDataFullSignedSum_eq_sum_productWeight]
  let F : HeadChildOpenData n a C rest → ℤ := fun data =>
    headChildOpenDataFullProductWeight n a C rest hC P root data
  calc
    (∑ data : HeadChildOpenData n a C rest,
        parentActualHeadDiagDataWeightAtTail
          n a C rest hC P root tail data) =
        ∑ data : HeadChildOpenData n a C rest, F (e data) := by
          refine Finset.sum_congr rfl ?_
          intro data _
          exact hweight data
    _ = ∑ data : HeadChildOpenData n a C rest, F data := by
          exact Equiv.sum_comp e F

theorem parentActualHeadPhaseSignedSumAtTail_eq_fullSignedSum_of_equiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataFullProductWeight n a C rest hC P root (e data)) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      headChildOpenDataFullSignedSum n a C rest hC P root := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_dataSignedSum]
  exact parentActualHeadDataSignedSumAtTail_eq_fullSignedSum_of_equiv
    n a C rest hC P root tail e hweight

theorem parentActualHeadPhaseSignedSumAtTail_eq_fullSignedSum_of_diagEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDiagDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataFullProductWeight n a C rest hC P root (e data)) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      headChildOpenDataFullSignedSum n a C rest hC P root := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_diagDataSignedSum]
  exact parentActualHeadDiagDataSignedSumAtTail_eq_fullSignedSum_of_equiv
    n a C rest hC P root tail e hweight

theorem parentActualHeadPhaseSignedSumAtTail_eq_descScalar_mul_messageSum_of_equiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataFullProductWeight n a C rest hC P root (e data)) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest hC *
        headBranchMessageSignedSum n a C rest hC P root := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_fullSignedSum_of_equiv
    n a C rest hC P root tail e hweight]
  exact headChildOpenDataFullSignedSum_eq_descScalar_mul_messageSum
    n a C rest hC P root

theorem parentActualHeadPhaseSignedSumAtTail_eq_descScalar_mul_messageSum_of_diagEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDiagDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataFullProductWeight n a C rest hC P root (e data)) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest hC *
        headBranchMessageSignedSum n a C rest hC P root := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_fullSignedSum_of_diagEquiv
    n a C rest hC P root tail e hweight]
  exact headChildOpenDataFullSignedSum_eq_descScalar_mul_messageSum
    n a C rest hC P root

theorem parentActualHeadPhaseSignedSumAtTail_eq_fullSignedSum_rootSucc_node_of_internal
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest)
    (hinternal :
      ∀ data : HeadChildOpenData n a (RTree.node b ds) rest,
        (∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n (RTree.node b ds),
            chi (headInternalPhaseAtSiteClean_node (RTree.node b ds) rest
              (closeOpenNormalAssignmentClean root
                ((openNormalAssignmentCleanEquivHeadTail
                  n a (RTree.node b ds) rest).symm
                  ((parentOpenHeadFieldsEquivHeadChildOpenData
                    n a (RTree.node b ds) rest hC P).symm data, tail)))
              ((normalSiteClean_node_headDiagIndexEquiv
                n a (RTree.node b ds) rest hC).symm (idx, childSite)))) =
          headChildOpenDataInternalWeight
            n a (RTree.node b ds) rest data) :
    parentActualHeadPhaseSignedSumAtTail
        n a (RTree.node b ds) rest root tail =
      headChildOpenDataFullSignedSum
        n a (RTree.node b ds) rest hC P root := by
  exact
    parentActualHeadPhaseSignedSumAtTail_eq_fullSignedSum_of_diagEquiv
      n a (RTree.node b ds) rest hC P root tail
      (headChildOpenDataRootSuccEquiv n a (RTree.node b ds) rest)
      (fun data =>
        parentActualHeadDiagDataWeightAtTail_eq_fullProductWeight_rootSucc_node_of_internal
          n a b ds rest hC P root tail data (hinternal data))

theorem parentActualHeadPhaseSignedSumAtTail_eq_descScalar_mul_messageSum_rootSucc_node_of_internal
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest)
    (hinternal :
      ∀ data : HeadChildOpenData n a (RTree.node b ds) rest,
        (∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n (RTree.node b ds),
            chi (headInternalPhaseAtSiteClean_node (RTree.node b ds) rest
              (closeOpenNormalAssignmentClean root
                ((openNormalAssignmentCleanEquivHeadTail
                  n a (RTree.node b ds) rest).symm
                  ((parentOpenHeadFieldsEquivHeadChildOpenData
                    n a (RTree.node b ds) rest hC P).symm data, tail)))
              ((normalSiteClean_node_headDiagIndexEquiv
                n a (RTree.node b ds) rest hC).symm (idx, childSite)))) =
          headChildOpenDataInternalWeight
            n a (RTree.node b ds) rest data) :
    parentActualHeadPhaseSignedSumAtTail
        n a (RTree.node b ds) rest root tail =
      (2 : ℤ) ^
          branchDescendantScalarExponent
            n a 0 (RTree.node b ds) rest hC *
        headBranchMessageSignedSum
          n a (RTree.node b ds) rest hC P root := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_fullSignedSum_rootSucc_node_of_internal
    n a b ds rest hC P root tail hinternal]
  exact headChildOpenDataFullSignedSum_eq_descScalar_mul_messageSum
    n a (RTree.node b ds) rest hC P root

end Imbalance
end TreeGraph
