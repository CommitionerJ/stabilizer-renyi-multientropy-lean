import TreeGraph.Imbalance.NodeHeadInternalWeightPhase
import TreeGraph.Imbalance.NodeHeadActualToFullSum

namespace TreeGraph
namespace Imbalance

theorem parentNonRootCoordsHeadTailEquiv_head_root_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (rd : RootFieldDomainClean n (RTree.node a (C :: rest)))
    (j : Fin C.rootWeight) :
    ((parentNonRootCoordsHeadTailEquiv n a C rest) rd).1
        (Vertex.root C) j =
      rd
        (headChildRootNonRootInParent
          (a := a) (C := C) (rest := rest))
        (Fin.cast
          (headChildRootNonRootInParent_weight_eq_rootWeight
            (a := a) (C := C) (rest := rest)).symm j) := by
  let E := parentNonRootCoordsHeadTailEquiv n a C rest
  have h :=
    parentNonRootCoordsHeadTailEquiv_symm_head_root
      n a C rest (E rd).1 (E rd).2 j
  have hE : E.symm (E rd) = rd := E.left_inv rd
  rw [hE] at h
  exact h.symm

theorem parentNonRootCoordsHeadTailEquiv_head_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (rd : RootFieldDomainClean n (RTree.node a (C :: rest)))
    (v : NonRootVertex C)
    (j : Fin (NonRootVertex.weight v)) :
    ((parentNonRootCoordsHeadTailEquiv n a C rest) rd).1
        v.1 j =
      rd
        (headChildNonRootInParent
          (a := a) (C := C) (rest := rest) v)
        (Fin.cast
          (headChildNonRootInParent_weight
            (a := a) (C := C) (rest := rest) v).symm j) := by
  let E := parentNonRootCoordsHeadTailEquiv n a C rest
  have h :=
    parentNonRootCoordsHeadTailEquiv_symm_head
      n a C rest (E rd).1 (E rd).2 v j
  have hE : E.symm (E rd) = rd := E.left_inv rd
  rw [hE] at h
  exact h.symm

theorem parentNonRootCoordsHeadTailEquiv_tail_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (rd : RootFieldDomainClean n (RTree.node a (C :: rest)))
    (p : NodeChildVertex rest)
    (j : Fin (Vertex.weight p.2)) :
    ((nodeChildVertexCoordsEquivCoordsList n rest).symm
        ((parentNonRootCoordsHeadTailEquiv n a C rest) rd).2) p j =
      rd
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j) := by
  let E := parentNonRootCoordsHeadTailEquiv n a C rest
  have h :=
    parentNonRootCoordsHeadTailEquiv_symm_tail
      n a C rest (E rd).1 (E rd).2 p j
  have hE : E.symm (E rd) = rd := E.left_inv rd
  rw [hE] at h
  exact h.symm

theorem normalSiteClean_node_headDiagIndexEquiv_symm_childNonRootCoord
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (v : NonRootVertex C)
    (j : Fin (NonRootVertex.weight v)) :
    (((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
        (idx, childSite)).nonRootCoord
        (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
        (Fin.cast
          (headChildNonRootInParent_weight
            (a := a) (C := C) (rest := rest) v).symm j)) =
      childSite.nonRootCoord v j := by
  let site :=
    (normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
      (idx, childSite)
  have hproj :=
    parentNonRootCoordsHeadTailEquiv_head_apply
      n a C rest site.nonRootCoord v j
  have hboundary :=
    headChildBoundaryVertexCoord_eq_parentHeadCoord_nonroot
      n a C rest hC site v j
  have hlocal :=
    headChildLocalOpenCoordOfParentSite_headDiagIndexEquiv_symm
      n a C rest hC idx childSite
  rw [hlocal] at hboundary
  have hleft :
      vertexCoordDomainFromBoundaryOpen n C
          ((rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord)
          v.1 j =
        childSite.nonRootCoord v j := by
    rw [vertexCoordDomainFromBoundaryOpen_apply_nonroot]
    exact congrFun
      (congrFun
        ((rootFieldDomainCleanEquivCopen n C).left_inv
          childSite.nonRootCoord) v) j
  rw [hleft] at hboundary
  exact hproj.symm.trans hboundary.symm

theorem diagonalClean_headChildNonRoot_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (v : NonRootVertex C) :
    diagonalClean
        ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
          (idx, childSite))
        (headChildNonRootInParent (a := a) (C := C) (rest := rest) v) =
      diagonalClean childSite v := by
  unfold diagonalClean
  refine Finset.sum_congr rfl ?_
  intro j _
  simpa using
    normalSiteClean_node_headDiagIndexEquiv_symm_childNonRootCoord
      n a C rest hC idx childSite v
      (Fin.cast
        (headChildNonRootInParent_weight
          (a := a) (C := C) (rest := rest) v) j)

theorem normalSiteClean_node_headDiagIndexEquiv_symm_childRootCoord_splitLast
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (j : Fin C.rootWeight) :
    (((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
        (idx, childSite)).nonRootCoord
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
        (Fin.cast
          (headChildRootNonRootInParent_weight_eq_rootWeight
            (a := a) (C := C) (rest := rest)).symm j)) =
      ((blockSplitLastEquiv n C.rootWeight
          (rootWeight_pos_of_positiveWeights hC)).symm
        (childSite.rootCoord,
          headChildIndexRootDiag idx -
            normalSiteCleanRootTotalDiag n C childSite)) j := by
  rw [normalSiteClean_node_headDiagIndexEquiv_symm_apply]
  let oldP :=
    (headIndexChildSiteLastToDiagEquiv n a C rest).symm (idx, childSite)
  have hcoord :=
    normalSiteClean_node_headIndexEquiv_symm_childRootCoord
      n a C rest hC oldP.1 oldP.2 j
  have hroot :
      oldP.2.rootCoord = childSite.rootCoord := by
    dsimp [oldP]
    exact headIndexChildSiteLastToDiagEquiv_symm_site_rootCoord
      n a C rest idx childSite
  have hdiag :
      headChildIndexRootDiag oldP.1 =
        headChildIndexRootDiag idx -
          normalSiteCleanRootTotalDiag n C childSite := by
    dsimp [oldP, normalSiteCleanRootTotalDiag]
    exact headIndexChildSiteLastToDiagEquiv_symm_rootDiag
      n a C rest idx childSite
  simpa [oldP, hroot, hdiag] using hcoord

theorem headNonRootParentDomainChildRootBlock_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (v : NonRootVertex C)
    (shift : Rep n) :
    headNonRootParentDomainChildRootBlock n a C rest v
        (nonRootDomainOfSiteClean
          ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
            (idx, childSite))
          (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
          shift) =
      (blockSplitLastEquiv n C.rootWeight
          (rootWeight_pos_of_positiveWeights hC)).symm
        (childSite.rootCoord,
          headChildIndexRootDiag idx -
            normalSiteCleanRootTotalDiag n C childSite) := by
  funext j
  unfold headNonRootParentDomainChildRootBlock nonRootDomainOfSiteClean
  exact normalSiteClean_node_headDiagIndexEquiv_symm_childRootCoord_splitLast
    n a C rest hC idx childSite j

theorem headNonRootParentDomainChildDomain_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (v : NonRootVertex C)
    (shift : Rep n) :
    headNonRootParentDomainChildDomain n a C rest hC v
        (nonRootDomainOfSiteClean
          ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
            (idx, childSite))
          (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
          shift) =
      nonRootDomainOfSiteClean childSite v shift := by
  apply nonRootFieldDomainClean_ext_apply
  · unfold headNonRootParentDomainChildDomain
    rw [headNonRootParentDomainChildRootBlock_headDiagIndexEquiv_symm]
    exact congrArg Prod.fst
      ((blockSplitLastEquiv n C.rootWeight
        (rootWeight_pos_of_positiveWeights hC)).right_inv
        (childSite.rootCoord,
          headChildIndexRootDiag idx -
            normalSiteCleanRootTotalDiag n C childSite))
  · unfold headNonRootParentDomainChildDomain nonRootDomainOfSiteClean
    rw [diagonalClean_headChildNonRoot_headDiagIndexEquiv_symm]
  · intro u j
    unfold headNonRootParentDomainChildDomain nonRootDomainOfSiteClean
    change
      (((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
          (idx, childSite)).nonRootCoord
          (headChildNonRootInParent
            (a := a) (C := C) (rest := rest) u.1)
          (Fin.cast
            (headChildNonRootInParent_weight
              (a := a) (C := C) (rest := rest) u.1).symm j)) =
        childSite.nonRootCoord u.1 j
    exact normalSiteClean_node_headDiagIndexEquiv_symm_childNonRootCoord
      n a C rest hC idx childSite u.1 j

theorem headNonRootParentDomainTail_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (v : NonRootVertex C)
    (shift : Rep n) :
    headNonRootParentDomainTail n a C rest v
        (nonRootDomainOfSiteClean
          ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
            (idx, childSite))
          (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
          shift) =
      headChildIndexTail idx := by
  let site :=
    (normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
      (idx, childSite)
  let E := nodeChildVertexCoordsEquivCoordsList n rest
  let F : (p : NodeChildVertex rest) → Fin (Vertex.weight p.2) → Rep n :=
    fun p j =>
      site.nonRootCoord
        ⟨childVertexAtAsNonRootInNode (a := a)
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)), by
          cases p with
          | mk i w =>
              simp [nodeChildVertexConsEquiv]⟩
        (Fin.cast (by
          rw [childVertexAtAsNonRootInNode_weight]
          exact (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm) j)
  have hF : F =
      (nodeChildVertexCoordsEquivCoordsList n rest).symm
        ((parentNonRootCoordsHeadTailEquiv n a C rest) site.nonRootCoord).2 := by
    funext p j
    dsimp [F]
    exact
      (parentNonRootCoordsHeadTailEquiv_tail_apply
        n a C rest site.nonRootCoord p j).symm
  have htail :
      ((parentNonRootCoordsHeadTailEquiv n a C rest) site.nonRootCoord).2 =
        headChildIndexTail idx := by
    have hboundary :=
      headBoundaryTailCoords_eq_parentNonRootCoordsHeadTailEquiv_snd
        n a C rest hC site
    have hdiag :=
      headBoundaryTailCoords_headDiagIndexEquiv_symm
        n a C rest hC idx childSite
    simpa [site] using hboundary.symm.trans hdiag
  unfold headNonRootParentDomainTail nonRootDomainOfSiteClean
  change E F = headChildIndexTail idx
  rw [hF, htail]
  exact E.right_inv (headChildIndexTail idx)

theorem headNonRootParentDomainIndex_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (v : NonRootVertex C)
    (shift : Rep n) :
    headNonRootParentDomainIndex n a C rest hC v
        (nonRootDomainOfSiteClean
          ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
            (idx, childSite))
          (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
          shift) =
      (headChildIndexParentRoot idx, headChildIndexTail idx,
        headChildIndexRootDiag idx -
          normalSiteCleanRootTotalDiag n C childSite) := by
  let site :=
    (normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
      (idx, childSite)
  have hroot :
      site.rootCoord = headChildIndexParentRoot idx := by
    have hsite :=
      headBoundaryParentRootContext_eq_site_rootCoord
        n a C rest hC site
    have hidx :=
      headBoundaryParentRootContext_headDiagIndexEquiv_symm
        n a C rest hC idx childSite
    exact hsite.symm.trans (by simpa [site] using hidx)
  have hsnd :
      ((blockSplitLastEquiv n C.rootWeight
          (rootWeight_pos_of_positiveWeights hC))
        ((blockSplitLastEquiv n C.rootWeight
          (rootWeight_pos_of_positiveWeights hC)).symm
          (childSite.rootCoord,
            headChildIndexRootDiag idx -
              normalSiteCleanRootTotalDiag n C childSite))).2 =
        headChildIndexRootDiag idx -
          normalSiteCleanRootTotalDiag n C childSite :=
    congrArg Prod.snd
      ((blockSplitLastEquiv n C.rootWeight
        (rootWeight_pos_of_positiveWeights hC)).right_inv
        (childSite.rootCoord,
          headChildIndexRootDiag idx -
            normalSiteCleanRootTotalDiag n C childSite))
  unfold headNonRootParentDomainIndex
  rw [headNonRootParentDomainTail_headDiagIndexEquiv_symm]
  rw [headNonRootParentDomainChildRootBlock_headDiagIndexEquiv_symm]
  change
    (site.rootCoord, headChildIndexTail idx,
      ((blockSplitLastEquiv n C.rootWeight
          (rootWeight_pos_of_positiveWeights hC))
        ((blockSplitLastEquiv n C.rootWeight
          (rootWeight_pos_of_positiveWeights hC)).symm
          (childSite.rootCoord,
            headChildIndexRootDiag idx -
              normalSiteCleanRootTotalDiag n C childSite))).2) =
      (headChildIndexParentRoot idx, headChildIndexTail idx,
        headChildIndexRootDiag idx -
          normalSiteCleanRootTotalDiag n C childSite)
  rw [hroot, hsnd]
  rfl

theorem parentHeadDiagData_childRootPulledKet_eq_data
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
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let y := (rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord
    headChildPulledKetAtPathFromParent A site [] =
      P.rootCopenBridge.linearEquiv
        (data (headChildIndexParentRoot idx,
          headChildIndexTail idx,
          headChildIndexRootDiag idx)).1 y := by
  intro head Aopen A site y
  unfold headChildPulledKetAtPathFromParent
  change headBoundaryChildRootKet A site = _
  rw [headBoundaryChildRootKet_eq_boundaryFamilyAtSite n a C rest root Aopen site]
  rw [← headChildRootBoundaryFieldFromParent_diag_eq_site
    n a C rest hC Aopen site]
  rw [diagonalClean_headChildRoot_headDiagIndexEquiv_symm]
  rw [headBoundaryParentRootContext_headDiagIndexEquiv_symm]
  rw [headBoundaryTailCoords_headDiagIndexEquiv_symm]
  rw [headChildLocalOpenCoordOfParentSite_headDiagIndexEquiv_symm]
  exact headChildRootBoundaryFieldFromParent_headChildOpenData
    n a C rest hC P data tail
    (headChildIndexParentRoot idx)
    (headChildIndexTail idx)
    (headChildIndexRootDiag idx)
    ((rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord)

theorem parentHeadDiagData_childRootPulledBra_eq_data_succ
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
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let y := (rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord
    headChildPulledBraAtPathFromParent A site [] =
      P.rootCopenBridge.linearEquiv
        (data (headChildIndexParentRoot idx,
          headChildIndexTail idx,
          headChildIndexRootDiag idx + 1)).1 y := by
  intro head Aopen A site y
  unfold headChildPulledBraAtPathFromParent
  change headBoundaryChildRootBra A site = _
  rw [headBoundaryChildRootBra_eq_boundaryFamilyAtSite_succ
    n a C rest root Aopen site]
  rw [← headChildRootBoundaryFieldFromParent_succ_eq_site
    n a C rest hC Aopen site]
  rw [diagonalClean_headChildRoot_headDiagIndexEquiv_symm]
  rw [headBoundaryParentRootContext_headDiagIndexEquiv_symm]
  rw [headBoundaryTailCoords_headDiagIndexEquiv_symm]
  rw [headChildLocalOpenCoordOfParentSite_headDiagIndexEquiv_symm]
  exact headChildRootBoundaryFieldFromParent_headChildOpenData
    n a C rest hC P data tail
    (headChildIndexParentRoot idx)
    (headChildIndexTail idx)
    (headChildIndexRootDiag idx + 1)
    ((rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord)

theorem parentHeadDiagData_childRootPulledKet_eq_shearedData
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
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let y := (rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord
    headChildPulledKetAtPathFromParent A site [] =
      P.rootCopenBridge.linearEquiv
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite)).1 y := by
  intro head Aopen A site y
  rw [parentHeadDiagData_childRootPulledKet_eq_data]
  exact (headTotalShearDataWithBridge_root_site_total
    n a C rest P.rootCopenBridge data
    (headChildIndexParentRoot idx)
    (headChildIndexTail idx)
    (headChildIndexRootDiag idx)
    childSite).symm

theorem parentHeadDiagData_childRootPulledBra_eq_shearedData
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
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let y := (rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord
    headChildPulledBraAtPathFromParent A site [] =
      P.rootCopenBridge.linearEquiv
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite + 1)).1 y := by
  intro head Aopen A site y
  rw [parentHeadDiagData_childRootPulledBra_eq_data_succ]
  have hidx :
      ((headChildIndexParentRoot idx, headChildIndexTail idx,
          headChildIndexRootDiag idx +
            normalSiteCleanCopenTotalDiag n C childSite + 1) :
          HeadChildIndex n a rest) =
        (headChildIndexParentRoot idx, headChildIndexTail idx,
          (headChildIndexRootDiag idx + 1) +
            normalSiteCleanCopenTotalDiag n C childSite) := by
    ext <;> simp [headChildIndexParentRoot, headChildIndexTail,
      headChildIndexRootDiag]
    abel
  rw [hidx]
  exact (headTotalShearDataWithBridge_root_site_total
    n a C rest P.rootCopenBridge data
    (headChildIndexParentRoot idx)
    (headChildIndexTail idx)
    (headChildIndexRootDiag idx + 1)
    childSite).symm

theorem parentHeadData_childNonRootKetAtVertex_eq_data_extract
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (v : NonRootVertex C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let parentDom :=
      nonRootDomainOfSiteClean site
        (headChildNonRootInParent
          (a := a) (C := C) (rest := rest) v) 0
    ketAtVertexClean A site
        (headChildVertexInParent (a := a) (C := C) (rest := rest) v.1) =
      ((data
        (headNonRootParentDomainIndex n a C rest hC v parentDom)).2).nodeField
        v (headNonRootParentDomainChildDomain
          n a C rest hC v parentDom) := by
  intro head Aopen A parentDom
  have hvertex :
      (⟨headChildVertexInParent
          (a := a) (C := C) (rest := rest) v.1,
        by
          simp [headChildVertexInParent_addr]⟩ :
        NonRootVertex (RTree.node a (C :: rest))) =
      headChildNonRootInParent (a := a) (C := C) (rest := rest) v := by
    apply Subtype.ext
    rfl
  unfold ketAtVertexClean
  rw [dif_neg]
  · change
      A.nodeField
        (⟨headChildVertexInParent
            (a := a) (C := C) (rest := rest) v.1,
          ?_⟩ :
          NonRootVertex (RTree.node a (C :: rest)))
        (nonRootDomainOfSiteClean site
          (⟨headChildVertexInParent
              (a := a) (C := C) (rest := rest) v.1,
            ?_⟩ :
            NonRootVertex (RTree.node a (C :: rest))) 0) =
        _
    rw [hvertex]
    change Aopen.nodeField
        (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
        parentDom = _
    rw [openNormalAssignmentCleanEquivHeadTail_symm_nodeField_head_nonroot]
    have hdata :=
      parentOpenHeadFieldsEquivHeadChildOpenData_symm_apply_nonroot
      n a C rest hC P data
      (headNonRootParentDomainIndex n a C rest hC v parentDom)
      v
      (headNonRootParentDomainChildDomain n a C rest hC v parentDom)
    have hconstruct :=
      headNonRootParentDomain_construct_extract n a C rest hC v parentDom
    rw [hconstruct] at hdata
    exact hdata
  · intro hroot
    simp [headChildVertexInParent_addr] at hroot

theorem ketAtPathClean_headChildNonRoot
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (v : NonRootVertex C) :
    ketAtPathClean A site (0 :: v.1.1) =
      ketAtVertexClean A site
        (headChildVertexInParent (a := a) (C := C) (rest := rest) v.1) := by
  unfold ketAtPathClean
  by_cases hp :
      (0 :: v.1.1) ∈ RTree.addresses (RTree.node a (C :: rest))
  · rw [dif_pos hp]
    congr 1
  · exact False.elim
      (hp (headChildVertexInParent
        (a := a) (C := C) (rest := rest) v.1).2)

theorem braAtPathClean_headChildNonRoot
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (v : NonRootVertex C) :
    braAtPathClean A site (0 :: v.1.1) =
      braAtVertexClean A site
        (headChildVertexInParent (a := a) (C := C) (rest := rest) v.1) := by
  unfold braAtPathClean
  by_cases hp :
      (0 :: v.1.1) ∈ RTree.addresses (RTree.node a (C :: rest))
  · rw [dif_pos hp]
    congr 1
  · exact False.elim
      (hp (headChildVertexInParent
        (a := a) (C := C) (rest := rest) v.1).2)

theorem parentHeadData_childNonRootPulledKet_eq_data_extract
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (v : NonRootVertex C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let parentDom :=
      nonRootDomainOfSiteClean site
        (headChildNonRootInParent
          (a := a) (C := C) (rest := rest) v) 0
    headChildPulledKetAtPathFromParent A site v.1.1 =
      ((data
        (headNonRootParentDomainIndex n a C rest hC v parentDom)).2).nodeField
        v (headNonRootParentDomainChildDomain
          n a C rest hC v parentDom) := by
  intro head Aopen A parentDom
  unfold headChildPulledKetAtPathFromParent
  rw [ketAtPathClean_headChildNonRoot]
  exact parentHeadData_childNonRootKetAtVertex_eq_data_extract
    n a C rest hC P root data tail site v

theorem parentHeadDiagData_childNonRootPulledKet_eq_data
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (v : NonRootVertex C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    headChildPulledKetAtPathFromParent A site v.1.1 =
      ((data (headChildIndexParentRoot idx,
        headChildIndexTail idx,
        headChildIndexRootDiag idx -
          normalSiteCleanRootTotalDiag n C childSite)).2).nodeField
        v (nonRootDomainOfSiteClean childSite v 0) := by
  intro head Aopen A site
  rw [parentHeadData_childNonRootPulledKet_eq_data_extract]
  rw [headNonRootParentDomainIndex_headDiagIndexEquiv_symm]
  rw [headNonRootParentDomainChildDomain_headDiagIndexEquiv_symm]

theorem parentHeadDiagData_childNonRootPulledKet_eq_shearedData
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (v : NonRootVertex C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    headChildPulledKetAtPathFromParent A site v.1.1 =
      ((headTotalShearDataWithBridge n a C rest
        P.rootCopenBridge data)
        (headChildIndexParentRoot idx,
          headChildIndexTail idx,
          headChildIndexRootDiag idx +
            normalSiteCleanCopenTotalDiag n C childSite)).2.nodeField
        v (nonRootDomainOfSiteClean childSite v 0) := by
  intro head Aopen A site
  rw [parentHeadDiagData_childNonRootPulledKet_eq_data]
  have hidx :
      ((headChildIndexParentRoot idx, headChildIndexTail idx,
          headChildIndexRootDiag idx +
            normalSiteCleanCopenTotalDiag n C childSite) :
          HeadChildIndex n a rest) =
        (headChildIndexParentRoot idx, headChildIndexTail idx,
          headChildIndexRootDiag idx -
            normalSiteCleanRootTotalDiag n C childSite +
            normalSiteCleanTotalDiag n C childSite) := by
    ext <;> simp [headChildIndexParentRoot, headChildIndexTail,
      headChildIndexRootDiag, normalSiteCleanTotalDiag]
    abel
  rw [hidx]
  exact (headTotalShearDataWithBridge_node_site_zero_total
    n a C rest P.rootCopenBridge data
    (headChildIndexParentRoot idx)
    (headChildIndexTail idx)
    (headChildIndexRootDiag idx -
      normalSiteCleanRootTotalDiag n C childSite)
    childSite v).symm

theorem parentHeadData_childNonRootBraAtVertex_eq_data_extract
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (v : NonRootVertex C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let parentDom :=
      nonRootDomainOfSiteClean site
        (headChildNonRootInParent
          (a := a) (C := C) (rest := rest) v) 1
    braAtVertexClean A site
        (headChildVertexInParent (a := a) (C := C) (rest := rest) v.1) =
      ((data
        (headNonRootParentDomainIndex n a C rest hC v parentDom)).2).nodeField
        v (headNonRootParentDomainChildDomain
          n a C rest hC v parentDom) := by
  intro head Aopen A parentDom
  have hvertex :
      (⟨headChildVertexInParent
          (a := a) (C := C) (rest := rest) v.1,
        by
          simp [headChildVertexInParent_addr]⟩ :
        NonRootVertex (RTree.node a (C :: rest))) =
      headChildNonRootInParent (a := a) (C := C) (rest := rest) v := by
    apply Subtype.ext
    rfl
  unfold braAtVertexClean
  rw [dif_neg]
  · change
      A.nodeField
        (⟨headChildVertexInParent
            (a := a) (C := C) (rest := rest) v.1,
          ?_⟩ :
          NonRootVertex (RTree.node a (C :: rest)))
        (nonRootDomainOfSiteClean site
          (⟨headChildVertexInParent
              (a := a) (C := C) (rest := rest) v.1,
            ?_⟩ :
            NonRootVertex (RTree.node a (C :: rest))) 1) =
        _
    rw [hvertex]
    change Aopen.nodeField
        (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
        parentDom = _
    rw [openNormalAssignmentCleanEquivHeadTail_symm_nodeField_head_nonroot]
    have hdata :=
      parentOpenHeadFieldsEquivHeadChildOpenData_symm_apply_nonroot
      n a C rest hC P data
      (headNonRootParentDomainIndex n a C rest hC v parentDom)
      v
      (headNonRootParentDomainChildDomain n a C rest hC v parentDom)
    have hconstruct :=
      headNonRootParentDomain_construct_extract n a C rest hC v parentDom
    rw [hconstruct] at hdata
    exact hdata
  · intro hroot
    simp [headChildVertexInParent_addr] at hroot

theorem parentHeadData_childNonRootPulledBra_eq_data_extract
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (v : NonRootVertex C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let parentDom :=
      nonRootDomainOfSiteClean site
        (headChildNonRootInParent
          (a := a) (C := C) (rest := rest) v) 1
    headChildPulledBraAtPathFromParent A site v.1.1 =
      ((data
        (headNonRootParentDomainIndex n a C rest hC v parentDom)).2).nodeField
        v (headNonRootParentDomainChildDomain
          n a C rest hC v parentDom) := by
  intro head Aopen A parentDom
  unfold headChildPulledBraAtPathFromParent
  rw [braAtPathClean_headChildNonRoot]
  exact parentHeadData_childNonRootBraAtVertex_eq_data_extract
    n a C rest hC P root data tail site v

theorem parentHeadDiagData_childNonRootPulledBra_eq_data
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (v : NonRootVertex C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    headChildPulledBraAtPathFromParent A site v.1.1 =
      ((data (headChildIndexParentRoot idx,
        headChildIndexTail idx,
        headChildIndexRootDiag idx -
          normalSiteCleanRootTotalDiag n C childSite)).2).nodeField
        v (nonRootDomainOfSiteClean childSite v 1) := by
  intro head Aopen A site
  rw [parentHeadData_childNonRootPulledBra_eq_data_extract]
  rw [headNonRootParentDomainIndex_headDiagIndexEquiv_symm]
  rw [headNonRootParentDomainChildDomain_headDiagIndexEquiv_symm]

theorem parentHeadDiagData_childNonRootPulledBra_eq_shearedData
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (v : NonRootVertex C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    headChildPulledBraAtPathFromParent A site v.1.1 =
      ((headTotalShearDataWithBridge n a C rest
        P.rootCopenBridge data)
        (headChildIndexParentRoot idx,
          headChildIndexTail idx,
          headChildIndexRootDiag idx +
            normalSiteCleanCopenTotalDiag n C childSite + 1)).2.nodeField
        v (nonRootDomainOfSiteClean childSite v 1) := by
  intro head Aopen A site
  rw [parentHeadDiagData_childNonRootPulledBra_eq_data]
  have hidx :
      ((headChildIndexParentRoot idx, headChildIndexTail idx,
          headChildIndexRootDiag idx +
            normalSiteCleanCopenTotalDiag n C childSite + 1) :
          HeadChildIndex n a rest) =
        (headChildIndexParentRoot idx, headChildIndexTail idx,
          headChildIndexRootDiag idx -
            normalSiteCleanRootTotalDiag n C childSite +
            normalSiteCleanTotalDiag n C childSite + 1) := by
    ext <;> simp [headChildIndexParentRoot, headChildIndexTail,
      headChildIndexRootDiag, normalSiteCleanTotalDiag]
    abel
  rw [hidx]
  exact (headTotalShearDataWithBridge_node_site_one_total
    n a C rest P.rootCopenBridge data
    (headChildIndexParentRoot idx)
    (headChildIndexTail idx)
    (headChildIndexRootDiag idx -
      normalSiteCleanRootTotalDiag n C childSite)
    childSite v).symm

end Imbalance
end TreeGraph
