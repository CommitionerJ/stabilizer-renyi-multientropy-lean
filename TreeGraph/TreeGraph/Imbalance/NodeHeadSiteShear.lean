import TreeGraph.Imbalance.NodeHeadFiberShear

namespace TreeGraph
namespace Imbalance

noncomputable def headIndexChildSiteLastToDiagEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) :
    HeadChildIndex n a rest × NormalSiteClean n C ≃
      HeadChildIndex n a rest × NormalSiteClean n C where
  toFun P :=
    let Q :=
      blockLastToDiagPairEquiv n C.rootWeight
        (P.2.rootCoord, headChildIndexRootDiag P.1)
    ((headChildIndexParentRoot P.1, headChildIndexTail P.1, Q.2),
      { rootCoord := Q.1
        nonRootCoord := P.2.nonRootCoord })
  invFun P :=
    let Q :=
      (blockLastToDiagPairEquiv n C.rootWeight).symm
        (P.2.rootCoord, headChildIndexRootDiag P.1)
    ((headChildIndexParentRoot P.1, headChildIndexTail P.1, Q.2),
      { rootCoord := Q.1
        nonRootCoord := P.2.nonRootCoord })
  left_inv P := by
    rcases P with ⟨idx, site⟩
    rcases idx with ⟨parentRoot, tail, s⟩
    cases site with
    | mk rootCoord nonRootCoord =>
        ext <;>
          simp [blockLastToDiagPairEquiv, headChildIndexParentRoot,
            headChildIndexTail, headChildIndexRootDiag]
  right_inv P := by
    rcases P with ⟨idx, site⟩
    rcases idx with ⟨parentRoot, tail, s⟩
    cases site with
    | mk rootCoord nonRootCoord =>
        ext <;>
          simp [blockLastToDiagPairEquiv, headChildIndexParentRoot,
            headChildIndexTail, headChildIndexRootDiag]

theorem headIndexChildSiteLastToDiagEquiv_parentRoot
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexParentRoot
        ((headIndexChildSiteLastToDiagEquiv n a C rest (idx, site)).1) =
      headChildIndexParentRoot idx := by
  rfl

theorem headIndexChildSiteLastToDiagEquiv_tail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexTail
        ((headIndexChildSiteLastToDiagEquiv n a C rest (idx, site)).1) =
      headChildIndexTail idx := by
  rfl

theorem headIndexChildSiteLastToDiagEquiv_rootDiag
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexRootDiag
        ((headIndexChildSiteLastToDiagEquiv n a C rest (idx, site)).1) =
      headChildIndexRootDiag idx +
        ∑ i : Fin (C.rootWeight - 1), site.rootCoord i := by
  rfl

theorem headIndexChildSiteLastToDiagEquiv_site_rootCoord
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    ((headIndexChildSiteLastToDiagEquiv n a C rest (idx, site)).2).rootCoord =
      site.rootCoord := by
  rfl

theorem headIndexChildSiteLastToDiagEquiv_site_nonRootCoord
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    ((headIndexChildSiteLastToDiagEquiv n a C rest (idx, site)).2).nonRootCoord =
      site.nonRootCoord := by
  rfl

theorem headIndexChildSiteLastToDiagEquiv_rootDiag_eq_fullRootDiag
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexRootDiag
        ((headIndexChildSiteLastToDiagEquiv n a C rest (idx, site)).1) =
      diag n C.rootWeight
        ((blockSplitLastEquiv n C.rootWeight
            (rootWeight_pos_of_positiveWeights hC)).symm
          (site.rootCoord, headChildIndexRootDiag idx)) := by
  rw [headIndexChildSiteLastToDiagEquiv_rootDiag]
  have hdiag :=
    diag_eq_splitLast_sum n C.rootWeight
      (rootWeight_pos_of_positiveWeights hC)
      ((blockSplitLastEquiv n C.rootWeight
        (rootWeight_pos_of_positiveWeights hC)).symm
          (site.rootCoord, headChildIndexRootDiag idx))
  simp only [Equiv.apply_symm_apply] at hdiag
  rw [hdiag]
  abel

theorem headIndexChildSiteLastToDiagEquiv_symm_rootDiag
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexRootDiag
        (((headIndexChildSiteLastToDiagEquiv n a C rest).symm (idx, site)).1) =
      headChildIndexRootDiag idx -
        ∑ i : Fin (C.rootWeight - 1), site.rootCoord i := by
  rfl

theorem headIndexChildSiteLastToDiagEquiv_symm_site_rootCoord
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    (((headIndexChildSiteLastToDiagEquiv n a C rest).symm (idx, site)).2).rootCoord =
      site.rootCoord := by
  rfl

theorem headIndexChildSiteLastToDiagEquiv_symm_site_nonRootCoord
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    (((headIndexChildSiteLastToDiagEquiv n a C rest).symm (idx, site)).2).nonRootCoord =
      site.nonRootCoord := by
  rfl

theorem prod_headIndex_childSite_eq_prod_lastToDiag_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (w : HeadChildIndex n a rest × NormalSiteClean n C → ℤ) :
    (∏ idx : HeadChildIndex n a rest,
      ∏ site : NormalSiteClean n C, w (idx, site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          w ((headIndexChildSiteLastToDiagEquiv n a C rest).symm
            (idx, site)) := by
  classical
  let e := headIndexChildSiteLastToDiagEquiv n a C rest
  calc
    (∏ idx : HeadChildIndex n a rest,
      ∏ site : NormalSiteClean n C, w (idx, site)) =
        ∏ P : HeadChildIndex n a rest × NormalSiteClean n C, w P := by
          exact
            (Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun site : NormalSiteClean n C => w (idx, site))).symm
    _ =
        ∏ P : HeadChildIndex n a rest × NormalSiteClean n C,
          w (e.symm P) := by
          exact (Equiv.prod_comp e.symm w).symm
    _ =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          w ((headIndexChildSiteLastToDiagEquiv n a C rest).symm
            (idx, site)) := by
          exact
            Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun site : NormalSiteClean n C =>
                  w ((headIndexChildSiteLastToDiagEquiv
                    n a C rest).symm (idx, site)))

theorem prod_headIndex_childSite_eq_prod_lastToDiag_symm_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (w : HeadChildIndex n a rest → NormalSiteClean n C → ℤ) :
    (∏ idx : HeadChildIndex n a rest,
      ∏ site : NormalSiteClean n C, w idx site) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          w
            (((headIndexChildSiteLastToDiagEquiv n a C rest).symm
              (idx, site)).1)
            (((headIndexChildSiteLastToDiagEquiv n a C rest).symm
              (idx, site)).2) := by
  exact prod_headIndex_childSite_eq_prod_lastToDiag_symm
    n a C rest (fun P => w P.1 P.2)

noncomputable def normalSiteClean_node_headDiagIndexEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C) :
    NormalSiteClean n (RTree.node a (C :: rest)) ≃
      HeadChildIndex n a rest × NormalSiteClean n C :=
  (normalSiteClean_node_headIndexEquiv n a C rest hC).trans
    (headIndexChildSiteLastToDiagEquiv n a C rest)

theorem normalSiteClean_node_headDiagIndexEquiv_symm_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    (normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
        (idx, site) =
      (normalSiteClean_node_headIndexEquiv n a C rest hC).symm
        ((headIndexChildSiteLastToDiagEquiv n a C rest).symm
          (idx, site)) := by
  rfl

theorem headChildLocalSiteOfParent_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    headChildLocalSiteOfParent n a C rest hC
        ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
          (idx, childSite)) =
      childSite := by
  rw [normalSiteClean_node_headDiagIndexEquiv_symm_apply]
  rw [headChildLocalSiteOfParent_headIndexEquiv_symm]
  cases childSite
  rfl

theorem headChildSiteContextOfParent_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    headChildSiteContextOfParent n a C rest hC
        ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
          (idx, childSite)) =
      (headChildIndexParentRoot idx,
        headChildIndexRootDiag idx -
          ∑ i : Fin (C.rootWeight - 1), childSite.rootCoord i,
        headChildIndexTail idx) := by
  rw [normalSiteClean_node_headDiagIndexEquiv_symm_apply]
  rw [headChildSiteContextOfParent_headIndexEquiv_symm]
  rfl

theorem headBoundaryParentRootContext_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    headBoundaryParentRootContext n a C rest hC
        ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
          (idx, childSite)) =
      headChildIndexParentRoot idx := by
  rw [headBoundaryParentRootContext]
  rw [headChildSiteContextOfParent_headDiagIndexEquiv_symm]

theorem headBoundaryExtraRootCoord_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    headBoundaryExtraRootCoord n a C rest hC
        ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
          (idx, childSite)) =
      headChildIndexRootDiag idx -
        ∑ i : Fin (C.rootWeight - 1), childSite.rootCoord i := by
  rw [headBoundaryExtraRootCoord]
  rw [headChildSiteContextOfParent_headDiagIndexEquiv_symm]

theorem headBoundaryTailCoords_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    headBoundaryTailCoords n a C rest hC
        ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
          (idx, childSite)) =
      headChildIndexTail idx := by
  rw [headBoundaryTailCoords]
  rw [headChildSiteContextOfParent_headDiagIndexEquiv_symm]

theorem normalSiteClean_node_headIndexEquiv_symm_childRootCoord
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (j : Fin C.rootWeight) :
    (((normalSiteClean_node_headIndexEquiv n a C rest hC).symm
          (idx, childSite)).nonRootCoord
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
        (Fin.cast
          (headChildRootNonRootInParent_weight_eq_rootWeight
            (a := a) (C := C) (rest := rest)).symm j)) =
      ((blockSplitLastEquiv n C.rootWeight
          (rootWeight_pos_of_positiveWeights hC)).symm
        (childSite.rootCoord, headChildIndexRootDiag idx)) j := by
  unfold normalSiteClean_node_headIndexEquiv normalSiteClean_node_headEquiv
  change
    ((parentNonRootCoordsHeadTailEquiv n a C rest).symm
      ((vertexCoordDomainEquivExtraSite n C hC).symm
        (headChildIndexRootDiag idx, childSite), headChildIndexTail idx))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
      (Fin.cast
        (headChildRootNonRootInParent_weight_eq_rootWeight
          (a := a) (C := C) (rest := rest)).symm j) =
      ((blockSplitLastEquiv n C.rootWeight
          (rootWeight_pos_of_positiveWeights hC)).symm
        (childSite.rootCoord, headChildIndexRootDiag idx)) j
  rw [parentNonRootCoordsHeadTailEquiv_symm_head_root]
  cases C with
  | node b cs =>
      dsimp [vertexCoordDomainEquivExtraSite,
        splitFullRootOpenEquivExtraSite, vertexCoordDomainEquivCplus,
        vertexCoordDomainNodeEquivBlockNonRoot]
      rfl

theorem diagonalClean_headChildRoot_headIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    diagonalClean
        ((normalSiteClean_node_headIndexEquiv n a C rest hC).symm
          (idx, childSite))
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) =
      diag n C.rootWeight
        ((blockSplitLastEquiv n C.rootWeight
            (rootWeight_pos_of_positiveWeights hC)).symm
          (childSite.rootCoord, headChildIndexRootDiag idx)) := by
  unfold diagonalClean diag
  let h := headChildRootNonRootInParent_weight_eq_rootWeight
    (a := a) (C := C) (rest := rest)
  refine Fintype.sum_equiv (finCastEquivOfEqClean h)
    (fun j =>
      ((normalSiteClean_node_headIndexEquiv n a C rest hC).symm
        (idx, childSite)).nonRootCoord
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) j)
    (fun j =>
      ((blockSplitLastEquiv n C.rootWeight
        (rootWeight_pos_of_positiveWeights hC)).symm
          (childSite.rootCoord, headChildIndexRootDiag idx)) j)
    ?_
  intro j
  dsimp [finCastEquivOfEqClean]
  simpa [h] using
    normalSiteClean_node_headIndexEquiv_symm_childRootCoord
      n a C rest hC idx childSite (Fin.cast h j)

theorem diagonalClean_headChildRoot_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    diagonalClean
        ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
          (idx, childSite))
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) =
      headChildIndexRootDiag idx := by
  rw [normalSiteClean_node_headDiagIndexEquiv_symm_apply]
  rw [diagonalClean_headChildRoot_headIndexEquiv_symm]
  let E := headIndexChildSiteLastToDiagEquiv n a C rest
  let P : HeadChildIndex n a rest × NormalSiteClean n C := (idx, childSite)
  let oldP : HeadChildIndex n a rest × NormalSiteClean n C := E.symm P
  have hroot :
      headChildIndexRootDiag (E oldP).1 = headChildIndexRootDiag idx := by
    have hpair : E oldP = P := by
      exact E.right_inv P
    exact congrArg (fun Q => headChildIndexRootDiag Q.1) hpair
  have hdiag :=
    headIndexChildSiteLastToDiagEquiv_rootDiag_eq_fullRootDiag
      n a C rest hC oldP.1 oldP.2
  dsimp [oldP, P, E] at hroot hdiag ⊢
  rw [← hroot]
  exact hdiag.symm

theorem headChildLocalOpenCoordOfParentSite_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    headChildLocalOpenCoordOfParentSite n a C rest hC
        ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
          (idx, childSite)) =
      (rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord := by
  unfold headChildLocalOpenCoordOfParentSite
  rw [headChildLocalSiteOfParent_headDiagIndexEquiv_symm]

theorem headBoundaryOpenPairingDataExpressionAtSite_headDiagIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    headBoundaryOpenPairingDataExpressionAtSite n a C rest hC root Aopen
        ((normalSiteClean_node_headDiagIndexEquiv n a C rest hC).symm
          (idx, childSite)) =
      headBoundaryParentRootKet (closeOpenNormalAssignmentClean root Aopen)
          ((normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)) *
        headChildRootBoundaryFieldFromParent n a C rest hC Aopen
          (headChildIndexParentRoot idx) (headChildIndexTail idx)
          (headChildIndexRootDiag idx)
          ((rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord) +
      headBoundaryParentRootBra (closeOpenNormalAssignmentClean root Aopen)
          ((normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)) *
        headChildRootBoundaryFieldFromParent n a C rest hC Aopen
          (headChildIndexParentRoot idx) (headChildIndexTail idx)
          (headChildIndexRootDiag idx + 1)
          ((rootFieldDomainCleanEquivCopen n C) childSite.nonRootCoord) := by
  unfold headBoundaryOpenPairingDataExpressionAtSite
  rw [diagonalClean_headChildRoot_headDiagIndexEquiv_symm]
  rw [headBoundaryParentRootContext_headDiagIndexEquiv_symm]
  rw [headBoundaryTailCoords_headDiagIndexEquiv_symm]
  rw [headChildLocalOpenCoordOfParentSite_headDiagIndexEquiv_symm]

theorem prod_normalSiteClean_node_eq_prod_headDiagIndex_childSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (w : NormalSiteClean n (RTree.node a (C :: rest)) → ℤ) :
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)), w site) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          w ((normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)) := by
  classical
  let e := normalSiteClean_node_headDiagIndexEquiv n a C rest hC
  calc
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)), w site) =
        ∏ P : HeadChildIndex n a rest × NormalSiteClean n C,
          w (e.symm P) := by
          exact (Equiv.prod_comp e.symm w).symm
    _ =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          w ((normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)) := by
          exact
            Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun childSite : NormalSiteClean n C =>
                  w ((normalSiteClean_node_headDiagIndexEquiv
                    n a C rest hC).symm (idx, childSite)))

theorem prod_headBoundaryPhaseAtSiteClean_node_eq_headDiagIndex_childSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
      chi (headBoundaryPhaseAtSiteClean_node C rest A site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headBoundaryPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headDiagIndexEquiv
              n a C rest hC).symm (idx, childSite))) := by
  exact prod_normalSiteClean_node_eq_prod_headDiagIndex_childSite
    n a C rest hC
    (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
      chi (headBoundaryPhaseAtSiteClean_node C rest A site))

theorem prod_headInternalPhaseAtSiteClean_node_eq_headDiagIndex_childSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
      chi (headInternalPhaseAtSiteClean_node C rest A site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headInternalPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headDiagIndexEquiv
              n a C rest hC).symm (idx, childSite))) := by
  exact prod_normalSiteClean_node_eq_prod_headDiagIndex_childSite
    n a C rest hC
    (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
      chi (headInternalPhaseAtSiteClean_node C rest A site))

theorem prod_headBoundaryPhaseAtSiteClean_node_eq_headDiagIndex_dataOpenPairing
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
      chi (headBoundaryPhaseAtSiteClean_node C rest
        (closeOpenNormalAssignmentClean root Aopen) site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headBoundaryOpenPairingDataExpressionAtSite
            n a C rest hC root Aopen
            ((normalSiteClean_node_headDiagIndexEquiv
              n a C rest hC).symm (idx, childSite))) := by
  classical
  rw [prod_headBoundaryPhaseAtSiteClean_node_eq_headDiagIndex_childSite]
  exact Finset.prod_congr rfl (by
    intro idx _
    exact Finset.prod_congr rfl (by
      intro childSite _
      rw [headBoundaryPhaseAtSiteClean_node_eq_dataOpenPairingAtSite]))

theorem parentHeadPhaseSiteProductAtHeadTail_eq_headDiagIndexProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) :
    parentHeadPhaseSiteProductAtHeadTail n a C rest root head tail =
      let A :=
        closeOpenNormalAssignmentClean root
          ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
            (head, tail))
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headBoundaryPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headDiagIndexEquiv
              n a C rest hC).symm (idx, childSite)))) *
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headInternalPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headDiagIndexEquiv
              n a C rest hC).symm (idx, childSite)))) := by
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  change
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headInternalPhaseAtSiteClean_node C rest A site)) =
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headBoundaryPhaseAtSiteClean_node C rest A
          ((normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)))) *
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headInternalPhaseAtSiteClean_node C rest A
          ((normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite))))
  rw [prod_headBoundaryPhaseAtSiteClean_node_eq_headDiagIndex_childSite]
  rw [prod_headInternalPhaseAtSiteClean_node_eq_headDiagIndex_childSite]

noncomputable def parentHeadDiagDataInternalPhaseAtHeadIndexChildSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) : F2 :=
  let Aopen :=
    (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)
  let site :=
    (normalSiteClean_node_headDiagIndexEquiv
      n a C rest hC).symm (idx, childSite)
  headBoundaryOpenPairingDataExpressionAtSite
      n a C rest hC root Aopen site +
    headInternalPhaseAtSiteClean_node C rest
      (closeOpenNormalAssignmentClean root Aopen) site

theorem parentHeadPhaseSiteProductAtHeadTail_eq_prod_diagDataInternalPhase
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) :
    parentHeadPhaseSiteProductAtHeadTail n a C rest root head tail =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (parentHeadDiagDataInternalPhaseAtHeadIndexChildSite
            n a C rest hC root head tail idx childSite) := by
  classical
  let Aopen :=
    (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)
  let A := closeOpenNormalAssignmentClean root Aopen
  have hboundary :
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headBoundaryPhaseAtSiteClean_node C rest A site)) =
        ∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C,
            chi (headBoundaryOpenPairingDataExpressionAtSite
              n a C rest hC root Aopen
              ((normalSiteClean_node_headDiagIndexEquiv
                n a C rest hC).symm (idx, childSite))) := by
    simpa [A, Aopen] using
      prod_headBoundaryPhaseAtSiteClean_node_eq_headDiagIndex_dataOpenPairing
        n a C rest hC root Aopen
  have hinternal :
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headInternalPhaseAtSiteClean_node C rest A site)) =
        ∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C,
            chi (headInternalPhaseAtSiteClean_node C rest A
              ((normalSiteClean_node_headDiagIndexEquiv
                n a C rest hC).symm (idx, childSite))) := by
    simpa [A] using
      prod_headInternalPhaseAtSiteClean_node_eq_headDiagIndex_childSite
        n a C rest hC A
  unfold parentHeadPhaseSiteProductAtHeadTail
  change
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
      chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
      chi (headInternalPhaseAtSiteClean_node C rest A site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (parentHeadDiagDataInternalPhaseAtHeadIndexChildSite
            n a C rest hC root head tail idx childSite)
  rw [hboundary, hinternal]
  change
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headBoundaryOpenPairingDataExpressionAtSite
          n a C rest hC root Aopen
          ((normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)))) *
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headInternalPhaseAtSiteClean_node C rest A
          ((normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)))) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headBoundaryOpenPairingDataExpressionAtSite
              n a C rest hC root Aopen
              ((normalSiteClean_node_headDiagIndexEquiv
                n a C rest hC).symm (idx, childSite)) +
            headInternalPhaseAtSiteClean_node C rest A
              ((normalSiteClean_node_headDiagIndexEquiv
                n a C rest hC).symm (idx, childSite)))
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (by
    intro idx _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (by
      intro childSite _
      rw [chi_add]))

end Imbalance
end TreeGraph
