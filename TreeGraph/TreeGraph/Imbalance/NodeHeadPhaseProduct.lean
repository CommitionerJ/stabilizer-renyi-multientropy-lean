import TreeGraph.Imbalance.HeadOpenFubini
import TreeGraph.Imbalance.NodeOpenHeadTailPhase

namespace TreeGraph
namespace Imbalance

theorem chi_totalHeadPhaseClean_node_eq_boundary_mul_internal
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    chi (totalHeadPhaseClean_node n a C rest A) =
      chi (totalHeadBoundaryPhaseClean_node n a C rest A) *
        chi (totalHeadInternalPhaseClean_node n a C rest A) := by
  unfold totalHeadPhaseClean_node
  rw [chi_add]

theorem chi_totalHeadBoundaryPhaseClean_node_eq_prod_site
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    chi (totalHeadBoundaryPhaseClean_node n a C rest A) =
      ∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headBoundaryPhaseAtSiteClean_node C rest A site) := by
  unfold totalHeadBoundaryPhaseClean_node
  exact chi_sum_univ_apply
    (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
      headBoundaryPhaseAtSiteClean_node C rest A site)

theorem chi_totalHeadInternalPhaseClean_node_eq_prod_site
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    chi (totalHeadInternalPhaseClean_node n a C rest A) =
      ∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headInternalPhaseAtSiteClean_node C rest A site) := by
  unfold totalHeadInternalPhaseClean_node
  exact chi_sum_univ_apply
    (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
      headInternalPhaseAtSiteClean_node C rest A site)

theorem chi_totalHeadPhaseClean_node_eq_prod_boundary_mul_prod_internal
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    chi (totalHeadPhaseClean_node n a C rest A) =
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headInternalPhaseAtSiteClean_node C rest A site)) := by
  rw [chi_totalHeadPhaseClean_node_eq_boundary_mul_internal]
  rw [chi_totalHeadBoundaryPhaseClean_node_eq_prod_site]
  rw [chi_totalHeadInternalPhaseClean_node_eq_prod_site]

theorem chi_totalTailPhaseClean_node_eq_boundary_mul_internal
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    chi (totalTailPhaseClean_node n a C rest A) =
      chi (totalTailBoundaryPhaseClean_node n a C rest A) *
        chi (totalTailInternalPhaseClean_node n a C rest A) := by
  unfold totalTailPhaseClean_node
  rw [chi_add]

theorem chi_totalTailBoundaryPhaseClean_node_eq_prod_site
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    chi (totalTailBoundaryPhaseClean_node n a C rest A) =
      ∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (tailBoundaryPhaseAtSiteClean_node C rest A site) := by
  unfold totalTailBoundaryPhaseClean_node
  exact chi_sum_univ_apply
    (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
      tailBoundaryPhaseAtSiteClean_node C rest A site)

theorem chi_totalTailInternalPhaseClean_node_eq_prod_site
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    chi (totalTailInternalPhaseClean_node n a C rest A) =
      ∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (tailInternalPhaseAtSiteClean_node C rest A site) := by
  unfold totalTailInternalPhaseClean_node
  exact chi_sum_univ_apply
    (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
      tailInternalPhaseAtSiteClean_node C rest A site)

theorem chi_totalTailPhaseClean_node_eq_prod_boundary_mul_prod_internal
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    chi (totalTailPhaseClean_node n a C rest A) =
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (tailBoundaryPhaseAtSiteClean_node C rest A site)) *
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (tailInternalPhaseAtSiteClean_node C rest A site)) := by
  rw [chi_totalTailPhaseClean_node_eq_boundary_mul_internal]
  rw [chi_totalTailBoundaryPhaseClean_node_eq_prod_site]
  rw [chi_totalTailInternalPhaseClean_node_eq_prod_site]

noncomputable def headChildSiteContextEquivIndex
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    HeadChildSiteContext n a C rest ≃ HeadChildIndex n a rest where
  toFun ctx := (ctx.1, ctx.2.2, ctx.2.1)
  invFun idx := (idx.1, idx.2.2, idx.2.1)
  left_inv := by
    intro ctx
    rcases ctx with ⟨q, s, tail⟩
    rfl
  right_inv := by
    intro idx
    rcases idx with ⟨q, tail, s⟩
    rfl

noncomputable def normalSiteClean_node_headIndexEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C) :
    NormalSiteClean n (RTree.node a (C :: rest)) ≃
      HeadChildIndex n a rest × NormalSiteClean n C :=
  (normalSiteClean_node_headEquiv n a C rest hC).trans
    (Equiv.prodCongr
      (headChildSiteContextEquivIndex n a C rest)
      (Equiv.refl (NormalSiteClean n C)))

theorem headChildLocalSiteOfParent_headIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    headChildLocalSiteOfParent n a C rest hC
      ((normalSiteClean_node_headIndexEquiv n a C rest hC).symm
        (idx, childSite)) = childSite := by
  unfold headChildLocalSiteOfParent normalSiteClean_node_headIndexEquiv
  simp

theorem headChildSiteContextOfParent_headIndexEquiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    headChildSiteContextOfParent n a C rest hC
      ((normalSiteClean_node_headIndexEquiv n a C rest hC).symm
        (idx, childSite)) =
      (headChildIndexParentRoot idx,
        headChildIndexRootDiag idx, headChildIndexTail idx) := by
  unfold headChildSiteContextOfParent normalSiteClean_node_headIndexEquiv
  simp [headChildSiteContextEquivIndex, headChildIndexParentRoot,
    headChildIndexRootDiag, headChildIndexTail]

theorem prod_normalSiteClean_node_eq_prod_headIndex_childSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (w : NormalSiteClean n (RTree.node a (C :: rest)) → ℤ) :
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)), w site) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          w ((normalSiteClean_node_headIndexEquiv
            n a C rest hC).symm (idx, childSite)) := by
  classical
  let e := normalSiteClean_node_headIndexEquiv n a C rest hC
  calc
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)), w site) =
        ∏ P : HeadChildIndex n a rest × NormalSiteClean n C,
          w (e.symm P) := by
          exact (Equiv.prod_comp e.symm w).symm
    _ =
        ∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C,
            w ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)) := by
          rw [Fintype.prod_prod_type]

theorem prod_headBoundaryPhaseAtSiteClean_node_eq_headIndex_childSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
      chi (headBoundaryPhaseAtSiteClean_node C rest A site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headBoundaryPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite))) := by
  exact prod_normalSiteClean_node_eq_prod_headIndex_childSite
    n a C rest hC
    (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
      chi (headBoundaryPhaseAtSiteClean_node C rest A site))

theorem prod_headInternalPhaseAtSiteClean_node_eq_headIndex_childSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
      chi (headInternalPhaseAtSiteClean_node C rest A site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headInternalPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite))) := by
  exact prod_normalSiteClean_node_eq_prod_headIndex_childSite
    n a C rest hC
    (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
      chi (headInternalPhaseAtSiteClean_node C rest A site))

theorem prod_tailBoundaryPhaseAtSiteClean_node_eq_headIndex_childSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
      chi (tailBoundaryPhaseAtSiteClean_node C rest A site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (tailBoundaryPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite))) := by
  exact prod_normalSiteClean_node_eq_prod_headIndex_childSite
    n a C rest hC
    (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
      chi (tailBoundaryPhaseAtSiteClean_node C rest A site))

theorem prod_tailInternalPhaseAtSiteClean_node_eq_headIndex_childSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
      chi (tailInternalPhaseAtSiteClean_node C rest A site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (tailInternalPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite))) := by
  exact prod_normalSiteClean_node_eq_prod_headIndex_childSite
    n a C rest hC
    (fun site : NormalSiteClean n (RTree.node a (C :: rest)) =>
      chi (tailInternalPhaseAtSiteClean_node C rest A site))

theorem prod_headBoundaryPhaseAtSiteClean_node_eq_headIndex_dataOpenPairing
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
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite))) := by
  classical
  rw [prod_headBoundaryPhaseAtSiteClean_node_eq_headIndex_childSite]
  exact Finset.prod_congr rfl (by
    intro idx _
    exact Finset.prod_congr rfl (by
      intro childSite _
      rw [headBoundaryPhaseAtSiteClean_node_eq_dataOpenPairingAtSite]))

theorem chi_totalHeadPhaseClean_node_eq_headIndexProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    chi (totalHeadPhaseClean_node n a C rest A) =
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headBoundaryPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)))) *
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headInternalPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)))) := by
  rw [chi_totalHeadPhaseClean_node_eq_prod_boundary_mul_prod_internal]
  rw [prod_headBoundaryPhaseAtSiteClean_node_eq_headIndex_childSite]
  rw [prod_headInternalPhaseAtSiteClean_node_eq_headIndex_childSite]

theorem chi_totalTailPhaseClean_node_eq_headIndexProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest))) :
    chi (totalTailPhaseClean_node n a C rest A) =
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (tailBoundaryPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)))) *
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (tailInternalPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)))) := by
  rw [chi_totalTailPhaseClean_node_eq_prod_boundary_mul_prod_internal]
  rw [prod_tailBoundaryPhaseAtSiteClean_node_eq_headIndex_childSite]
  rw [prod_tailInternalPhaseAtSiteClean_node_eq_headIndex_childSite]

noncomputable def parentHeadPhaseSiteProductAtHeadTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) : ℤ :=
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
    chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
  (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
    chi (headInternalPhaseAtSiteClean_node C rest A site))

noncomputable def parentTailPhaseSiteProductAtHeadTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) : ℤ :=
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
    chi (tailBoundaryPhaseAtSiteClean_node C rest A site)) *
  (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
    chi (tailInternalPhaseAtSiteClean_node C rest A site))

theorem parentHeadPhaseSiteProductAtHeadTail_eq_headIndexProducts
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
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)))) *
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headInternalPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
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
          ((normalSiteClean_node_headIndexEquiv
            n a C rest hC).symm (idx, childSite)))) *
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headInternalPhaseAtSiteClean_node C rest A
          ((normalSiteClean_node_headIndexEquiv
            n a C rest hC).symm (idx, childSite))))
  rw [prod_headBoundaryPhaseAtSiteClean_node_eq_headIndex_childSite]
  rw [prod_headInternalPhaseAtSiteClean_node_eq_headIndex_childSite]

theorem parentHeadPhaseSiteProductAtHeadTail_eq_dataOpenPairing_mul_internal
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) :
    parentHeadPhaseSiteProductAtHeadTail n a C rest root head tail =
      let Aopen :=
        (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail)
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headBoundaryOpenPairingDataExpressionAtSite
            n a C rest hC root Aopen
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)))) *
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headInternalPhaseAtSiteClean_node C rest
            (closeOpenNormalAssignmentClean root Aopen)
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)))) := by
  let Aopen :=
    (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)
  let A := closeOpenNormalAssignmentClean root Aopen
  change
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headInternalPhaseAtSiteClean_node C rest A site)) =
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headBoundaryOpenPairingDataExpressionAtSite
          n a C rest hC root Aopen
          ((normalSiteClean_node_headIndexEquiv
            n a C rest hC).symm (idx, childSite)))) *
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headInternalPhaseAtSiteClean_node C rest A
          ((normalSiteClean_node_headIndexEquiv
            n a C rest hC).symm (idx, childSite))))
  rw [prod_headBoundaryPhaseAtSiteClean_node_eq_headIndex_dataOpenPairing]
  rw [prod_headInternalPhaseAtSiteClean_node_eq_headIndex_childSite]

noncomputable def parentHeadDataInternalPhaseAtHeadIndexChildSite
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
    (normalSiteClean_node_headIndexEquiv
      n a C rest hC).symm (idx, childSite)
  headBoundaryOpenPairingDataExpressionAtSite
      n a C rest hC root Aopen site +
    headInternalPhaseAtSiteClean_node C rest
      (closeOpenNormalAssignmentClean root Aopen) site

theorem parentHeadPhaseSiteProductAtHeadTail_eq_prod_dataInternalPhase
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) :
    parentHeadPhaseSiteProductAtHeadTail n a C rest root head tail =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
            n a C rest hC root head tail idx childSite) := by
  classical
  rw [parentHeadPhaseSiteProductAtHeadTail_eq_dataOpenPairing_mul_internal]
  change
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headBoundaryOpenPairingDataExpressionAtSite
          n a C rest hC root
          ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
            (head, tail))
          ((normalSiteClean_node_headIndexEquiv
            n a C rest hC).symm (idx, childSite)))) *
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headInternalPhaseAtSiteClean_node C rest
          (closeOpenNormalAssignmentClean root
            ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
              (head, tail)))
          ((normalSiteClean_node_headIndexEquiv
            n a C rest hC).symm (idx, childSite)))) =
    ∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headBoundaryOpenPairingDataExpressionAtSite
            n a C rest hC root
            ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
              (head, tail))
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)) +
          headInternalPhaseAtSiteClean_node C rest
            (closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
                (head, tail)))
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)))
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (by
    intro idx _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (by
      intro childSite _
      rw [chi_add]))

theorem parentHeadFieldsDataWeightAtHead_eq_prod_index_weight_character
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) :
    parentHeadFieldsDataWeightAtHead n a C rest hC P root head =
      ∏ idx : HeadChildIndex n a rest,
        let data :=
          (parentOpenHeadFieldsEquivHeadChildOpenData
            n a C rest hC P) head
        weightClean C (closeOpenNormalAssignmentClean
          (data idx).1 (data idx).2) *
          chi (headChildIndexBranchCoeff n a C rest hC P root idx
            (headChildOpenDataRootMessage
              n a C rest hC P root (data idx).1)) := by
  classical
  let data :=
    (parentOpenHeadFieldsEquivHeadChildOpenData
      n a C rest hC P) head
  change
    (∏ idx : HeadChildIndex n a rest,
      weightClean C (closeOpenNormalAssignmentClean
        (data idx).1 (data idx).2)) *
      chi (headChildOpenDataBoundaryExponent
        n a C rest hC P root data) =
    ∏ idx : HeadChildIndex n a rest,
      weightClean C (closeOpenNormalAssignmentClean
        (data idx).1 (data idx).2) *
        chi (headChildIndexBranchCoeff n a C rest hC P root idx
          (headChildOpenDataRootMessage
            n a C rest hC P root (data idx).1))
  rw [headChildOpenDataBoundaryExponent_eq_sum_index]
  rw [chi_sum_univ_apply]
  rw [← Finset.prod_mul_distrib]

theorem parentHeadPhaseSiteProductAtHeadTail_eq_parentHeadFieldsDataWeightAtHead_of_index
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (hidx :
      ∀ idx : HeadChildIndex n a rest,
        (∏ childSite : NormalSiteClean n C,
          chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
            n a C rest hC root head tail idx childSite)) =
          let data : HeadChildOpenData n a C rest :=
            (parentOpenHeadFieldsEquivHeadChildOpenData
              n a C rest hC P) head
          weightClean C (closeOpenNormalAssignmentClean
            (data idx).1 (data idx).2) *
            chi (headChildIndexBranchCoeff n a C rest hC P root idx
              (headChildOpenDataRootMessage
                n a C rest hC P root (data idx).1))) :
    parentHeadPhaseSiteProductAtHeadTail n a C rest root head tail =
      parentHeadFieldsDataWeightAtHead n a C rest hC P root head := by
  rw [parentHeadPhaseSiteProductAtHeadTail_eq_prod_dataInternalPhase
    n a C rest hC root head tail]
  rw [parentHeadFieldsDataWeightAtHead_eq_prod_index_weight_character
    n a C rest hC P root head]
  exact Finset.prod_congr rfl (by
    intro idx _
    rw [hidx idx])

theorem parentTailPhaseSiteProductAtHeadTail_eq_headIndexProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) :
    parentTailPhaseSiteProductAtHeadTail n a C rest root head tail =
      let A :=
        closeOpenNormalAssignmentClean root
          ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
            (head, tail))
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (tailBoundaryPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)))) *
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (tailInternalPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headIndexEquiv
              n a C rest hC).symm (idx, childSite)))) := by
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  change
    (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (tailBoundaryPhaseAtSiteClean_node C rest A site)) *
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (tailInternalPhaseAtSiteClean_node C rest A site)) =
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (tailBoundaryPhaseAtSiteClean_node C rest A
          ((normalSiteClean_node_headIndexEquiv
            n a C rest hC).symm (idx, childSite)))) *
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (tailInternalPhaseAtSiteClean_node C rest A
          ((normalSiteClean_node_headIndexEquiv
            n a C rest hC).symm (idx, childSite))))
  rw [prod_tailBoundaryPhaseAtSiteClean_node_eq_headIndex_childSite]
  rw [prod_tailInternalPhaseAtSiteClean_node_eq_headIndex_childSite]

theorem chi_totalHeadPhaseClean_node_eq_parentHeadPhaseSiteProductAtHeadTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) :
    let A :=
      closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail))
    chi (totalHeadPhaseClean_node n a C rest A) =
      parentHeadPhaseSiteProductAtHeadTail
        n a C rest root head tail := by
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  change
    chi (totalHeadPhaseClean_node n a C rest A) =
      parentHeadPhaseSiteProductAtHeadTail n a C rest root head tail
  rw [chi_totalHeadPhaseClean_node_eq_prod_boundary_mul_prod_internal]
  rfl

theorem chi_totalTailPhaseClean_node_eq_parentTailPhaseSiteProductAtHeadTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (tail : ParentOpenTailFields n a C rest) :
    let A :=
      closeOpenNormalAssignmentClean root
        ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
          (head, tail))
    chi (totalTailPhaseClean_node n a C rest A) =
      parentTailPhaseSiteProductAtHeadTail
        n a C rest root head tail := by
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  change
    chi (totalTailPhaseClean_node n a C rest A) =
      parentTailPhaseSiteProductAtHeadTail n a C rest root head tail
  rw [chi_totalTailPhaseClean_node_eq_prod_boundary_mul_prod_internal]
  rfl

theorem parentOpenTailPhaseProductAtHead_eq_sum_headSiteProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) :
    parentOpenTailPhaseProductAtHead n a C rest root head =
      ∑ tail : ParentOpenTailFields n a C rest,
        let A :=
          closeOpenNormalAssignmentClean root
            ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
              (head, tail))
        ((∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
            chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
          (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
            chi (headInternalPhaseAtSiteClean_node C rest A site))) *
          chi (totalTailPhaseClean_node n a C rest A) := by
  classical
  unfold parentOpenTailPhaseProductAtHead
  refine Finset.sum_congr rfl ?_
  intro tail _
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  change
    chi (totalHeadPhaseClean_node n a C rest A) *
        chi (totalTailPhaseClean_node n a C rest A) =
      ((∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
          chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
        (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
          chi (headInternalPhaseAtSiteClean_node C rest A site))) *
        chi (totalTailPhaseClean_node n a C rest A)
  rw [chi_totalHeadPhaseClean_node_eq_prod_boundary_mul_prod_internal]

theorem parentOpenTailPhaseSignedSumAtHead_eq_sum_tailSiteProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) :
    parentOpenTailPhaseSignedSumAtHead n a C rest root head =
      ∑ tail : ParentOpenTailFields n a C rest,
        let A :=
          closeOpenNormalAssignmentClean root
            ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
              (head, tail))
        (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
          chi (tailBoundaryPhaseAtSiteClean_node C rest A site)) *
        (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
          chi (tailInternalPhaseAtSiteClean_node C rest A site)) := by
  classical
  unfold parentOpenTailPhaseSignedSumAtHead
  refine Finset.sum_congr rfl ?_
  intro tail _
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  change
    chi (totalTailPhaseClean_node n a C rest A) =
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (tailBoundaryPhaseAtSiteClean_node C rest A site)) *
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (tailInternalPhaseAtSiteClean_node C rest A site))
  rw [chi_totalTailPhaseClean_node_eq_prod_boundary_mul_prod_internal]

theorem parentOpenTailPhaseProductAtHead_eq_sum_siteProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) :
    parentOpenTailPhaseProductAtHead n a C rest root head =
      ∑ tail : ParentOpenTailFields n a C rest,
        let A :=
          closeOpenNormalAssignmentClean root
            ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
              (head, tail))
        ((∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
            chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
          (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
            chi (headInternalPhaseAtSiteClean_node C rest A site))) *
          ((∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
              chi (tailBoundaryPhaseAtSiteClean_node C rest A site)) *
            (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
              chi (tailInternalPhaseAtSiteClean_node C rest A site))) := by
  classical
  rw [parentOpenTailPhaseProductAtHead_eq_sum_headSiteProducts]
  refine Finset.sum_congr rfl ?_
  intro tail _
  let A :=
    closeOpenNormalAssignmentClean root
      ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail))
  change
    ((∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
      (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
        chi (headInternalPhaseAtSiteClean_node C rest A site))) *
        chi (totalTailPhaseClean_node n a C rest A) =
      ((∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
          chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
        (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
          chi (headInternalPhaseAtSiteClean_node C rest A site))) *
        ((∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
            chi (tailBoundaryPhaseAtSiteClean_node C rest A site)) *
          (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
            chi (tailInternalPhaseAtSiteClean_node C rest A site)))
  rw [chi_totalTailPhaseClean_node_eq_prod_boundary_mul_prod_internal]

theorem openNormalSignedSumClean_eq_sum_head_tail_headSiteProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      ∑ head : ParentOpenHeadFields n a C rest,
        ∑ tail : ParentOpenTailFields n a C rest,
          let A :=
            closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
                (head, tail))
          ((∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
              chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
            (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
              chi (headInternalPhaseAtSiteClean_node C rest A site))) *
            chi (totalTailPhaseClean_node n a C rest A) := by
  rw [openNormalSignedSumClean_eq_sum_parentOpenTailPhaseProductAtHead]
  refine Finset.sum_congr rfl ?_
  intro head _
  rw [parentOpenTailPhaseProductAtHead_eq_sum_headSiteProducts]

theorem openNormalSignedSumClean_eq_sum_head_tail_siteProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      ∑ head : ParentOpenHeadFields n a C rest,
        ∑ tail : ParentOpenTailFields n a C rest,
          let A :=
            closeOpenNormalAssignmentClean root
              ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
                (head, tail))
          ((∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
              chi (headBoundaryPhaseAtSiteClean_node C rest A site)) *
            (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
              chi (headInternalPhaseAtSiteClean_node C rest A site))) *
            ((∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
                chi (tailBoundaryPhaseAtSiteClean_node C rest A site)) *
              (∏ site : NormalSiteClean n (RTree.node a (C :: rest)),
                chi (tailInternalPhaseAtSiteClean_node C rest A site))) := by
  rw [openNormalSignedSumClean_eq_sum_parentOpenTailPhaseProductAtHead]
  refine Finset.sum_congr rfl ?_
  intro head _
  rw [parentOpenTailPhaseProductAtHead_eq_sum_siteProducts]

theorem parentOpenTailPhaseSignedSumAtHead_eq_sum_tailSiteProduct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) :
    parentOpenTailPhaseSignedSumAtHead n a C rest root head =
      ∑ tail : ParentOpenTailFields n a C rest,
        parentTailPhaseSiteProductAtHeadTail
          n a C rest root head tail := by
  rw [parentOpenTailPhaseSignedSumAtHead_eq_sum_tailSiteProducts]
  rfl

theorem parentOpenTailPhaseProductAtHead_eq_sum_phaseSiteProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest) :
    parentOpenTailPhaseProductAtHead n a C rest root head =
      ∑ tail : ParentOpenTailFields n a C rest,
        parentHeadPhaseSiteProductAtHeadTail
          n a C rest root head tail *
          parentTailPhaseSiteProductAtHeadTail
            n a C rest root head tail := by
  rw [parentOpenTailPhaseProductAtHead_eq_sum_siteProducts]
  rfl

theorem openNormalSignedSumClean_eq_sum_head_tail_phaseSiteProducts
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      ∑ head : ParentOpenHeadFields n a C rest,
        ∑ tail : ParentOpenTailFields n a C rest,
          parentHeadPhaseSiteProductAtHeadTail
            n a C rest root head tail *
            parentTailPhaseSiteProductAtHeadTail
              n a C rest root head tail := by
  rw [openNormalSignedSumClean_eq_sum_parentOpenTailPhaseProductAtHead]
  refine Finset.sum_congr rfl ?_
  intro head _
  rw [parentOpenTailPhaseProductAtHead_eq_sum_phaseSiteProducts]

theorem openNormalSignedSumClean_eq_sum_parentHeadDataWeight_mul_tailPhaseSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (hhead :
      ∀ head : ParentOpenHeadFields n a C rest,
        ∀ tail : ParentOpenTailFields n a C rest,
          parentHeadPhaseSiteProductAtHeadTail
              n a C rest root head tail =
            parentHeadFieldsDataWeightAtHead
              n a C rest hC P root head) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      ∑ head : ParentOpenHeadFields n a C rest,
        parentHeadFieldsDataWeightAtHead
          n a C rest hC P root head *
          parentOpenTailPhaseSignedSumAtHead n a C rest root head := by
  classical
  exact
    openNormalSignedSumClean_eq_sum_headFactor_mul_tailPhaseSignedSum
      n a C rest root
      (fun head : ParentOpenHeadFields n a C rest =>
        parentHeadFieldsDataWeightAtHead n a C rest hC P root head)
      (by
        intro head tail
        let A :=
          closeOpenNormalAssignmentClean root
            ((openNormalAssignmentCleanEquivHeadTail n a C rest).symm
              (head, tail))
        change
          chi (totalHeadPhaseClean_node n a C rest A) =
            parentHeadFieldsDataWeightAtHead
              n a C rest hC P root head
        rw [show
          chi (totalHeadPhaseClean_node n a C rest A) =
            parentHeadPhaseSiteProductAtHeadTail
              n a C rest root head tail by
            simpa [A] using
              chi_totalHeadPhaseClean_node_eq_parentHeadPhaseSiteProductAtHeadTail
                n a C rest root head tail]
        exact hhead head tail)

theorem openNormalSignedSumClean_eq_sum_parentHeadDataWeight_mul_tailPhaseSignedSum_of_index
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (hidx :
      ∀ head : ParentOpenHeadFields n a C rest,
        ∀ tail : ParentOpenTailFields n a C rest,
          ∀ idx : HeadChildIndex n a rest,
            (∏ childSite : NormalSiteClean n C,
              chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
                n a C rest hC root head tail idx childSite)) =
              let data : HeadChildOpenData n a C rest :=
                (parentOpenHeadFieldsEquivHeadChildOpenData
                  n a C rest hC P) head
              weightClean C (closeOpenNormalAssignmentClean
                (data idx).1 (data idx).2) *
                chi (headChildIndexBranchCoeff n a C rest hC P root idx
                  (headChildOpenDataRootMessage
                    n a C rest hC P root (data idx).1))) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      ∑ head : ParentOpenHeadFields n a C rest,
        parentHeadFieldsDataWeightAtHead
          n a C rest hC P root head *
          parentOpenTailPhaseSignedSumAtHead n a C rest root head := by
  exact openNormalSignedSumClean_eq_sum_parentHeadDataWeight_mul_tailPhaseSignedSum
    n a C rest hC P root
    (by
      intro head tail
      exact parentHeadPhaseSiteProductAtHeadTail_eq_parentHeadFieldsDataWeightAtHead_of_index
        n a C rest hC P root head tail (hidx head tail))

theorem openNormalSignedSumClean_eq_sum_parentHeadDataWeight_mul_tailFactor
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tailFactor : ParentOpenHeadFields n a C rest → ℤ)
    (hhead :
      ∀ head : ParentOpenHeadFields n a C rest,
        ∀ tail : ParentOpenTailFields n a C rest,
          parentHeadPhaseSiteProductAtHeadTail
              n a C rest root head tail =
            parentHeadFieldsDataWeightAtHead
              n a C rest hC P root head)
    (htail :
      ∀ head : ParentOpenHeadFields n a C rest,
        parentOpenTailPhaseSignedSumAtHead n a C rest root head =
          tailFactor head) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      ∑ head : ParentOpenHeadFields n a C rest,
        parentHeadFieldsDataWeightAtHead
          n a C rest hC P root head *
          tailFactor head := by
  rw [openNormalSignedSumClean_eq_sum_parentHeadDataWeight_mul_tailPhaseSignedSum
    n a C rest hC P root hhead]
  refine Finset.sum_congr rfl ?_
  intro head _
  rw [htail head]

end Imbalance
end TreeGraph
