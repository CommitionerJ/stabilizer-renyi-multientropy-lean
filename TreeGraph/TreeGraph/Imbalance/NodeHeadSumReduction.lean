import TreeGraph.Imbalance.NodeHeadPhaseProduct

namespace TreeGraph
namespace Imbalance

noncomputable instance headChildIndexDecidableEq
    (n a : Nat) [NeZero n] (rest : List RTree) :
    DecidableEq (HeadChildIndex n a rest) := by
  classical
  infer_instance

noncomputable instance headChildOpenDataFintype
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    Fintype (HeadChildOpenData n a C rest) :=
  Pi.instFintype

noncomputable def parentActualHeadPhaseSignedSumAtTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest) : ℤ :=
  ∑ head : ParentOpenHeadFields n a C rest,
    parentHeadPhaseSiteProductAtHeadTail n a C rest root head tail

theorem parentActualHeadPhaseSignedSumAtTail_eq_sum_dataInternalPhase
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      ∑ data : HeadChildOpenData n a C rest,
        ∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C,
            chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
              n a C rest hC root
              ((parentOpenHeadFieldsEquivHeadChildOpenData
                n a C rest hC P).symm data)
              tail idx childSite) := by
  classical
  unfold parentActualHeadPhaseSignedSumAtTail
  rw [show
      (∑ head : ParentOpenHeadFields n a C rest,
        parentHeadPhaseSiteProductAtHeadTail n a C rest root head tail) =
        ∑ head : ParentOpenHeadFields n a C rest,
          ∏ idx : HeadChildIndex n a rest,
            ∏ childSite : NormalSiteClean n C,
              chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
                n a C rest hC root head tail idx childSite) by
    refine Finset.sum_congr rfl ?_
    intro head _
    rw [parentHeadPhaseSiteProductAtHeadTail_eq_prod_dataInternalPhase]]
  let e := parentOpenHeadFieldsEquivHeadChildOpenData n a C rest hC P
  let F : ParentOpenHeadFields n a C rest → ℤ := fun head =>
    ∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
          n a C rest hC root head tail idx childSite)
  change (∑ head : ParentOpenHeadFields n a C rest, F head) =
    ∑ data : HeadChildOpenData n a C rest, F (e.symm data)
  exact (Equiv.sum_comp e.symm F).symm

theorem parentHeadFieldsDataSignedSum_eq_sum_headChildDataWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    parentHeadFieldsDataSignedSum n a C rest hC P root =
      ∑ data : HeadChildOpenData n a C rest,
        headChildOpenDataInternalWeight n a C rest data *
          chi (headChildOpenDataBoundaryExponent
            n a C rest hC P root data) := by
  classical
  unfold parentHeadFieldsDataSignedSum
  let e := parentOpenHeadFieldsEquivHeadChildOpenData n a C rest hC P
  let F : HeadChildOpenData n a C rest → ℤ := fun data =>
    headChildOpenDataInternalWeight n a C rest data *
      chi (headChildOpenDataBoundaryExponent
        n a C rest hC P root data)
  change (∑ head : ParentOpenHeadFields n a C rest, F (e head)) =
    ∑ data : HeadChildOpenData n a C rest, F data
  exact Equiv.sum_comp e F

theorem parentActualHeadPhaseSignedSumAtTail_eq_parentHeadFieldsDataSignedSum_of_data_sum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (hdata :
      (∑ data : HeadChildOpenData n a C rest,
        ∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C,
            chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
              n a C rest hC root
              ((parentOpenHeadFieldsEquivHeadChildOpenData
                n a C rest hC P).symm data)
              tail idx childSite)) =
      ∑ data : HeadChildOpenData n a C rest,
        headChildOpenDataInternalWeight n a C rest data *
          chi (headChildOpenDataBoundaryExponent
            n a C rest hC P root data)) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      parentHeadFieldsDataSignedSum n a C rest hC P root := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_sum_dataInternalPhase
    n a C rest hC P root tail]
  rw [parentHeadFieldsDataSignedSum_eq_sum_headChildDataWeight]
  exact hdata

theorem parentActualHeadPhaseSignedSumAtTail_eq_parentHeadFieldsDataSignedSum_of_index
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (hidx :
      ∀ head : ParentOpenHeadFields n a C rest,
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
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      parentHeadFieldsDataSignedSum n a C rest hC P root := by
  classical
  unfold parentActualHeadPhaseSignedSumAtTail
  rw [parentHeadFieldsDataSignedSum_eq_sum_dataWeight]
  refine Finset.sum_congr rfl ?_
  intro head _
  exact parentHeadPhaseSiteProductAtHeadTail_eq_parentHeadFieldsDataWeightAtHead_of_index
    n a C rest hC P root head tail (hidx head)

end Imbalance
end TreeGraph
