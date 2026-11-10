import TreeGraph.Imbalance.NodeHeadSumReduction
import TreeGraph.Imbalance.NodeTailPhasePreservation
import TreeGraph.Imbalance.NodeTailCplusProduct

namespace TreeGraph
namespace Imbalance

theorem openNormalSignedSumClean_node_cons_eq_headSum_mul_tailSum_of_bridges
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (headSum : ℤ)
    (tailFactor : ParentOpenTailFields n a C rest → ℤ)
    (hhead :
      ∀ tail : ParentOpenTailFields n a C rest,
        parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
          headSum)
    (htail :
      ∀ head : ParentOpenHeadFields n a C rest,
        ∀ tail : ParentOpenTailFields n a C rest,
          parentTailPhaseSiteProductAtHeadTail n a C rest root head tail =
            tailFactor tail) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      headSum * ∑ tail : ParentOpenTailFields n a C rest,
        tailFactor tail := by
  classical
  rw [openNormalSignedSumClean_eq_sum_head_tail_phaseSiteProducts
    n a C rest root]
  rw [Finset.sum_comm]
  calc
    (∑ tail : ParentOpenTailFields n a C rest,
      ∑ head : ParentOpenHeadFields n a C rest,
        parentHeadPhaseSiteProductAtHeadTail n a C rest root head tail *
          parentTailPhaseSiteProductAtHeadTail n a C rest root head tail) =
        ∑ tail : ParentOpenTailFields n a C rest,
          ∑ head : ParentOpenHeadFields n a C rest,
            parentHeadPhaseSiteProductAtHeadTail n a C rest root head tail *
              tailFactor tail := by
          refine Finset.sum_congr rfl ?_
          intro tail _
          refine Finset.sum_congr rfl ?_
          intro head _
          rw [htail head tail]
    _ =
        ∑ tail : ParentOpenTailFields n a C rest,
          parentActualHeadPhaseSignedSumAtTail n a C rest root tail *
            tailFactor tail := by
          refine Finset.sum_congr rfl ?_
          intro tail _
          rw [← Finset.sum_mul]
          rfl
    _ =
        ∑ tail : ParentOpenTailFields n a C rest,
          headSum * tailFactor tail := by
          refine Finset.sum_congr rfl ?_
          intro tail _
          rw [hhead tail]
    _ =
        headSum *
          ∑ tail : ParentOpenTailFields n a C rest, tailFactor tail := by
          rw [Finset.mul_sum]

theorem openNormalSignedSumClean_node_cons_eq_parentHeadDataSum_mul_tailSum_of_bridges
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tailFactor : ParentOpenTailFields n a C rest → ℤ)
    (hhead :
      ∀ tail : ParentOpenTailFields n a C rest,
        parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
          parentHeadFieldsDataSignedSum n a C rest hC P root)
    (htail :
      ∀ head : ParentOpenHeadFields n a C rest,
        ∀ tail : ParentOpenTailFields n a C rest,
          parentTailPhaseSiteProductAtHeadTail n a C rest root head tail =
            tailFactor tail) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      parentHeadFieldsDataSignedSum n a C rest hC P root *
        ∑ tail : ParentOpenTailFields n a C rest, tailFactor tail := by
  exact
    openNormalSignedSumClean_node_cons_eq_headSum_mul_tailSum_of_bridges
      n a C rest root
      (parentHeadFieldsDataSignedSum n a C rest hC P root)
      tailFactor hhead htail

theorem openNormalSignedSumClean_node_cons_eq_parentHeadDataSum_mul_prod_tailOpenAtCplus
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (hhead :
      ∀ tail : ParentOpenTailFields n a C rest,
        parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
          parentHeadFieldsDataSignedSum n a C rest hC P root) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      parentHeadFieldsDataSignedSum n a C rest hC P root *
        ∏ p : Cplus n C,
          openNormalSignedSumClean n (RTree.node a rest)
            (tailRootFieldFromHeadCplus n a C rest root p) := by
  rw [openNormalSignedSumClean_node_cons_eq_parentHeadDataSum_mul_tailSum_of_bridges
    n a C rest hC P root
    (tailOpenProductAtCplus n a C rest root) hhead
    (by
      intro head tail
      exact parentTailPhaseSiteProductAtHeadTail_eq_tailOpenProductAtCplus
        n a C rest root head tail)]
  rw [sum_tailOpenProductAtCplus_eq_prod_tailOpenAtCplus]

theorem canonical_openNormalSignedSumClean_node_cons_eq_if_packageAllowed_of_head_sum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ C :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (Wtail :
      NodeOpenPackageStepCertificate n a rest
        (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a C rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage)))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (hhead :
      ∀ tail : ParentOpenTailFields n a C rest,
        parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
          parentHeadFieldsDataSignedSum n a C rest
            (child_positive_of_node hT C (by simp))
            (childPackage C (by simp)) root) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      (by
        classical
        exact
          if root ∈
              packageAllowedRootFieldSpace n a (C :: rest) hT
                (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                  n a (C :: rest) hT childPackage) then
            (2 : ℤ) ^ (Xdim n (RTree.node a (C :: rest)) -
              Ydim n (RTree.node a (C :: rest)) hT)
          else
            0) := by
  rw [openNormalSignedSumClean_node_cons_eq_parentHeadDataSum_mul_prod_tailOpenAtCplus
    n a C rest
    (child_positive_of_node hT C (by simp))
    (childPackage C (by simp)) root hhead]
  exact canonical_parentHeadDataSignedSum_mul_prod_tailOpenAtCplus_eq_if_packageAllowed
    n a C rest hT childPackage Wtail root

theorem openNormalSignedSumClean_node_cons_eq_parentHeadDataSum_mul_prod_tailOpenAtCplus_of_index
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
      parentHeadFieldsDataSignedSum n a C rest hC P root *
        ∏ p : Cplus n C,
          openNormalSignedSumClean n (RTree.node a rest)
            (tailRootFieldFromHeadCplus n a C rest root p) := by
  classical
  rw [openNormalSignedSumClean_eq_sum_parentHeadDataWeight_mul_tailPhaseSignedSum_of_index
    n a C rest hC P root hidx]
  calc
    (∑ head : ParentOpenHeadFields n a C rest,
      parentHeadFieldsDataWeightAtHead n a C rest hC P root head *
        parentOpenTailPhaseSignedSumAtHead n a C rest root head) =
        ∑ head : ParentOpenHeadFields n a C rest,
          parentHeadFieldsDataWeightAtHead n a C rest hC P root head *
            (∏ p : Cplus n C,
              openNormalSignedSumClean n (RTree.node a rest)
                (tailRootFieldFromHeadCplus n a C rest root p)) := by
          refine Finset.sum_congr rfl ?_
          intro head _
          rw [parentOpenTailPhaseSignedSumAtHead_eq_prod_tailOpenAtCplus]
    _ =
        (∑ head : ParentOpenHeadFields n a C rest,
          parentHeadFieldsDataWeightAtHead n a C rest hC P root head) *
          ∏ p : Cplus n C,
            openNormalSignedSumClean n (RTree.node a rest)
              (tailRootFieldFromHeadCplus n a C rest root p) := by
          rw [Finset.sum_mul]
    _ =
        parentHeadFieldsDataSignedSum n a C rest hC P root *
          ∏ p : Cplus n C,
            openNormalSignedSumClean n (RTree.node a rest)
              (tailRootFieldFromHeadCplus n a C rest root p) := by
          rw [← parentHeadFieldsDataSignedSum_eq_sum_dataWeight]

theorem canonical_openNormalSignedSumClean_node_cons_eq_if_packageAllowed_of_index
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ C :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (Wtail :
      NodeOpenPackageStepCertificate n a rest
        (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a C rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage)))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (hidx :
      ∀ head : ParentOpenHeadFields n a C rest,
        ∀ tail : ParentOpenTailFields n a C rest,
          ∀ idx : HeadChildIndex n a rest,
            (∏ childSite : NormalSiteClean n C,
              chi (parentHeadDataInternalPhaseAtHeadIndexChildSite
                n a C rest
                (child_positive_of_node hT C (by simp))
                root head tail idx childSite)) =
              let data : HeadChildOpenData n a C rest :=
                (parentOpenHeadFieldsEquivHeadChildOpenData
                  n a C rest
                  (child_positive_of_node hT C (by simp))
                  (childPackage C (by simp))) head
              weightClean C (closeOpenNormalAssignmentClean
                (data idx).1 (data idx).2) *
                chi (headChildIndexBranchCoeff n a C rest
                  (child_positive_of_node hT C (by simp))
                  (childPackage C (by simp)) root idx
                  (headChildOpenDataRootMessage
                    n a C rest
                    (child_positive_of_node hT C (by simp))
                    (childPackage C (by simp)) root (data idx).1))) :
    openNormalSignedSumClean n (RTree.node a (C :: rest)) root =
      (by
        classical
        exact
          if root ∈
              packageAllowedRootFieldSpace n a (C :: rest) hT
                (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                  n a (C :: rest) hT childPackage) then
            (2 : ℤ) ^ (Xdim n (RTree.node a (C :: rest)) -
              Ydim n (RTree.node a (C :: rest)) hT)
          else
            0) := by
  rw [openNormalSignedSumClean_node_cons_eq_parentHeadDataSum_mul_prod_tailOpenAtCplus_of_index
    n a C rest
    (child_positive_of_node hT C (by simp))
    (childPackage C (by simp)) root hidx]
  exact canonical_parentHeadDataSignedSum_mul_prod_tailOpenAtCplus_eq_if_packageAllowed
    n a C rest hT childPackage Wtail root

end Imbalance
end TreeGraph
