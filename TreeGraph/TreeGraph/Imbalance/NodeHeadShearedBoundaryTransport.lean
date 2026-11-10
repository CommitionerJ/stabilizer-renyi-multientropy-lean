import TreeGraph.Imbalance.NodeHeadActualToShearedSum
import TreeGraph.Imbalance.NodeHeadShearedBoundaryCyclic

namespace TreeGraph
namespace Imbalance

theorem headChildRShearedFull_sum_shift_totalShear_eq_RFull_sum_node
    (n b : Nat) [NeZero n]
    (ds : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (h : BranchField n (RTree.node b ds))
    (μ : Rep n → BoundaryField n (RTree.node b ds))
    (δ : Rep n) :
    (∑ α : Rep n,
      headChildRShearedFull n (RTree.node b ds) hC h α
        (fun y => μ (α + δ -
          copenTotalDiag n (RTree.node b ds) y) y)) =
      ∑ s : Rep n,
        headChildRFull n (RTree.node b ds) hC h s
          (μ (s + δ)) := by
  classical
  change
    (∑ α : Rep n,
      ∑ y : Copen n (RTree.node b ds),
        μ (α + δ - copenTotalDiag n (RTree.node b ds) y) y *
          (∑ x : Block n b,
            if diag n b x +
                copenTotalDiag n (RTree.node b ds) y = α then
              h (x, y)
            else
              0)) =
      ∑ s : Rep n,
        ∑ y : Copen n (RTree.node b ds),
          μ (s + δ) y *
            (∑ x : Block n b,
              if diag n b x = s then h (x, y) else 0)
  calc
    (∑ α : Rep n,
      ∑ y : Copen n (RTree.node b ds),
        μ (α + δ - copenTotalDiag n (RTree.node b ds) y) y *
          (∑ x : Block n b,
            if diag n b x +
                copenTotalDiag n (RTree.node b ds) y = α then
              h (x, y)
            else
              0)) =
        ∑ y : Copen n (RTree.node b ds),
          ∑ α : Rep n,
            μ (α + δ - copenTotalDiag n (RTree.node b ds) y) y *
              (∑ x : Block n b,
                if diag n b x +
                    copenTotalDiag n (RTree.node b ds) y = α then
                  h (x, y)
                else
                  0) := by
          rw [Finset.sum_comm]
    _ =
        ∑ y : Copen n (RTree.node b ds),
          ∑ s : Rep n,
            μ (s + δ) y *
              (∑ x : Block n b,
                if diag n b x = s then h (x, y) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro y _
          let τ := copenTotalDiag n (RTree.node b ds) y
          have hshift :
              (∑ α : Rep n,
                μ (α + δ - τ) y *
                  (∑ x : Block n b,
                    if diag n b x + τ = α then h (x, y) else 0)) =
                ∑ s : Rep n,
                  μ (s + δ) y *
                    (∑ x : Block n b,
                      if diag n b x = s then h (x, y) else 0) := by
            simpa [τ, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
              (Equiv.sum_comp (Equiv.addRight τ)
                (fun α : Rep n =>
                  μ (α + δ - τ) y *
                    (∑ x : Block n b,
                      if diag n b x + τ = α then h (x, y) else 0))).symm
          exact hshift
    _ =
        ∑ s : Rep n,
          ∑ y : Copen n (RTree.node b ds),
            μ (s + δ) y *
              (∑ x : Block n b,
                if diag n b x = s then h (x, y) else 0) := by
          rw [Finset.sum_comm]

theorem shearedBoundaryExponent_rootSuccShear_eq_fullBoundary
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (data : HeadChildOpenData n a (RTree.node b ds) rest) :
    headChildOpenDataShearedFullBoundaryExponent
        n a (RTree.node b ds) rest hC P root
        (headChildOpenDataRootSuccEquiv n a (RTree.node b ds) rest
          (headTotalShearDataWithBridge n a (RTree.node b ds) rest
            P.rootCopenBridge data)) =
      headChildOpenDataFullBoundaryExponent
        n a (RTree.node b ds) rest hC P root
        (headChildOpenDataRootSuccEquiv n a (RTree.node b ds) rest data) := by
  classical
  rw [headChildOpenDataShearedFullBoundaryExponent_rootSucc_eq_cyclicPairing]
  rw [headChildOpenDataFullBoundaryExponent_rootSucc_eq_cyclicPairing]
  refine Finset.sum_congr rfl ?_
  intro q _
  refine Finset.sum_congr rfl ?_
  intro tail _
  let h : BranchField n (RTree.node b ds) :=
    headParentRootBranchFieldFromRoot n a (RTree.node b ds) rest root tail
  let μ : Rep n → BoundaryField n (RTree.node b ds) := fun s =>
    P.rootCopenBridge.linearEquiv (data (q, tail, s)).1
  have h0 :=
    headChildRShearedFull_sum_shift_totalShear_eq_RFull_sum_node
      n b ds hC h μ (0 : Rep n)
  have h1 :=
    headChildRShearedFull_sum_shift_totalShear_eq_RFull_sum_node
      n b ds hC h μ (1 : Rep n)
  calc
    (∑ s : Rep n,
        (headChildRShearedFull n (RTree.node b ds) hC h s
            (P.rootCopenBridge.linearEquiv
              ((headTotalShearDataWithBridge n a (RTree.node b ds) rest
                P.rootCopenBridge data) (q, tail, s)).1) +
          headChildRShearedFull n (RTree.node b ds) hC h s
            (P.rootCopenBridge.linearEquiv
              ((headTotalShearDataWithBridge n a (RTree.node b ds) rest
                P.rootCopenBridge data)
                  (q, tail, s + (1 : Rep n))).1))) =
        (∑ s : Rep n,
          headChildRShearedFull n (RTree.node b ds) hC h s
            (fun y => μ (s + (0 : Rep n) -
              copenTotalDiag n (RTree.node b ds) y) y)) +
        (∑ s : Rep n,
          headChildRShearedFull n (RTree.node b ds) hC h s
            (fun y => μ (s + (1 : Rep n) -
              copenTotalDiag n (RTree.node b ds) y) y)) := by
          rw [Finset.sum_add_distrib]
          exact congrArg₂ (fun x y : F2 => x + y)
            (by
              refine Finset.sum_congr rfl ?_
              intro s _
              apply congrArg
                (headChildRShearedFull n (RTree.node b ds) hC h s)
              funext y
              simp [μ, headTotalShearDataWithBridge_boundary_apply,
                headChildIndexParentRoot, headChildIndexTail,
                headChildIndexRootDiag])
            (by
              refine Finset.sum_congr rfl ?_
              intro s _
              apply congrArg
                (headChildRShearedFull n (RTree.node b ds) hC h s)
              funext y
              rw [headTotalShearDataWithBridge_boundary_apply]
              simp [μ, headChildIndexParentRoot, headChildIndexTail,
                headChildIndexRootDiag])
    _ =
        (∑ s : Rep n,
          headChildRFull n (RTree.node b ds) hC h s
            (μ (s + (0 : Rep n)))) +
        (∑ s : Rep n,
          headChildRFull n (RTree.node b ds) hC h s
            (μ (s + (1 : Rep n)))) := by
          exact congrArg₂ (fun x y : F2 => x + y) h0 h1
    _ =
        ∑ s : Rep n,
          (headChildRFull n (RTree.node b ds) hC h s
              (P.rootCopenBridge.linearEquiv (data (q, tail, s)).1) +
            headChildRFull n (RTree.node b ds) hC h s
              (P.rootCopenBridge.linearEquiv
                (data (q, tail, s + (1 : Rep n))).1)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro s _
          simp [μ]

theorem parentActualHeadDiagBoundaryExponentAtTail_eq_shearedBoundary_rootSucc_totalShear_node
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
      headChildOpenDataShearedFullBoundaryExponent
        n a (RTree.node b ds) rest hC P root
        (headChildOpenDataRootSuccEquiv n a (RTree.node b ds) rest
          (headTotalShearDataWithBridge n a (RTree.node b ds) rest
            P.rootCopenBridge data)) := by
  rw [parentActualHeadDiagBoundaryExponentAtTail_eq_fullBoundary_rootSucc_node]
  rw [shearedBoundaryExponent_rootSuccShear_eq_fullBoundary]

noncomputable def headRootSuccTotalShearDataWithBridgeEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C) :
    HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest :=
  (headTotalShearDataWithBridgeEquiv n a C rest B).trans
    (headChildOpenDataRootSuccEquiv n a C rest)

@[simp] theorem headRootSuccTotalShearDataWithBridgeEquiv_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest) :
    headRootSuccTotalShearDataWithBridgeEquiv n a C rest B data =
      headChildOpenDataRootSuccEquiv n a C rest
        (headTotalShearDataWithBridge n a C rest B data) := by
  rfl

theorem actualHeadDiagDataWeight_eq_shearedFullWeight_of_internal
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
          n a (RTree.node b ds) rest
          (headTotalShearDataWithBridge n a (RTree.node b ds) rest
            P.rootCopenBridge data)) :
    parentActualHeadDiagDataWeightAtTail
        n a (RTree.node b ds) rest hC P root tail data =
      headChildOpenDataShearedFullWeight
        n a (RTree.node b ds) rest hC P root
        (headRootSuccTotalShearDataWithBridgeEquiv
          n a (RTree.node b ds) rest P.rootCopenBridge data) := by
  rw [parentActualHeadDiagDataWeightAtTail_eq_internal_mul_boundary]
  rw [hinternal]
  unfold headChildOpenDataShearedFullWeight
  rw [headRootSuccTotalShearDataWithBridgeEquiv_apply]
  rw [headChildOpenDataInternalWeight_rootSucc]
  rw [parentActualHeadDiagBoundaryExponentAtTail_eq_shearedBoundary_rootSucc_totalShear_node]

theorem actualHeadDiagDataWeight_eq_shearedFullProductWeight_of_internal
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
          n a (RTree.node b ds) rest
          (headTotalShearDataWithBridge n a (RTree.node b ds) rest
            P.rootCopenBridge data)) :
    parentActualHeadDiagDataWeightAtTail
        n a (RTree.node b ds) rest hC P root tail data =
      headChildOpenDataShearedFullProductWeight
        n a (RTree.node b ds) rest hC P root
        (headRootSuccTotalShearDataWithBridgeEquiv
          n a (RTree.node b ds) rest P.rootCopenBridge data) := by
  rw [← headChildOpenDataShearedFullWeight_eq_prod_index]
  exact
    actualHeadDiagDataWeight_eq_shearedFullWeight_of_internal
      n a b ds rest hC P root tail data hinternal

theorem actualHeadPhaseSum_eq_descScalar_mul_shearedMessageSum_of_internal
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
            n a (RTree.node b ds) rest
            (headTotalShearDataWithBridge n a (RTree.node b ds) rest
              P.rootCopenBridge data)) :
    parentActualHeadPhaseSignedSumAtTail
        n a (RTree.node b ds) rest root tail =
      (2 : ℤ) ^
          branchDescendantScalarExponent
            n a 0 (RTree.node b ds) rest hC *
        headShearedBranchMessageSignedSum
          n a (RTree.node b ds) rest hC P root := by
  refine
    parentActualHeadPhaseSignedSumAtTail_eq_descScalar_mul_shearedMessageSum_of_diagEquiv
      n a (RTree.node b ds) rest hC P root tail
      (headRootSuccTotalShearDataWithBridgeEquiv
        n a (RTree.node b ds) rest P.rootCopenBridge) ?_
  intro data
  exact
    actualHeadDiagDataWeight_eq_shearedFullProductWeight_of_internal
      n a b ds rest hC P root tail data (hinternal data)

end Imbalance
end TreeGraph
