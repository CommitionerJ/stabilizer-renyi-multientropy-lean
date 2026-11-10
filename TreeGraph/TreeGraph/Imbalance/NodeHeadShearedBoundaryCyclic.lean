import TreeGraph.Imbalance.CyclicPairing
import TreeGraph.Imbalance.NodeHeadRootShift
import TreeGraph.Imbalance.NodeHeadShearedFullSignedSum

namespace TreeGraph
namespace Imbalance

theorem headChildShearedFullBoundaryCoeff_sum_rootSucc_eq_cyclicPairing
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) :
    (∑ idx : HeadChildIndex n a rest,
        headChildIndexShearedFullBoundaryCoeff n a C rest hC P root idx
          (P.rootCopenBridge.linearEquiv
            (data ((headChildIndexRootSuccEquiv n a rest) idx)).1)) =
      ∑ q : Block n (a - 1),
        ∑ tail : CoordsList n rest,
          ∑ s : Rep n,
            (headChildRShearedFull n C hC
                (headParentRootBranchFieldFromRoot n a C rest root tail) s
                (P.rootCopenBridge.linearEquiv (data (q, tail, s)).1) +
              headChildRShearedFull n C hC
                (headParentRootBranchFieldFromRoot n a C rest root tail) s
                (P.rootCopenBridge.linearEquiv
                  (data (q, tail, s + (1 : Rep n))).1)) := by
  classical
  change
    (∑ idx : Block n (a - 1) × CoordsList n rest × Rep n,
        headChildIndexShearedFullBoundaryCoeff n a C rest hC P root idx
          (P.rootCopenBridge.linearEquiv
            (data ((headChildIndexRootSuccEquiv n a rest) idx)).1)) =
      ∑ q : Block n (a - 1),
        ∑ tail : CoordsList n rest,
          ∑ s : Rep n,
            (headChildRShearedFull n C hC
                (headParentRootBranchFieldFromRoot n a C rest root tail) s
                (P.rootCopenBridge.linearEquiv (data (q, tail, s)).1) +
              headChildRShearedFull n C hC
                (headParentRootBranchFieldFromRoot n a C rest root tail) s
                (P.rootCopenBridge.linearEquiv
                  (data (q, tail, s + (1 : Rep n))).1))
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro tail _
  let h : Rep n → Module.Dual F2 (BoundaryField n C) := fun s =>
    headChildRShearedFull n C hC
      (headParentRootBranchFieldFromRoot n a C rest root tail) s
  let μ : Rep n → BoundaryField n C := fun s =>
    P.rootCopenBridge.linearEquiv (data (q, tail, s)).1
  have hcyc :=
    cyclic_dual_pairing_sum_eq_forwardCoeff_shifted n
      (BoundaryField n C) h μ
  calc
    (∑ s : Rep n,
        headChildIndexShearedFullBoundaryCoeff n a C rest hC P root
          (q, tail, s)
          (P.rootCopenBridge.linearEquiv
            (data ((headChildIndexRootSuccEquiv n a rest)
              (q, tail, s))).1)) =
        ∑ s : Rep n, (h s + h (s + (1 : Rep n))) (μ (s + (1 : Rep n))) := by
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [headChildIndexShearedFullBoundaryCoeff_apply]
          rfl
    _ =
        ∑ s : Rep n, (h s (μ s) + h s (μ (s + (1 : Rep n)))) := by
          exact hcyc.symm

theorem headChildOpenDataShearedFullBoundaryExponent_rootSucc_eq_cyclicPairing
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataShearedFullBoundaryExponent n a C rest hC P root
        (headChildOpenDataRootSuccEquiv n a C rest data) =
      ∑ q : Block n (a - 1),
        ∑ tail : CoordsList n rest,
          ∑ s : Rep n,
            (headChildRShearedFull n C hC
                (headParentRootBranchFieldFromRoot n a C rest root tail) s
                (P.rootCopenBridge.linearEquiv (data (q, tail, s)).1) +
              headChildRShearedFull n C hC
                (headParentRootBranchFieldFromRoot n a C rest root tail) s
                (P.rootCopenBridge.linearEquiv
                  (data (q, tail, s + (1 : Rep n))).1)) := by
  unfold headChildOpenDataShearedFullBoundaryExponent
  simp only [headChildOpenDataRootSuccEquiv_apply_fst]
  exact headChildShearedFullBoundaryCoeff_sum_rootSucc_eq_cyclicPairing
    n a C rest hC P root data

end Imbalance
end TreeGraph
