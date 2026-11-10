import TreeGraph.Imbalance.NodeHeadRootShift
import TreeGraph.Imbalance.NodeHeadFullSignedSum

namespace TreeGraph
namespace Imbalance

theorem headChildOpenDataInternalWeight_rootSucc
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataInternalWeight n a C rest
        (headChildOpenDataRootSuccEquiv n a C rest data) =
      headChildOpenDataInternalWeight n a C rest data := by
  classical
  let e := headChildIndexRootSuccEquiv n a rest
  let w : HeadChildIndex n a rest → ℤ := fun idx =>
    weightClean C
      (closeOpenNormalAssignmentClean
        (data idx).1 (data idx).2)
  unfold headChildOpenDataInternalWeight
  change (∏ idx : HeadChildIndex n a rest, w (e idx)) =
    ∏ idx : HeadChildIndex n a rest, w idx
  exact Equiv.prod_comp e w

theorem headChildOpenDataFullBoundaryExponent_rootSucc
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataFullBoundaryExponent n a C rest hC P root
        (headChildOpenDataRootSuccEquiv n a C rest data) =
      ∑ idx : HeadChildIndex n a rest,
        headChildIndexFullBoundaryCoeff n a C rest hC P root idx
          (P.rootCopenBridge.linearEquiv
            (data ((headChildIndexRootSuccEquiv n a rest) idx)).1) := by
  rfl

theorem headChildOpenDataFullProductWeight_rootSucc
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataFullProductWeight n a C rest hC P root
        (headChildOpenDataRootSuccEquiv n a C rest data) =
      ∏ idx : HeadChildIndex n a rest,
        headIndexPhysicalPairWeight n a C rest hC P root idx
          (data ((headChildIndexRootSuccEquiv n a rest) idx)) := by
  rfl

theorem headChildOpenDataFullWeight_rootSucc
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataFullWeight n a C rest hC P root
        (headChildOpenDataRootSuccEquiv n a C rest data) =
      headChildOpenDataInternalWeight n a C rest data *
        chi (∑ idx : HeadChildIndex n a rest,
          headChildIndexFullBoundaryCoeff n a C rest hC P root idx
            (P.rootCopenBridge.linearEquiv
              (data ((headChildIndexRootSuccEquiv n a rest) idx)).1)) := by
  unfold headChildOpenDataFullWeight
  rw [headChildOpenDataInternalWeight_rootSucc]
  rw [headChildOpenDataFullBoundaryExponent_rootSucc]

end Imbalance
end TreeGraph
