import TreeGraph.Imbalance.NodeHeadActualInternalCanonical
import TreeGraph.Imbalance.NodeHeadShearedBoundaryTransport

namespace TreeGraph
namespace Imbalance

theorem actualHeadDiagDataWeight_eq_shearedFullProductWeight_of_canonical
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (hP : P.IsCanonical)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest)
    (data : HeadChildOpenData n a (RTree.node b ds) rest) :
    parentActualHeadDiagDataWeightAtTail
        n a (RTree.node b ds) rest hC P root tail data =
      headChildOpenDataShearedFullProductWeight
        n a (RTree.node b ds) rest hC P root
        (headRootSuccTotalShearDataWithBridgeEquiv
          n a (RTree.node b ds) rest P.rootCopenBridge data) := by
  exact
    actualHeadDiagDataWeight_eq_shearedFullProductWeight_of_internal
      n a b ds rest hC P root tail data
      (parentActualHeadDiagInternalProductAtTail_eq_shearedInternalWeight_of_canonical
        n a (RTree.node b ds) rest hC P hP root tail data)

theorem actualHeadPhaseSum_eq_descScalar_mul_shearedMessageSum_of_canonical
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (hP : P.IsCanonical)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest) :
    parentActualHeadPhaseSignedSumAtTail
        n a (RTree.node b ds) rest root tail =
      (2 : ℤ) ^
          branchDescendantScalarExponent
            n a 0 (RTree.node b ds) rest hC *
        headShearedBranchMessageSignedSum
          n a (RTree.node b ds) rest hC P root := by
  exact
    actualHeadPhaseSum_eq_descScalar_mul_shearedMessageSum_of_internal
      n a b ds rest hC P root tail
      (fun data =>
        parentActualHeadDiagInternalProductAtTail_eq_shearedInternalWeight_of_canonical
          n a (RTree.node b ds) rest hC P hP root tail data)

end Imbalance
end TreeGraph
