import TreeGraph.Imbalance.NodePackageShearedStepCertificate
import TreeGraph.Imbalance.NodePackageShearedRank

namespace TreeGraph
namespace Imbalance

namespace NodeShearedOpenPackageStepCertificate

noncomputable def toOpenPackageStepTheorem
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : NodeOpenPackageStepInputs n a cs hT}
    (W : NodeShearedOpenPackageStepCertificate n a cs hT I) :
    NodeOpenPackageStepTheorem n a cs hT I where
  parentPackage := {
    rootCopenBridge := I.parentRootCopenBridge
    openBridge := {
      rootMessageSpace := packageShearedAllowedRootFieldSpace n a cs hT I
      rootMessageSpace_finrank :=
        finrank_packageShearedAllowedRootFieldSpace n a cs hT I
      open_signed_sum_eq := W.open_signed_sum_eq } }

noncomputable def toOpenBridge
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : NodeOpenPackageStepInputs n a cs hT}
    (W : NodeShearedOpenPackageStepCertificate n a cs hT I) :
    OpenNormalCleanReductionBridge n (RTree.node a cs) hT :=
  (W.toOpenPackageStepTheorem).toOpenBridge

noncomputable def toClosedBridge
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : NodeOpenPackageStepInputs n a cs hT}
    (W : NodeShearedOpenPackageStepCertificate n a cs hT I) :
    NormalCleanReductionBridge n (RTree.node a cs) hT :=
  (W.toOpenPackageStepTheorem).toClosedBridge

end NodeShearedOpenPackageStepCertificate

end Imbalance
end TreeGraph
