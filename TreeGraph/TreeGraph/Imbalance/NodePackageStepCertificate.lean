import TreeGraph.Imbalance.NodePackageBoundary

namespace TreeGraph
namespace Imbalance

open Classical in
structure NodeOpenPackageStepCertificate
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) where
  open_signed_sum_eq :
    ∀ root : RootFieldAssignmentClean n (RTree.node a cs),
      openNormalSignedSumClean n (RTree.node a cs) root =
        if root ∈ packageAllowedRootFieldSpace n a cs hT I then
          (2 : ℤ) ^ (Xdim n (RTree.node a cs) -
            Ydim n (RTree.node a cs) hT)
        else 0

namespace NodeOpenPackageStepCertificate

noncomputable def toOpenPackageStepTheorem
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : NodeOpenPackageStepInputs n a cs hT}
    (W : NodeOpenPackageStepCertificate n a cs hT I) :
    NodeOpenPackageStepTheorem n a cs hT I where
  parentPackage := {
    rootCopenBridge := I.parentRootCopenBridge
    openBridge := {
      rootMessageSpace := packageAllowedRootFieldSpace n a cs hT I
      rootMessageSpace_finrank :=
        finrank_packageAllowedRootFieldSpace n a cs hT I
      open_signed_sum_eq := W.open_signed_sum_eq } }

noncomputable def toOpenBridge
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : NodeOpenPackageStepInputs n a cs hT}
    (W : NodeOpenPackageStepCertificate n a cs hT I) :
    OpenNormalCleanReductionBridge n (RTree.node a cs) hT :=
  (W.toOpenPackageStepTheorem).toOpenBridge

noncomputable def toClosedBridge
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : NodeOpenPackageStepInputs n a cs hT}
    (W : NodeOpenPackageStepCertificate n a cs hT I) :
    NormalCleanReductionBridge n (RTree.node a cs) hT :=
  (W.toOpenPackageStepTheorem).toClosedBridge

end NodeOpenPackageStepCertificate

end Imbalance
end TreeGraph
