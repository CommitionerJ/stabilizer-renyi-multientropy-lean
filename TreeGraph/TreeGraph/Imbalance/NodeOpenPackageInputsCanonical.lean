import TreeGraph.Imbalance.NodeRootCopenBridgeCanonical
import TreeGraph.Imbalance.NodeOpenPackageSkeleton

namespace TreeGraph
namespace Imbalance

namespace NodeOpenPackageStepInputs

noncomputable def withCanonicalParentBridge
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (childPackage :
      ∀ C, (hCmem : C ∈ cs) →
        OpenNormalCleanPackage n C
          (child_positive_of_node hT C hCmem)) :
    NodeOpenPackageStepInputs n a cs hT where
  childPackage := childPackage
  parentRootCopenBridge := RootFieldCleanCopenBridge.node n a cs

noncomputable def ofChildPackagesCanonical
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (childPackage :
      ∀ C, (hCmem : C ∈ cs) →
        OpenNormalCleanPackage n C
          (child_positive_of_node hT C hCmem)) :
    NodeOpenPackageStepInputs n a cs hT :=
  withCanonicalParentBridge n a cs hT childPackage

end NodeOpenPackageStepInputs

end Imbalance
end TreeGraph
