import TreeGraph.Imbalance.OpenNormalPackage

namespace TreeGraph
namespace Imbalance

structure NodeOpenPackageStepInputs
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) where
  childPackage :
    ∀ C, (hCmem : C ∈ cs) →
      OpenNormalCleanPackage n C
        (child_positive_of_node hT C hCmem)
  parentRootCopenBridge :
    RootFieldCleanCopenBridge n (RTree.node a cs)

structure NodeOpenPackageStepTheorem
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) where
  parentPackage :
    OpenNormalCleanPackage n (RTree.node a cs) hT

namespace NodeOpenPackageStepTheorem

noncomputable def toOpenBridge
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : NodeOpenPackageStepInputs n a cs hT}
    (S : NodeOpenPackageStepTheorem n a cs hT I) :
    OpenNormalCleanReductionBridge n (RTree.node a cs) hT :=
  S.parentPackage.openBridge

noncomputable def toClosedBridge
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : NodeOpenPackageStepInputs n a cs hT}
    (S : NodeOpenPackageStepTheorem n a cs hT I) :
    NormalCleanReductionBridge n (RTree.node a cs) hT :=
  S.parentPackage.openBridge.toNormalCleanReductionBridge

end NodeOpenPackageStepTheorem

end Imbalance
end TreeGraph
