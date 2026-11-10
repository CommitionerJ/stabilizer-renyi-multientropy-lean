import TreeGraph.Imbalance.OpenNormalEdgeMessage
import TreeGraph.Imbalance.OpenNormalClosed

namespace TreeGraph
namespace Imbalance

namespace CoordsList

noncomputable def headTailEquiv
    (n : Nat) (C : RTree) (rest : List RTree) :
    CoordsList n (C :: rest) ≃ Cplus n C × CoordsList n rest :=
  Equiv.refl _

end CoordsList

structure RootFieldCleanCopenBridge
    (n : Nat) [NeZero n] (T : RTree) where
  domEquiv : RootFieldDomainClean n T ≃ Copen n T

namespace RootFieldCleanCopenBridge

noncomputable def linearEquiv
    {n : Nat} [NeZero n] {T : RTree}
    (B : RootFieldCleanCopenBridge n T) :
    RootFieldAssignmentClean n T ≃ₗ[F2] BoundaryField n T :=
  rootFieldCleanLinearEquivBoundaryOfEquiv B.domEquiv

noncomputable def leaf
    (n a : Nat) [NeZero n] :
    RootFieldCleanCopenBridge n (RTree.node a []) where
  domEquiv := rootFieldDomainCleanEquivCopen_leaf n a

noncomputable def singleEdge
    (n a b : Nat) [NeZero n] :
    RootFieldCleanCopenBridge n (RTree.node a [RTree.node b []]) where
  domEquiv := rootFieldDomainCleanEquivCopen_singleEdge n a b

end RootFieldCleanCopenBridge

structure NodeOpenStepInputs
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) where
  childOpenBridge :
    ∀ C, (hCmem : C ∈ cs) →
      OpenNormalCleanReductionBridge n C
        (child_positive_of_node hT C hCmem)
  rootCopenBridge :
    RootFieldCleanCopenBridge n (RTree.node a cs)

structure NodeOpenStepTheorem
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenStepInputs n a cs hT) where
  parentBridge :
    OpenNormalCleanReductionBridge n (RTree.node a cs) hT

namespace NodeOpenStepTheorem

noncomputable def toClosedBridge
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : NodeOpenStepInputs n a cs hT}
    (S : NodeOpenStepTheorem n a cs hT I) :
    NormalCleanReductionBridge n (RTree.node a cs) hT :=
  S.parentBridge.toNormalCleanReductionBridge

end NodeOpenStepTheorem

end Imbalance
end TreeGraph
