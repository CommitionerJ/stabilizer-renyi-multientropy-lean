import TreeGraph.Imbalance.NodeRootCopenBridgeCanonical
import TreeGraph.Imbalance.OpenNormalPackage

namespace TreeGraph
namespace Imbalance

namespace RootFieldCleanCopenBridge

def IsCanonical
    {n : Nat} [NeZero n] {T : RTree}
    (B : RootFieldCleanCopenBridge n T) : Prop :=
  B.domEquiv = rootFieldDomainCleanEquivCopen n T

@[simp] theorem ofTree_isCanonical
    (n : Nat) [NeZero n] (T : RTree) :
    (RootFieldCleanCopenBridge.ofTree n T).IsCanonical := by
  rfl

@[simp] theorem node_isCanonical
    (n a : Nat) [NeZero n] (cs : List RTree) :
    (RootFieldCleanCopenBridge.node n a cs).IsCanonical := by
  rfl

end RootFieldCleanCopenBridge

theorem rootFieldCleanCopenBridge_linearEquiv_apply_of_isCanonical_copen
    (n : Nat) [NeZero n] (T : RTree)
    (B : RootFieldCleanCopenBridge n T)
    (hB : B.IsCanonical)
    (r : RootFieldAssignmentClean n T)
    (y : Copen n T) :
    B.linearEquiv r y =
      r ((rootFieldDomainCleanEquivCopen n T).symm y) := by
  unfold RootFieldCleanCopenBridge.IsCanonical at hB
  unfold RootFieldCleanCopenBridge.linearEquiv
    rootFieldCleanLinearEquivBoundaryOfEquiv
  simp [precomposeLinearEquiv, hB]

theorem rootFieldCleanCopenBridge_linearEquiv_apply_of_isCanonical
    (n : Nat) [NeZero n] (T : RTree)
    (B : RootFieldCleanCopenBridge n T)
    (hB : B.IsCanonical)
    (r : RootFieldAssignmentClean n T)
    (rd : RootFieldDomainClean n T) :
    B.linearEquiv r ((rootFieldDomainCleanEquivCopen n T) rd) = r rd := by
  rw [rootFieldCleanCopenBridge_linearEquiv_apply_of_isCanonical_copen
    n T B hB r]
  simp

theorem rootFieldCleanCopenBridge_symm_apply_of_isCanonical
    (n : Nat) [NeZero n] (T : RTree)
    (B : RootFieldCleanCopenBridge n T)
    (hB : B.IsCanonical)
    (μ : BoundaryField n T)
    (rd : RootFieldDomainClean n T) :
    ((B.linearEquiv).symm μ) rd =
      μ ((rootFieldDomainCleanEquivCopen n T) rd) := by
  let r := (B.linearEquiv).symm μ
  have hlin :=
    rootFieldCleanCopenBridge_linearEquiv_apply_of_isCanonical
      n T B hB r rd
  have hμ :
      B.linearEquiv r ((rootFieldDomainCleanEquivCopen n T) rd) =
        μ ((rootFieldDomainCleanEquivCopen n T) rd) := by
    exact congrFun ((B.linearEquiv).apply_symm_apply μ)
      ((rootFieldDomainCleanEquivCopen n T) rd)
  exact hlin.symm.trans hμ

namespace OpenNormalCleanPackage

def IsCanonical
    {n : Nat} [NeZero n] {T : RTree}
    {hT : RTree.PositiveWeights T}
    (P : OpenNormalCleanPackage n T hT) : Prop :=
  P.rootCopenBridge.IsCanonical

noncomputable def leafCanonical
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    OpenNormalCleanPackage n (RTree.node a []) hT where
  rootCopenBridge := RootFieldCleanCopenBridge.ofTree n (RTree.node a [])
  openBridge := OpenNormalCleanReductionBridge.leaf n a hT

@[simp] theorem leafCanonical_isCanonical
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    (leafCanonical n a hT).IsCanonical := by
  rfl

noncomputable def singleEdgeCanonical
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    OpenNormalCleanPackage n (RTree.node a [RTree.node b []]) hT where
  rootCopenBridge :=
    RootFieldCleanCopenBridge.ofTree n
      (RTree.node a [RTree.node b []])
  openBridge := OpenNormalCleanReductionBridge.singleEdge_from_open n a b hT

@[simp] theorem singleEdgeCanonical_isCanonical
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    (singleEdgeCanonical n a b hT).IsCanonical := by
  rfl

end OpenNormalCleanPackage

end Imbalance
end TreeGraph
