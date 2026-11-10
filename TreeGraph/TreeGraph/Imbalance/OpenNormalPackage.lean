import TreeGraph.Imbalance.NodeRootSplitSkeleton
import TreeGraph.Imbalance.OpenNormalLeaf

namespace TreeGraph
namespace Imbalance

theorem finrank_submodule_map_linearEquiv
    {V W : Type} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W]
    (e : V ≃ₗ[F2] W) (K : Submodule F2 V) :
    Module.finrank F2 (K.map e.toLinearMap) = Module.finrank F2 K := by
  exact (LinearEquiv.finrank_eq (LinearEquiv.submoduleMap e K)).symm

structure OpenNormalCleanPackage
    (n : Nat) [NeZero n] (T : RTree)
    (hT : RTree.PositiveWeights T) where
  rootCopenBridge : RootFieldCleanCopenBridge n T
  openBridge : OpenNormalCleanReductionBridge n T hT

namespace OpenNormalCleanPackage

noncomputable def boundaryMessageSpace
    {n : Nat} [NeZero n] {T : RTree}
    {hT : RTree.PositiveWeights T}
    (P : OpenNormalCleanPackage n T hT) :
    Submodule F2 (BoundaryField n T) :=
  P.openBridge.rootMessageSpace.map
    (P.rootCopenBridge.linearEquiv).toLinearMap

theorem boundaryMessageSpace_finrank
    {n : Nat} [NeZero n] {T : RTree}
    {hT : RTree.PositiveWeights T}
    (P : OpenNormalCleanPackage n T hT) :
    Module.finrank F2 P.boundaryMessageSpace = Ydim n T hT := by
  rw [boundaryMessageSpace, finrank_submodule_map_linearEquiv]
  exact P.openBridge.rootMessageSpace_finrank

noncomputable def leaf
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    OpenNormalCleanPackage n (RTree.node a []) hT where
  rootCopenBridge := RootFieldCleanCopenBridge.leaf n a
  openBridge := OpenNormalCleanReductionBridge.leaf n a hT

noncomputable def singleEdge
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    OpenNormalCleanPackage n (RTree.node a [RTree.node b []]) hT where
  rootCopenBridge := RootFieldCleanCopenBridge.singleEdge n a b
  openBridge := OpenNormalCleanReductionBridge.singleEdge_from_open n a b hT

noncomputable def toClosedBridge
    {n : Nat} [NeZero n] {T : RTree}
    {hT : RTree.PositiveWeights T}
    (P : OpenNormalCleanPackage n T hT) :
    NormalCleanReductionBridge n T hT :=
  P.openBridge.toNormalCleanReductionBridge

end OpenNormalCleanPackage

end Imbalance
end TreeGraph
