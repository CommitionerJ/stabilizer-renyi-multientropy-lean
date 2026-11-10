import TreeGraph.Imbalance.OpenNormalPackage

namespace TreeGraph
namespace Imbalance

namespace OpenNormalCleanPackage

noncomputable instance boundaryMessageSpaceFintype
    {n : Nat} [NeZero n] {T : RTree}
    {hT : RTree.PositiveWeights T}
    (P : OpenNormalCleanPackage n T hT) :
    Fintype P.boundaryMessageSpace :=
  Fintype.ofFinite P.boundaryMessageSpace

noncomputable instance rootMessageSpaceFintype
    {n : Nat} [NeZero n] {T : RTree}
    {hT : RTree.PositiveWeights T}
    (P : OpenNormalCleanPackage n T hT) :
    Fintype P.openBridge.rootMessageSpace :=
  Fintype.ofFinite P.openBridge.rootMessageSpace

noncomputable def rootMessageEquivBoundaryMessage
    {n : Nat} [NeZero n] {T : RTree}
    {hT : RTree.PositiveWeights T}
    (P : OpenNormalCleanPackage n T hT) :
    P.openBridge.rootMessageSpace ≃ P.boundaryMessageSpace := by
  change P.openBridge.rootMessageSpace ≃
    P.openBridge.rootMessageSpace.map
      (P.rootCopenBridge.linearEquiv).toLinearMap
  exact
    (LinearEquiv.submoduleMap
      P.rootCopenBridge.linearEquiv
      P.openBridge.rootMessageSpace).toEquiv

theorem rootMessageEquivBoundaryMessage_apply
    {n : Nat} [NeZero n] {T : RTree}
    {hT : RTree.PositiveWeights T}
    (P : OpenNormalCleanPackage n T hT)
    (r : P.openBridge.rootMessageSpace) :
    ((P.rootMessageEquivBoundaryMessage r : P.boundaryMessageSpace) :
        BoundaryField n T) =
      P.rootCopenBridge.linearEquiv
        (r : RootFieldAssignmentClean n T) := by
  rfl

theorem rootMessageEquivBoundaryMessage_symm_coe_mem
    {n : Nat} [NeZero n] {T : RTree}
    {hT : RTree.PositiveWeights T}
    (P : OpenNormalCleanPackage n T hT)
    (m : P.boundaryMessageSpace) :
    ((P.rootMessageEquivBoundaryMessage.symm m :
        P.openBridge.rootMessageSpace) :
      RootFieldAssignmentClean n T) ∈ P.openBridge.rootMessageSpace :=
  (P.rootMessageEquivBoundaryMessage.symm m).2

end OpenNormalCleanPackage

end Imbalance
end TreeGraph
