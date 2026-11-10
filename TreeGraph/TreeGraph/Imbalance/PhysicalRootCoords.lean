import TreeGraph.Imbalance.PhysicalEdge
import TreeGraph.Imbalance.Transport

namespace TreeGraph
namespace Imbalance

noncomputable def rootFieldCleanLinearEquivBoundaryOfEquiv
    {n : Nat} [NeZero n] {T : RTree}
    (e : RootFieldDomainClean n T ≃ Copen n T) :
    RootFieldAssignmentClean n T ≃ₗ[F2] BoundaryField n T :=
  (precomposeLinearEquiv (RootFieldDomainClean n T) (Copen n T) F2 e).symm

noncomputable def rootFieldDomainCleanEquivCopen_leaf
    (n a : Nat) [NeZero n] :
    RootFieldDomainClean n (RTree.node a []) ≃ Copen n (RTree.node a []) where
  toFun _ := PUnit.unit
  invFun _ := rootFieldDomainCleanLeafDefault n a
  left_inv x := by
    exact Subsingleton.elim (rootFieldDomainCleanLeafDefault n a) x
  right_inv y := by
    cases y
    rfl

noncomputable def rootFieldCleanLinearEquivBoundary_leaf
    (n a : Nat) [NeZero n] :
    RootFieldAssignmentClean n (RTree.node a []) ≃ₗ[F2]
      BoundaryField n (RTree.node a []) :=
  rootFieldCleanLinearEquivBoundaryOfEquiv
    (rootFieldDomainCleanEquivCopen_leaf n a)

noncomputable def copenSingleLeafEquivBlock
    (n a b : Nat) [NeZero n] :
    Copen n (RTree.node a [RTree.node b []]) ≃ Block n b where
  toFun x := x.1.1
  invFun y := ((y, PUnit.unit), PUnit.unit)
  left_inv x := by
    rcases x with ⟨⟨y, u⟩, v⟩
    cases u
    cases v
    rfl
  right_inv y := by
    rfl

noncomputable def rootFieldDomainCleanEquivCopen_singleEdge
    (n a b : Nat) [NeZero n] :
    RootFieldDomainClean n (RTree.node a [RTree.node b []]) ≃
      Copen n (RTree.node a [RTree.node b []]) :=
  (edgeRootFieldDomainCleanEquiv n a b).trans
    (copenSingleLeafEquivBlock n a b).symm

noncomputable def rootFieldCleanLinearEquivBoundary_singleEdge
    (n a b : Nat) [NeZero n] :
    RootFieldAssignmentClean n (RTree.node a [RTree.node b []]) ≃ₗ[F2]
      BoundaryField n (RTree.node a [RTree.node b []]) :=
  rootFieldCleanLinearEquivBoundaryOfEquiv
    (rootFieldDomainCleanEquivCopen_singleEdge n a b)

end Imbalance
end TreeGraph
