import TreeGraph.Imbalance.NodeOpenPackageSkeleton

namespace TreeGraph
namespace Imbalance

noncomputable def boundaryHeadSliceLinearEquiv
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    BoundaryField n (RTree.node a (C :: rest)) ≃ₗ[F2]
      (CoordsList n rest → BranchField n C) where
  toFun h := fun e p => h (p, e)
  invFun g := fun pe => g pe.2 pe.1
  left_inv h := by
    funext pe
    rcases pe with ⟨p, e⟩
    rfl
  right_inv g := by
    funext e p
    rfl
  map_add' h k := by
    ext e p
    rfl
  map_smul' r h := by
    ext e p
    rfl

@[simp] theorem boundaryHeadSliceLinearEquiv_apply
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (h : BoundaryField n (RTree.node a (C :: rest)))
    (e : CoordsList n rest) (p : Cplus n C) :
    boundaryHeadSliceLinearEquiv n a C rest h e p = h (p, e) :=
  rfl

end Imbalance
end TreeGraph
