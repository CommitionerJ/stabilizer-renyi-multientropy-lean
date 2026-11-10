import TreeGraph.Imbalance.OpenNormalClosed

namespace TreeGraph
namespace Imbalance

noncomputable def openNormalAssignmentCleanLeafEquiv
    (n a : Nat) [NeZero n] :
    OpenNormalAssignmentClean n (RTree.node a []) ≃ Unit where
  toFun _ := ()
  invFun _ :=
    { nodeField := fun v => False.elim (nonRootVertexClean_leaf_false v) }
  left_inv A := by
    cases A
    rw [OpenNormalAssignmentClean.mk.injEq]
    funext v dom
    exact False.elim (nonRootVertexClean_leaf_false v)
  right_inv y := by
    cases y
    rfl

theorem card_openNormalAssignmentClean_leaf
    (n a : Nat) [NeZero n] :
    Fintype.card (OpenNormalAssignmentClean n (RTree.node a [])) = 1 := by
  calc
    Fintype.card (OpenNormalAssignmentClean n (RTree.node a [])) =
        Fintype.card Unit :=
      Fintype.card_congr (openNormalAssignmentCleanLeafEquiv n a)
    _ = 1 := by
      simp

@[simp] theorem openNormalSignedSumClean_leaf
    (n a : Nat) [NeZero n]
    (root : RootFieldAssignmentClean n (RTree.node a [])) :
    openNormalSignedSumClean n (RTree.node a []) root = 1 := by
  unfold openNormalSignedSumClean
  calc
    (∑ A : OpenNormalAssignmentClean n (RTree.node a []),
        weightClean (RTree.node a [])
          (closeOpenNormalAssignmentClean root A)) =
        (Fintype.card (OpenNormalAssignmentClean n (RTree.node a [])) : ℤ) := by
      simp [weightClean]
    _ = 1 := by
      rw [card_openNormalAssignmentClean_leaf]
      norm_num

namespace OpenNormalCleanReductionBridge

noncomputable def leaf
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    OpenNormalCleanReductionBridge n (RTree.node a []) hT where
  rootMessageSpace := ⊤
  rootMessageSpace_finrank := by
    rw [finrank_top]
    calc
      Module.finrank F2 (RootFieldAssignmentClean n (RTree.node a [])) =
          Module.finrank F2 (BoundaryField n (RTree.node a [])) := by
        exact LinearEquiv.finrank_eq
          (rootFieldCleanLinearEquivBoundary_leaf n a)
      _ = 1 := by
        exact finrank_boundaryField_leaf n a
      _ = Ydim n (RTree.node a []) hT := by
        rw [Ydim_eq_YdimCandidate, YdimCandidate_leaf]
  open_signed_sum_eq := by
    intro root
    rw [openNormalSignedSumClean_leaf]
    simp only [Submodule.mem_top, if_true]
    have hX : Xdim n (RTree.node a []) = 1 := Xdim_leaf n a
    have hY : Ydim n (RTree.node a []) hT = 1 := by
      rw [Ydim_eq_YdimCandidate, YdimCandidate_leaf]
    rw [hX, hY]
    norm_num

end OpenNormalCleanReductionBridge

namespace NormalCleanReductionBridge

noncomputable def leaf_from_open
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    NormalCleanReductionBridge n (RTree.node a []) hT :=
  (OpenNormalCleanReductionBridge.leaf n a hT).toNormalCleanReductionBridge

end NormalCleanReductionBridge

end Imbalance
end TreeGraph
