import TreeGraph.Imbalance.NodeHeadSlice

namespace TreeGraph
namespace Imbalance

theorem rootWeight_pos_of_positiveWeights
    {T : RTree} (hT : RTree.PositiveWeights T) :
    0 < T.rootWeight := by
  cases T with
  | node a cs =>
      have h : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      exact h.1

noncomputable def headChildR
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    BranchField n C →ₗ[F2]
      (Rep n → Module.Dual F2 P.boundaryMessageSpace) :=
  branchProjection n C
    (rootWeight_pos_of_positiveWeights hC)
    P.boundaryMessageSpace

theorem headChildR_surjective
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Function.Surjective (headChildR n C hC P) := by
  exact branchProjection_surjective n C
    (rootWeight_pos_of_positiveWeights hC)
    P.boundaryMessageSpace

noncomputable def linearEquivComapSubmodule
    {V W : Type} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W]
    (e : V ≃ₗ[F2] W) (K : Submodule F2 W) :
    Submodule F2 V :=
  K.comap e.toLinearMap

noncomputable def submoduleComapLinearEquiv
    {V W : Type} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W]
    (e : V ≃ₗ[F2] W) (K : Submodule F2 W) :
    K.comap e.toLinearMap ≃ₗ[F2] K where
  toFun v := ⟨e v.1, v.2⟩
  invFun w := ⟨e.symm w.1, by simp [w.2]⟩
  left_inv v := by
    ext
    simp
  right_inv w := by
    ext
    simp
  map_add' v w := by
    ext
    simp
  map_smul' r v := by
    ext
    simp

theorem finrank_submodule_comap_linearEquiv
    {V W : Type} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W]
    (e : V ≃ₗ[F2] W) (K : Submodule F2 W) :
    Module.finrank F2 (K.comap e.toLinearMap) = Module.finrank F2 K := by
  exact LinearEquiv.finrank_eq (submoduleComapLinearEquiv e K)

noncomputable def headAllowedBoundarySpace
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Submodule F2 (BoundaryField n (RTree.node a (C :: rest))) :=
  (rtildeVisibleKernel n
      (CoordsList n rest)
      (BranchField n C)
      P.boundaryMessageSpace
      (headChildR n C hC P)).comap
    (boundaryHeadSliceLinearEquiv n a C rest).toLinearMap

theorem finrank_headAllowedBoundarySpace
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Module.finrank F2
      (headAllowedBoundarySpace n a C rest hC P) =
      Fintype.card (CoordsList n rest) *
        Module.finrank F2 (BranchField n C) -
      Fintype.card (CoordsList n rest) * (n - 1) *
        Module.finrank F2 P.boundaryMessageSpace := by
  rw [headAllowedBoundarySpace, finrank_submodule_comap_linearEquiv]
  exact finrank_rtildeVisibleKernel n
    (CoordsList n rest)
    (BranchField n C)
    P.boundaryMessageSpace
    (headChildR n C hC P)
    (headChildR_surjective n C hC P)

theorem finrank_headAllowedBoundarySpace_Ydim_shape
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Module.finrank F2
      (headAllowedBoundarySpace n a C rest hC P) =
      Fintype.card (CoordsList n rest) *
        (n ^ RTree.totalWeight C - (n - 1) * Ydim n C hC) := by
  rw [finrank_headAllowedBoundarySpace]
  rw [finrank_branchField, OpenNormalCleanPackage.boundaryMessageSpace_finrank]
  rw [Nat.mul_assoc, ← Nat.mul_sub_left_distrib]

end Imbalance
end TreeGraph
