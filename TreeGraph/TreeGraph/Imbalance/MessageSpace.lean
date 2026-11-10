import TreeGraph.Imbalance.RootedPolynomial

namespace TreeGraph
namespace Imbalance

abbrev BoundaryField (n : Nat) (T : RTree) :=
  Field (Copen n T)

abbrev BranchField (n : Nat) (T : RTree) :=
  Field (Cplus n T)

noncomputable def leafMessageSpace (n a : Nat) :
    Submodule F2 (BoundaryField n (RTree.node a [])) :=
  ⊤

theorem finrank_boundaryField_leaf (n a : Nat) [NeZero n] :
    Module.finrank F2 (BoundaryField n (RTree.node a [])) = 1 := by
  classical
  calc
    Module.finrank F2 (BoundaryField n (RTree.node a [])) =
        ∑ _ : Copen n (RTree.node a []), Module.finrank F2 F2 := by
      simpa [BoundaryField] using
        (Module.finrank_pi_fintype
          (R := F2) (M := fun _ : Copen n (RTree.node a []) => F2))
    _ = 1 := by
      simp

theorem finrank_leafMessageSpace (n a : Nat) [NeZero n] :
    Module.finrank F2 (leafMessageSpace n a) = 1 := by
  rw [leafMessageSpace, finrank_top, finrank_boundaryField_leaf]

noncomputable def branchProjection (n : Nat) [NeZero n]
    (T : RTree) (hroot : 0 < T.rootWeight)
    (Msub : Submodule F2 (BoundaryField n T)) :
    BranchField n T →ₗ[F2] (Rep n → Module.Dual F2 Msub) := by
  cases T with
  | node a cs =>
      exact PiSubmodule n hroot (Copen n (RTree.node a cs)) Msub

@[simp] theorem branchProjection_node_apply (n : Nat) [NeZero n]
    {a : Nat} (ha : 0 < a) (cs : List RTree)
    (Msub : Submodule F2 (BoundaryField n (RTree.node a cs)))
    (h : BranchField n (RTree.node a cs)) (s : Rep n) :
    branchProjection n (RTree.node a cs) ha Msub h s =
      PiSubmodule n ha (Copen n (RTree.node a cs)) Msub h s := rfl

theorem branchProjection_surjective (n : Nat) [NeZero n]
    (T : RTree) (hroot : 0 < T.rootWeight)
    (Msub : Submodule F2 (BoundaryField n T)) :
    Function.Surjective (branchProjection n T hroot Msub) := by
  cases T with
  | node a cs =>
      exact PiSubmodule_surjective n hroot (Copen n (RTree.node a cs)) Msub

noncomputable def Kchild (n : Nat) [NeZero n]
    (T : RTree) (hroot : 0 < T.rootWeight)
    (Msub : Submodule F2 (BoundaryField n T)) :
    Submodule F2 (BranchField n T) :=
  LinearMap.ker
    ((cycDiff n (Module.Dual F2 Msub)).comp
      (branchProjection n T hroot Msub))

theorem mem_Kchild_iff (n : Nat) [NeZero n]
    (T : RTree) (hroot : 0 < T.rootWeight)
    (Msub : Submodule F2 (BoundaryField n T))
    (h : BranchField n T) :
    h ∈ Kchild n T hroot Msub ↔
      cycDiff n (Module.Dual F2 Msub)
        (branchProjection n T hroot Msub h) = 0 := by
  rfl

theorem finrank_branchField (n : Nat) [NeZero n] (T : RTree) :
    Module.finrank F2 (BranchField n T) = n ^ RTree.totalWeight T := by
  classical
  calc
    Module.finrank F2 (BranchField n T) =
        ∑ _ : Cplus n T, Module.finrank F2 F2 := by
      change Module.finrank F2 (Cplus n T → F2) =
        ∑ _ : Cplus n T, Module.finrank F2 F2
      exact Module.finrank_pi_fintype
        (R := F2) (M := fun _ : Cplus n T => F2)
    _ = Fintype.card (Cplus n T) := by
      simp
    _ = n ^ RTree.totalWeight T := card_Cplus n T

private theorem range_comp_eq_range_of_surjective'
    {P Q S : Type}
    [AddCommMonoid P] [Module F2 P]
    [AddCommMonoid Q] [Module F2 Q]
    [AddCommMonoid S] [Module F2 S]
    (L : P →ₗ[F2] Q) (R : Q →ₗ[F2] S)
    (hL : Function.Surjective L) :
    LinearMap.range (R.comp L) = LinearMap.range R := by
  ext s
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨L p, hp⟩
  · rintro ⟨q, hq⟩
    rcases hL q with ⟨p, hp⟩
    exact ⟨p, by simp [hp, hq]⟩

theorem finrank_Kchild (n : Nat) [NeZero n]
    (T : RTree) (hroot : 0 < T.rootWeight)
    (Msub : Submodule F2 (BoundaryField n T))
    [FiniteDimensional F2 Msub] :
    Module.finrank F2 (Kchild n T hroot Msub) =
      branchAllowedDim n (RTree.totalWeight T)
        (Module.finrank F2 Msub) := by
  classical
  let L : BranchField n T →ₗ[F2] (Rep n → Module.Dual F2 Msub) :=
    (cycDiff n (Module.Dual F2 Msub)).comp
      (branchProjection n T hroot Msub)
  have hrange_eq :
      LinearMap.range L =
        LinearMap.range (cycDiff n (Module.Dual F2 Msub)) := by
    exact
      range_comp_eq_range_of_surjective'
        (branchProjection n T hroot Msub)
        (cycDiff n (Module.Dual F2 Msub))
        (branchProjection_surjective n T hroot Msub)
  have hrange :
      Module.finrank F2 (LinearMap.range L) =
        (n - 1) * Module.finrank F2 Msub := by
    rw [hrange_eq]
    rw [finrank_range_cycDiff]
    rw [Subspace.dual_finrank_eq]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hsum :
      (n - 1) * Module.finrank F2 Msub +
        Module.finrank F2 (Kchild n T hroot Msub) =
        n ^ RTree.totalWeight T := by
    simpa [L, Kchild, hrange, finrank_branchField n T] using hrank
  unfold branchAllowedDim
  omega

theorem branchAllowedDim_subtrahend_le (n : Nat) [NeZero n]
    (T : RTree) (hroot : 0 < T.rootWeight)
    (Msub : Submodule F2 (BoundaryField n T))
    [FiniteDimensional F2 Msub] :
    (n - 1) * Module.finrank F2 Msub ≤ n ^ RTree.totalWeight T := by
  have hle := oneSliceCyclicRank_le_of_surjective n
    (BranchField n T) Msub
    (branchProjection n T hroot Msub)
    (branchProjection_surjective n T hroot Msub)
  simpa [finrank_branchField n T] using hle

theorem finrank_Kchild_cast_eq (n : Nat) [NeZero n]
    (T : RTree) (hroot : 0 < T.rootWeight)
    (Msub : Submodule F2 (BoundaryField n T))
    [FiniteDimensional F2 Msub] :
    ((Module.finrank F2 (Kchild n T hroot Msub) : Nat) : ℤ) =
      (nZ n) ^ RTree.totalWeight T -
        (tZ n) * (Module.finrank F2 Msub : ℤ) := by
  rw [finrank_Kchild]
  exact branchAllowedDim_cast_of_le
    (branchAllowedDim_subtrahend_le n T hroot Msub)

-- RecursiveMessageSpace connects these child kernels to the rooted exponent;
-- BranchTransfer and AssignmentRecursion assemble the normal-form recursion.

end Imbalance
end TreeGraph
