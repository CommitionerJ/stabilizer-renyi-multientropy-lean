import TreeGraph.Imbalance.AssignmentRecursion

namespace TreeGraph
namespace Imbalance

structure RawNormalBridge
    (n : Nat) [NeZero n] (T : RTree) (hT : RTree.PositiveWeights T)
    (Raw : Type) [Fintype Raw] where
  rawAssign_equiv_normalField :
    Raw ≃ abstractTreeNormalAssignments n T hT
  rawPhase : Raw → F2
  normalPhase : abstractTreeNormalAssignments n T hT → F2
  phase_preserved_under_normalForm :
    ∀ A, rawPhase A = normalPhase (rawAssign_equiv_normalField A)
  normalPhase_eq_abstract :
    ∀ F, normalPhase F = abstractTreeNormalPhase n T hT F

namespace RawNormalBridge

noncomputable def toPhaseBridge
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : RawNormalBridge n T hT Raw) :
    PhaseBridge Raw (abstractTreeNormalAssignments n T hT) where
  toEquiv := B.rawAssign_equiv_normalField
  rawPhase := B.rawPhase
  normalPhase := B.normalPhase
  phase_preserved := B.phase_preserved_under_normalForm

noncomputable def DeltaRaw
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : RawNormalBridge n T hT Raw) : ℤ :=
  (B.toPhaseBridge).rawSum

noncomputable def NormalSum
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : RawNormalBridge n T hT Raw) : ℤ :=
  (B.toPhaseBridge).normalSum

theorem Delta_eq_normal_sum
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : RawNormalBridge n T hT Raw) :
    B.DeltaRaw = B.NormalSum := by
  exact (B.toPhaseBridge).sum_eq

theorem normal_sum_eq_abstractTreeSignedSum
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : RawNormalBridge n T hT Raw) :
    B.NormalSum = abstractTreeSignedSum n T hT := by
  unfold NormalSum PhaseBridge.normalSum abstractTreeSignedSum toPhaseBridge
  exact signedCharacterSum_congr B.normalPhase
    (abstractTreeNormalPhase n T hT) B.normalPhase_eq_abstract

theorem Delta_eq_abstractTreeSignedSum
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : RawNormalBridge n T hT Raw) :
    B.DeltaRaw = abstractTreeSignedSum n T hT := by
  rw [B.Delta_eq_normal_sum]
  exact B.normal_sum_eq_abstractTreeSignedSum

theorem rooted_tree_imbalance_formula
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : RawNormalBridge n T hT Raw) :
    B.DeltaRaw = (2 : ℤ) ^ Xdim n T := by
  rw [B.Delta_eq_abstractTreeSignedSum]
  exact TreeGraph.Imbalance.rooted_tree_signed_sum_imbalance_formula n T hT

theorem rooted_tree_imbalance_formula_allTerms
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : RawNormalBridge n T hT Raw) :
    ∃ X : Nat,
      B.DeltaRaw = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact B.rooted_tree_imbalance_formula
  · exact Xdim_cast_eq_allTerms n T hT

theorem rooted_tree_imbalance_formula_Xpoly
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : RawNormalBridge n T hT Raw) :
    ∃ X : Nat,
      B.DeltaRaw = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact B.rooted_tree_imbalance_formula
  · exact Xdim_cast_eq_Xpoly n T hT

noncomputable def abstractIdentity
    (n : Nat) [NeZero n] (T : RTree) (hT : RTree.PositiveWeights T) :
    RawNormalBridge n T hT (abstractTreeNormalAssignments n T hT) where
  rawAssign_equiv_normalField := Equiv.refl _
  rawPhase := abstractTreeNormalPhase n T hT
  normalPhase := abstractTreeNormalPhase n T hT
  phase_preserved_under_normalForm := by
    intro A
    rfl
  normalPhase_eq_abstract := by
    intro F
    rfl

theorem abstractIdentity_DeltaRaw_eq
    (n : Nat) [NeZero n] (T : RTree) (hT : RTree.PositiveWeights T) :
    (abstractIdentity n T hT).DeltaRaw =
      abstractTreeSignedSum n T hT := by
  exact (abstractIdentity n T hT).Delta_eq_abstractTreeSignedSum

end RawNormalBridge

end Imbalance
end TreeGraph
