import TreeGraph.Imbalance.RawBridge

namespace TreeGraph
namespace Imbalance

structure SignedReductionBridge
    (n : Nat) [NeZero n] (T : RTree) (hT : RTree.PositiveWeights T)
    (Raw : Type) [Fintype Raw] where
  rawPhase : Raw → F2
  raw_signed_sum_eq_abstract :
    signedCharacterSum Raw rawPhase = abstractTreeSignedSum n T hT

namespace SignedReductionBridge

noncomputable def DeltaRaw
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : SignedReductionBridge n T hT Raw) : ℤ :=
  signedCharacterSum Raw B.rawPhase

theorem Delta_eq_abstractTreeSignedSum
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : SignedReductionBridge n T hT Raw) :
    B.DeltaRaw = abstractTreeSignedSum n T hT := by
  exact B.raw_signed_sum_eq_abstract

theorem rooted_tree_imbalance_formula
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : SignedReductionBridge n T hT Raw) :
    B.DeltaRaw = (2 : ℤ) ^ Xdim n T := by
  rw [B.Delta_eq_abstractTreeSignedSum]
  exact rooted_tree_signed_sum_imbalance_formula n T hT

theorem rooted_tree_imbalance_formula_allTerms
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : SignedReductionBridge n T hT Raw) :
    ∃ X : Nat,
      B.DeltaRaw = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact B.rooted_tree_imbalance_formula
  · exact Xdim_cast_eq_allTerms n T hT

theorem rooted_tree_imbalance_formula_Xpoly
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    {Raw : Type} [Fintype Raw]
    (B : SignedReductionBridge n T hT Raw) :
    ∃ X : Nat,
      B.DeltaRaw = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact B.rooted_tree_imbalance_formula
  · exact Xdim_cast_eq_Xpoly n T hT

noncomputable def abstractIdentity
    (n : Nat) [NeZero n] (T : RTree) (hT : RTree.PositiveWeights T) :
    SignedReductionBridge n T hT
      (abstractTreeNormalAssignments n T hT) where
  rawPhase := abstractTreeNormalPhase n T hT
  raw_signed_sum_eq_abstract := rfl

theorem abstractIdentity_DeltaRaw_eq
    (n : Nat) [NeZero n] (T : RTree) (hT : RTree.PositiveWeights T) :
    (abstractIdentity n T hT).DeltaRaw =
      abstractTreeSignedSum n T hT := by
  exact (abstractIdentity n T hT).Delta_eq_abstractTreeSignedSum

end SignedReductionBridge

end Imbalance
end TreeGraph
