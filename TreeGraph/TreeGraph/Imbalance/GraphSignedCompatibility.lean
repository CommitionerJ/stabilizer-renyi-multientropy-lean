import TreeGraph.Imbalance.SignedReductionBridge

namespace TreeGraph
namespace Imbalance

structure GraphSignedCompatibilityBridge
    (n : Nat) [NeZero n] (Graph Raw : Type) [Fintype Raw] where
  graph : Graph
  rootedTree : RTree
  positiveWeights : RTree.PositiveWeights rootedTree
  connectedExponent : Nat
  signedReductionBridge :
    SignedReductionBridge n rootedTree positiveWeights Raw
  connectedExponent_eq_Xdim : connectedExponent = Xdim n rootedTree

namespace GraphSignedCompatibilityBridge

noncomputable def DeltaGraph
    {n : Nat} [NeZero n] {Graph Raw : Type} [Fintype Raw]
    (B : GraphSignedCompatibilityBridge n Graph Raw) : ℤ :=
  B.signedReductionBridge.DeltaRaw

theorem tree_imbalance_formula_connected_signed
    {n : Nat} [NeZero n] {Graph Raw : Type} [Fintype Raw]
    (B : GraphSignedCompatibilityBridge n Graph Raw) :
    B.DeltaGraph = (2 : ℤ) ^ B.connectedExponent := by
  unfold DeltaGraph
  rw [B.signedReductionBridge.rooted_tree_imbalance_formula]
  rw [B.connectedExponent_eq_Xdim]

theorem connectedExponent_cast_eq_allTerms
    {n : Nat} [NeZero n] {Graph Raw : Type} [Fintype Raw]
    (B : GraphSignedCompatibilityBridge n Graph Raw) :
    ((B.connectedExponent : Nat) : ℤ) =
      termSum n (allTerms B.rootedTree) := by
  rw [B.connectedExponent_eq_Xdim]
  exact Xdim_cast_eq_allTerms n B.rootedTree B.positiveWeights

theorem connectedExponent_cast_eq_Xpoly
    {n : Nat} [NeZero n] {Graph Raw : Type} [Fintype Raw]
    (B : GraphSignedCompatibilityBridge n Graph Raw) :
    ((B.connectedExponent : Nat) : ℤ) = Xpoly n B.rootedTree := by
  rw [B.connectedExponent_eq_Xdim]
  exact Xdim_cast_eq_Xpoly n B.rootedTree B.positiveWeights

theorem tree_imbalance_formula_connected_terms_signed
    {n : Nat} [NeZero n] {Graph Raw : Type} [Fintype Raw]
    (B : GraphSignedCompatibilityBridge n Graph Raw) :
    ∃ X : Nat,
      B.DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms B.rootedTree) := by
  refine ⟨B.connectedExponent, ?_, ?_⟩
  · exact B.tree_imbalance_formula_connected_signed
  · exact B.connectedExponent_cast_eq_allTerms

theorem tree_imbalance_formula_connected_Xpoly_signed
    {n : Nat} [NeZero n] {Graph Raw : Type} [Fintype Raw]
    (B : GraphSignedCompatibilityBridge n Graph Raw) :
    ∃ X : Nat,
      B.DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n B.rootedTree := by
  refine ⟨B.connectedExponent, ?_, ?_⟩
  · exact B.tree_imbalance_formula_connected_signed
  · exact B.connectedExponent_cast_eq_Xpoly

noncomputable def abstractRootedSigned
    (n : Nat) [NeZero n] (T : RTree) (hT : RTree.PositiveWeights T) :
    GraphSignedCompatibilityBridge n PUnit
      (abstractTreeNormalAssignments n T hT) where
  graph := PUnit.unit
  rootedTree := T
  positiveWeights := hT
  connectedExponent := Xdim n T
  signedReductionBridge := SignedReductionBridge.abstractIdentity n T hT
  connectedExponent_eq_Xdim := rfl

theorem abstractRootedSigned_formula
    (n : Nat) [NeZero n] (T : RTree) (hT : RTree.PositiveWeights T) :
    (abstractRootedSigned n T hT).DeltaGraph =
      (2 : ℤ) ^ Xdim n T := by
  exact (abstractRootedSigned n T hT).tree_imbalance_formula_connected_signed

end GraphSignedCompatibilityBridge

theorem tree_imbalance_formula_connected_signed
    {n : Nat} [NeZero n] {Graph Raw : Type} [Fintype Raw]
    (B : GraphSignedCompatibilityBridge n Graph Raw) :
    B.DeltaGraph = (2 : ℤ) ^ B.connectedExponent := by
  exact B.tree_imbalance_formula_connected_signed

theorem tree_imbalance_formula_connected_terms_signed
    {n : Nat} [NeZero n] {Graph Raw : Type} [Fintype Raw]
    (B : GraphSignedCompatibilityBridge n Graph Raw) :
    ∃ X : Nat,
      B.DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms B.rootedTree) := by
  exact B.tree_imbalance_formula_connected_terms_signed

theorem tree_imbalance_formula_connected_Xpoly_signed
    {n : Nat} [NeZero n] {Graph Raw : Type} [Fintype Raw]
    (B : GraphSignedCompatibilityBridge n Graph Raw) :
    ∃ X : Nat,
      B.DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n B.rootedTree := by
  exact B.tree_imbalance_formula_connected_Xpoly_signed

end Imbalance
end TreeGraph
