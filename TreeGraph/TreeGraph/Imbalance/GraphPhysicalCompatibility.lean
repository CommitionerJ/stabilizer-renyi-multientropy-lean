import TreeGraph.Imbalance.GraphSignedCompatibility
import TreeGraph.Imbalance.PhysicalRaw

namespace TreeGraph
namespace Imbalance

structure GraphPhysicalRealizedRawBridge
    (n : Nat) [NeZero n] (Graph : Type) where
  graph : Graph
  rootedTree : RTree
  positiveWeights : RTree.PositiveWeights rootedTree
  connectedExponent : Nat
  normalReductionBridge :
    NormalCleanReductionBridge n rootedTree positiveWeights
  connectedExponent_eq_Xdim : connectedExponent = Xdim n rootedTree

namespace GraphPhysicalRealizedRawBridge

noncomputable def toGraphSignedCompatibilityBridge
    {n : Nat} [NeZero n] {Graph : Type}
    (B : GraphPhysicalRealizedRawBridge n Graph) :
    GraphSignedCompatibilityBridge n Graph
      (NormalFormRawAssignmentsClean n B.rootedTree) where
  graph := B.graph
  rootedTree := B.rootedTree
  positiveWeights := B.positiveWeights
  connectedExponent := B.connectedExponent
  signedReductionBridge :=
    B.normalReductionBridge.toRealizedRawSignedReductionBridge
  connectedExponent_eq_Xdim := B.connectedExponent_eq_Xdim

noncomputable def DeltaGraph
    {n : Nat} [NeZero n] {Graph : Type}
    (B : GraphPhysicalRealizedRawBridge n Graph) : ℤ :=
  B.toGraphSignedCompatibilityBridge.DeltaGraph

theorem tree_imbalance_formula_connected_realizedRaw
    {n : Nat} [NeZero n] {Graph : Type}
    (B : GraphPhysicalRealizedRawBridge n Graph) :
    B.DeltaGraph = (2 : ℤ) ^ B.connectedExponent := by
  exact B.toGraphSignedCompatibilityBridge.tree_imbalance_formula_connected_signed

theorem tree_imbalance_formula_connected_terms_realizedRaw
    {n : Nat} [NeZero n] {Graph : Type}
    (B : GraphPhysicalRealizedRawBridge n Graph) :
    ∃ X : Nat,
      B.DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms B.rootedTree) := by
  exact
    B.toGraphSignedCompatibilityBridge.tree_imbalance_formula_connected_terms_signed

theorem tree_imbalance_formula_connected_Xpoly_realizedRaw
    {n : Nat} [NeZero n] {Graph : Type}
    (B : GraphPhysicalRealizedRawBridge n Graph) :
    ∃ X : Nat,
      B.DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n B.rootedTree := by
  exact
    B.toGraphSignedCompatibilityBridge.tree_imbalance_formula_connected_Xpoly_signed

noncomputable def leafRooted
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    GraphPhysicalRealizedRawBridge n PUnit where
  graph := PUnit.unit
  rootedTree := RTree.node a []
  positiveWeights := hT
  connectedExponent := Xdim n (RTree.node a [])
  normalReductionBridge := NormalCleanReductionBridge.leaf n a hT
  connectedExponent_eq_Xdim := rfl

theorem leafRooted_formula
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    (leafRooted n a hT).DeltaGraph = (2 : ℤ) := by
  rw [tree_imbalance_formula_connected_realizedRaw]
  simp [leafRooted]

end GraphPhysicalRealizedRawBridge

end Imbalance
end TreeGraph
