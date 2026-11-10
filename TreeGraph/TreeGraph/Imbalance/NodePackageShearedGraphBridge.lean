import TreeGraph.Imbalance.NodePackageShearedRecursion
import TreeGraph.Imbalance.GraphPhysicalCompatibility

namespace TreeGraph
namespace Imbalance

namespace GraphPhysicalRealizedRawBridge

noncomputable def canonicalShearedSignedReductionBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    SignedReductionBridge n T hT (NormalAssignmentClean n T) :=
  (canonicalShearedClosedBridgeOfTree n T hT).toSignedReductionBridge

noncomputable def canonicalShearedRealizedRawSignedReductionBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    SignedReductionBridge n T hT (NormalFormRawAssignmentsClean n T) :=
  (canonicalShearedClosedBridgeOfTree n T hT).toRealizedRawSignedReductionBridge

theorem canonicalShearedSignedReductionBridge_DeltaRaw_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (canonicalShearedSignedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Xdim n T :=
  (canonicalShearedSignedReductionBridge n T hT).rooted_tree_imbalance_formula

theorem canonicalShearedRealizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (canonicalShearedRealizedRawSignedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Xdim n T :=
  (canonicalShearedRealizedRawSignedReductionBridge n T hT).rooted_tree_imbalance_formula

noncomputable def canonicalSheared
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    GraphPhysicalRealizedRawBridge n Graph where
  graph := graph
  rootedTree := T
  positiveWeights := hT
  connectedExponent := Xdim n T
  normalReductionBridge := canonicalShearedClosedBridgeOfTree n T hT
  connectedExponent_eq_Xdim := rfl

noncomputable def canonicalShearedRooted
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    GraphPhysicalRealizedRawBridge n PUnit :=
  canonicalSheared n PUnit.unit T hT

theorem canonicalSheared_tree_imbalance_formula_connected_realizedRaw
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    (canonicalSheared n graph T hT).DeltaGraph =
      (2 : ℤ) ^ Xdim n T := by
  simpa [canonicalSheared] using
    (canonicalSheared n graph T hT).tree_imbalance_formula_connected_realizedRaw

theorem canonicalSheared_tree_imbalance_formula_connected_terms_realizedRaw
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (canonicalSheared n graph T hT).DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) := by
  simpa [canonicalSheared] using
    (canonicalSheared n graph T hT).tree_imbalance_formula_connected_terms_realizedRaw

theorem canonicalSheared_tree_imbalance_formula_connected_Xpoly_realizedRaw
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (canonicalSheared n graph T hT).DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T := by
  simpa [canonicalSheared] using
    (canonicalSheared n graph T hT).tree_imbalance_formula_connected_Xpoly_realizedRaw

theorem canonicalShearedRooted_tree_imbalance_formula_connected_realizedRaw
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (canonicalShearedRooted n T hT).DeltaGraph =
      (2 : ℤ) ^ Xdim n T := by
  exact
    canonicalSheared_tree_imbalance_formula_connected_realizedRaw
      n PUnit.unit T hT

theorem canonicalShearedRooted_tree_imbalance_formula_connected_terms_realizedRaw
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (canonicalShearedRooted n T hT).DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) := by
  exact
    canonicalSheared_tree_imbalance_formula_connected_terms_realizedRaw
      n PUnit.unit T hT

theorem canonicalShearedRooted_tree_imbalance_formula_connected_Xpoly_realizedRaw
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (canonicalShearedRooted n T hT).DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T := by
  exact
    canonicalSheared_tree_imbalance_formula_connected_Xpoly_realizedRaw
      n PUnit.unit T hT

end GraphPhysicalRealizedRawBridge

end Imbalance
end TreeGraph
