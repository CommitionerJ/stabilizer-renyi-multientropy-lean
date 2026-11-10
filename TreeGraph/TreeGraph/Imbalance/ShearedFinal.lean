import TreeGraph.Imbalance.NodePackageShearedGraphBridge
import TreeGraph.Imbalance.LegacyCleanBridge
import TreeGraph.ModelCertificate
import TreeGraph.RecursiveCertificate

namespace TreeGraph
namespace Imbalance

namespace CanonicalSheared

open GraphPhysicalRealizedRawBridge

noncomputable def openPackage
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    OpenNormalCleanPackage n T hT :=
  canonicalShearedOpenPackageOfTree n T hT

@[simp] theorem openPackage_isCanonical
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (openPackage n T hT).IsCanonical := by
  change (canonicalShearedOpenPackageOfTree n T hT).IsCanonical
  exact canonicalShearedOpenPackageOfTree_isCanonical n T hT

open Classical in
theorem open_signed_sum_eq
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T)
    (root : RootFieldAssignmentClean n T) :
    openNormalSignedSumClean n T root =
      if root ∈ (openPackage n T hT).openBridge.rootMessageSpace then
        (2 : ℤ) ^ (Xdim n T - Ydim n T hT)
      else 0 := by
  simpa [openPackage] using
    canonicalShearedOpenPackageOfTree_open_signed_sum_eq n T hT root

noncomputable def openBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    OpenNormalCleanReductionBridge n T hT :=
  canonicalShearedOpenBridgeOfTree n T hT

noncomputable def closedBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    NormalCleanReductionBridge n T hT :=
  canonicalShearedClosedBridgeOfTree n T hT

theorem normal_signed_sum_eq_abstract
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalSignedSumClean n T = abstractTreeSignedSum n T hT :=
  canonicalSheared_normalSignedSumClean_eq_abstractTreeSignedSum n T hT

theorem normal_signed_sum_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalSignedSumClean n T = (2 : ℤ) ^ Xdim n T :=
  canonicalSheared_normalSignedSumClean_eq_two_pow_Xdim n T hT

theorem normal_signed_sum_eq_two_pow_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      normalSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) :=
  canonicalSheared_normalSignedSumClean_eq_two_pow_allTerms n T hT

theorem normal_signed_sum_eq_two_pow_Xpoly
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      normalSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T :=
  canonicalSheared_normalSignedSumClean_eq_two_pow_Xpoly n T hT

theorem Xpoly_toNat_eq_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Int.toNat (Xpoly n T) = Xdim n T := by
  rw [← Xdim_cast_eq_Xpoly n T hT]
  simp

theorem allTerms_toNat_eq_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Int.toNat (termSum n (allTerms T)) = Xdim n T := by
  rw [← Xdim_cast_eq_allTerms n T hT]
  simp

theorem normal_signed_sum_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalSignedSumClean n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [Xpoly_toNat_eq_Xdim n T hT]
  exact normal_signed_sum_eq_two_pow_Xdim n T hT

theorem normal_signed_sum_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalSignedSumClean n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [allTerms_toNat_eq_Xdim n T hT]
  exact normal_signed_sum_eq_two_pow_Xdim n T hT

theorem normalFormRaw_signed_sum_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalFormRawSignedSumClean n T = (2 : ℤ) ^ Xdim n T := by
  rw [normalFormRawSignedSumClean_eq_normalSignedSumClean_of_positiveWeights
    (n := n) (T := T) hT]
  exact normal_signed_sum_eq_two_pow_Xdim n T hT

theorem normalFormRaw_signed_sum_eq_two_pow_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      normalFormRawSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) := by
  rcases normal_signed_sum_eq_two_pow_allTerms n T hT with
    ⟨X, hsum, hX⟩
  refine ⟨X, ?_, hX⟩
  rw [normalFormRawSignedSumClean_eq_normalSignedSumClean_of_positiveWeights
    (n := n) (T := T) hT]
  exact hsum

theorem normalFormRaw_signed_sum_eq_two_pow_Xpoly
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      normalFormRawSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T := by
  rcases normal_signed_sum_eq_two_pow_Xpoly n T hT with
    ⟨X, hsum, hX⟩
  refine ⟨X, ?_, hX⟩
  rw [normalFormRawSignedSumClean_eq_normalSignedSumClean_of_positiveWeights
    (n := n) (T := T) hT]
  exact hsum

theorem normalFormRaw_signed_sum_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalFormRawSignedSumClean n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [Xpoly_toNat_eq_Xdim n T hT]
  exact normalFormRaw_signed_sum_eq_two_pow_Xdim n T hT

theorem normalFormRaw_signed_sum_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalFormRawSignedSumClean n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [allTerms_toNat_eq_Xdim n T hT]
  exact normalFormRaw_signed_sum_eq_two_pow_Xdim n T hT

def NormalCleanClosedFormulaForAllPositive : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n], normalSignedSumClean n T = (2 : ℤ) ^ Xdim n T

theorem normalCleanClosedFormulaForAllPositive :
    NormalCleanClosedFormulaForAllPositive := by
  intro T hT n _
  exact normal_signed_sum_eq_two_pow_Xdim n T hT

def NormalFormRawCleanClosedFormulaForAllPositive : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      normalFormRawSignedSumClean n T = (2 : ℤ) ^ Xdim n T

theorem normalFormRawCleanClosedFormulaForAllPositive :
    NormalFormRawCleanClosedFormulaForAllPositive := by
  intro T hT n _
  exact normalFormRaw_signed_sum_eq_two_pow_Xdim n T hT

theorem legacy_signed_sum_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawNormal.signedSum n T = (2 : ℤ) ^ Xdim n T := by
  rw [LegacyCleanBridge.legacy_signedSum_eq_normalSignedSumClean n T]
  exact normal_signed_sum_eq_two_pow_Xdim n T hT

theorem legacy_signed_sum_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawNormal.signedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [LegacyCleanBridge.legacy_signedSum_eq_normalSignedSumClean n T]
  exact normal_signed_sum_eq_two_pow_Xpoly_toNat n T hT

theorem legacy_signed_sum_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawNormal.signedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [LegacyCleanBridge.legacy_signedSum_eq_normalSignedSumClean n T]
  exact normal_signed_sum_eq_two_pow_allTerms_toNat n T hT

theorem normalFormSignedSum_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.normalFormSignedSum n T = (2 : ℤ) ^ Xdim n T := by
  rw [RawPrimitive.normalFormSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := T) hT]
  exact legacy_signed_sum_eq_two_pow_Xdim n T hT

theorem normalFormSignedSum_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [RawPrimitive.normalFormSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := T) hT]
  exact legacy_signed_sum_eq_two_pow_Xpoly_toNat n T hT

theorem normalFormSignedSum_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [RawPrimitive.normalFormSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := T) hT]
  exact legacy_signed_sum_eq_two_pow_allTerms_toNat n T hT

theorem rawBitStringSignedSum_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.rawBitStringSignedSum n T = (2 : ℤ) ^ Xdim n T := by
  rw [RawPrimitive.rawBitStringSignedSum_eq_normalFormSignedSum]
  exact normalFormSignedSum_eq_two_pow_Xdim n T hT

theorem rawBitStringSignedSum_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [RawPrimitive.rawBitStringSignedSum_eq_normalFormSignedSum]
  exact normalFormSignedSum_eq_two_pow_Xpoly_toNat n T hT

theorem rawBitStringSignedSum_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [RawPrimitive.rawBitStringSignedSum_eq_normalFormSignedSum]
  exact normalFormSignedSum_eq_two_pow_allTerms_toNat n T hT

theorem normal_signed_sum_eq_DeltaTreeModel
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalSignedSumClean n T = DeltaTreeModel n T := by
  rw [normal_signed_sum_eq_two_pow_Xpoly_toNat n T hT]
  exact (DeltaTreeModel_closed_Xpoly n T).symm

theorem normalFormRaw_signed_sum_eq_DeltaTreeModel
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalFormRawSignedSumClean n T = DeltaTreeModel n T := by
  rw [normalFormRaw_signed_sum_eq_two_pow_Xpoly_toNat n T hT]
  exact (DeltaTreeModel_closed_Xpoly n T).symm

theorem legacy_signed_sum_eq_DeltaTreeModel
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawNormal.signedSum n T = DeltaTreeModel n T := by
  rw [legacy_signed_sum_eq_two_pow_Xpoly_toNat n T hT]
  exact (DeltaTreeModel_closed_Xpoly n T).symm

theorem normalFormSignedSum_eq_DeltaTreeModel
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.normalFormSignedSum n T = DeltaTreeModel n T := by
  rw [normalFormSignedSum_eq_two_pow_Xpoly_toNat n T hT]
  exact (DeltaTreeModel_closed_Xpoly n T).symm

theorem rawBitStringSignedSum_eq_DeltaTreeModel
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.rawBitStringSignedSum n T = DeltaTreeModel n T := by
  rw [rawBitStringSignedSum_eq_two_pow_Xpoly_toNat n T hT]
  exact (DeltaTreeModel_closed_Xpoly n T).symm

theorem modelCertificate_of_positiveWeights
    {T : RTree} (hT : RTree.PositiveWeights T) :
    RawPrimitive.ModelCertificate T where
  positiveWeights := hT
  signedSum_eq_DeltaTreeModel := by
    intro n _
    exact legacy_signed_sum_eq_DeltaTreeModel n T hT

theorem nodeStepRule : RawPrimitive.NodeStepRule := by
  intro a cs ha hchildren n _
  have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
    intro C hC
    exact RawPrimitive.SubtreeModelCertificate.positiveWeights
      (hchildren C hC)
  have hpos : RTree.PositiveWeights (RTree.node a cs) := by
    have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
      ⟨ha, hchildPos⟩
    simpa [RTree.PositiveWeights] using hnode
  exact legacy_signed_sum_eq_DeltaTreeModel n (RTree.node a cs) hpos

theorem nodeStepCertificate_of_positiveWeights
    {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    RawPrimitive.NodeStepCertificate a cs := by
  have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
    simpa [RTree.PositiveWeights] using hT
  have hchildren : ∀ C ∈ cs, RawPrimitive.SubtreeModelCertificate C := by
    intro C hC
    exact RawPrimitive.subtreeModelCertificate_of_positiveWeights_of_nodeStepRule
      nodeStepRule (hnode.2 C hC)
  exact RawPrimitive.nodeStepCertificate_of_rule nodeStepRule
    hnode.1 hchildren

theorem subtreeModelCertificate_of_positiveWeights
    {T : RTree} (hT : RTree.PositiveWeights T) :
    RawPrimitive.SubtreeModelCertificate T :=
  RawPrimitive.subtreeModelCertificate_of_positiveWeights_of_nodeStepRule
    nodeStepRule hT

theorem globalRawBitStringClosedXpoly :
    RawPrimitive.GlobalRawBitStringClosedXpoly :=
  RawPrimitive.globalRawBitStringClosedXpoly_of_nodeStepRule nodeStepRule

theorem globalRawBitStringClosedConnectedTerms :
    RawPrimitive.GlobalRawBitStringClosedConnectedTerms :=
  RawPrimitive.globalRawBitStringClosedConnectedTerms_of_nodeStepRule nodeStepRule

noncomputable def signedReductionBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    SignedReductionBridge n T hT (NormalAssignmentClean n T) :=
  canonicalShearedSignedReductionBridge n T hT

theorem signedReductionBridge_DeltaRaw_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (signedReductionBridge n T hT).DeltaRaw = (2 : ℤ) ^ Xdim n T :=
  canonicalShearedSignedReductionBridge_DeltaRaw_eq_two_pow_Xdim n T hT

theorem signedReductionBridge_DeltaRaw_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (signedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [Xpoly_toNat_eq_Xdim n T hT]
  exact signedReductionBridge_DeltaRaw_eq_two_pow_Xdim n T hT

theorem signedReductionBridge_DeltaRaw_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (signedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [allTerms_toNat_eq_Xdim n T hT]
  exact signedReductionBridge_DeltaRaw_eq_two_pow_Xdim n T hT

noncomputable def realizedRawSignedReductionBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    SignedReductionBridge n T hT (NormalFormRawAssignmentsClean n T) :=
  canonicalShearedRealizedRawSignedReductionBridge n T hT

theorem realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawSignedReductionBridge n T hT).DeltaRaw = (2 : ℤ) ^ Xdim n T :=
  canonicalShearedRealizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_Xdim n T hT

theorem realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawSignedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [Xpoly_toNat_eq_Xdim n T hT]
  exact realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_Xdim n T hT

theorem realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawSignedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [allTerms_toNat_eq_Xdim n T hT]
  exact realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_Xdim n T hT

noncomputable def realizedRawGraphBridge
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    GraphPhysicalRealizedRawBridge n Graph :=
  canonicalSheared n graph T hT

noncomputable def realizedRawRootedBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    GraphPhysicalRealizedRawBridge n PUnit :=
  canonicalShearedRooted n T hT

theorem realizedRaw_graph_eq_two_pow_Xdim
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawGraphBridge n graph T hT).DeltaGraph =
      (2 : ℤ) ^ Xdim n T :=
  canonicalSheared_tree_imbalance_formula_connected_realizedRaw n graph T hT

theorem realizedRaw_graph_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawGraphBridge n graph T hT).DeltaGraph =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [Xpoly_toNat_eq_Xdim n T hT]
  exact realizedRaw_graph_eq_two_pow_Xdim n graph T hT

theorem realizedRaw_graph_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawGraphBridge n graph T hT).DeltaGraph =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [allTerms_toNat_eq_Xdim n T hT]
  exact realizedRaw_graph_eq_two_pow_Xdim n graph T hT

theorem realizedRaw_graph_eq_two_pow_allTerms
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (realizedRawGraphBridge n graph T hT).DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) :=
  canonicalSheared_tree_imbalance_formula_connected_terms_realizedRaw n graph T hT

theorem realizedRaw_graph_eq_two_pow_Xpoly
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (realizedRawGraphBridge n graph T hT).DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T :=
  canonicalSheared_tree_imbalance_formula_connected_Xpoly_realizedRaw n graph T hT

theorem realizedRaw_rooted_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawRootedBridge n T hT).DeltaGraph = (2 : ℤ) ^ Xdim n T :=
  canonicalShearedRooted_tree_imbalance_formula_connected_realizedRaw n T hT

theorem realizedRaw_rooted_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawRootedBridge n T hT).DeltaGraph =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [Xpoly_toNat_eq_Xdim n T hT]
  exact realizedRaw_rooted_eq_two_pow_Xdim n T hT

theorem realizedRaw_rooted_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawRootedBridge n T hT).DeltaGraph =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [allTerms_toNat_eq_Xdim n T hT]
  exact realizedRaw_rooted_eq_two_pow_Xdim n T hT

theorem realizedRaw_rooted_eq_two_pow_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (realizedRawRootedBridge n T hT).DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) :=
  canonicalShearedRooted_tree_imbalance_formula_connected_terms_realizedRaw n T hT

theorem realizedRaw_rooted_eq_two_pow_Xpoly
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (realizedRawRootedBridge n T hT).DeltaGraph = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T :=
  canonicalShearedRooted_tree_imbalance_formula_connected_Xpoly_realizedRaw n T hT

end CanonicalSheared

end Imbalance
end TreeGraph
