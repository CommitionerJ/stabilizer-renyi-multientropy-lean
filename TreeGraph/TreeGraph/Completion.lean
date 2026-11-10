import TreeGraph.OpenRootLocalCertificate

namespace TreeGraph

namespace RawPrimitive

structure CompleteFormalization : Prop where
  localRawBitStringDeltaStepRule : LocalRawBitStringDeltaStepRule
  localModelCertificateStepRule : LocalModelCertificateStepRule
  openRootRawBitStringNodeStepRule : OpenRootRawBitStringNodeStepRule
  globalRawBitStringClosedXassign : GlobalRawBitStringClosedXassign
  globalRawBitStringClosedXpoly : GlobalRawBitStringClosedXpoly
  globalRawBitStringClosedConnectedTerms :
    GlobalRawBitStringClosedConnectedTerms
  globalRawBitStringClosedAssignmentFactorProduct :
    GlobalRawBitStringClosedAssignmentFactorProduct
  globalSignedSumClosedAssignmentFactorProduct :
    GlobalSignedSumClosedAssignmentFactorProduct
  rawBitStringSignedSum_eq_DeltaTreeModel :
    ∀ {T : RTree}, RTree.PositiveWeights T →
      ∀ (n : Nat) [NeZero n],
        rawBitStringSignedSum n T = DeltaTreeModel n T
  rawBitStringSignedSum_closed_Xassign :
    ∀ {T : RTree}, RTree.PositiveWeights T →
      ∀ (n : Nat) [NeZero n],
        rawBitStringSignedSum n T =
          (2 : ℤ) ^ Int.toNat (Xassign n T)
  rawBitStringSignedSum_closed_Xpoly :
    ∀ {T : RTree}, RTree.PositiveWeights T →
      ∀ (n : Nat) [NeZero n],
        rawBitStringSignedSum n T =
          (2 : ℤ) ^ Int.toNat (Xpoly n T)
  rawBitStringSignedSum_closed_connected_terms :
    ∀ {T : RTree}, RTree.PositiveWeights T →
      ∀ (n : Nat) [NeZero n],
        rawBitStringSignedSum n T =
          (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))
  normalFormSignedSum_closed_connected_terms :
    ∀ {T : RTree}, RTree.PositiveWeights T →
      ∀ (n : Nat) [NeZero n],
        normalFormSignedSum n T =
          (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))
  subtreeModelCertificate :
    ∀ {T : RTree}, RTree.PositiveWeights T → SubtreeModelCertificate T
  modelCertificate :
    ∀ {T : RTree}, RTree.PositiveWeights T → ModelCertificate T

theorem completeFormalization_of_localRawBitStringDeltaStepRule
    (hlocal : LocalRawBitStringDeltaStepRule) :
    CompleteFormalization where
  localRawBitStringDeltaStepRule := hlocal
  localModelCertificateStepRule :=
    (localModelCertificateStepRule_iff_openRootRawBitStringNodeStepRule).2
      (openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule
        hlocal)
  openRootRawBitStringNodeStepRule :=
    openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule
      hlocal
  globalRawBitStringClosedXassign :=
    (localRawBitStringDeltaStepRule_iff_globalRawBitStringClosedXassign).1
      hlocal
  globalRawBitStringClosedXpoly :=
    (localRawBitStringDeltaStepRule_iff_globalRawBitStringClosedXpoly).1
      hlocal
  globalRawBitStringClosedConnectedTerms :=
    (localRawBitStringDeltaStepRule_iff_globalRawBitStringClosedConnectedTerms).1
      hlocal
  globalRawBitStringClosedAssignmentFactorProduct :=
    globalRawBitStringClosedAssignmentFactorProduct_of_openRootRawBitStringNodeStepRule
      (openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule
        hlocal)
  globalSignedSumClosedAssignmentFactorProduct :=
    globalSignedAssignmentFactorProduct_of_openRootRawNodeStep
      (openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule
        hlocal)
  rawBitStringSignedSum_eq_DeltaTreeModel := by
    intro T hT n _
    exact rawBitStringSignedSum_eq_DeltaTreeModel_of_localRawBitStringDeltaStepRule
      hlocal hT n
  rawBitStringSignedSum_closed_Xassign := by
    intro T hT n _
    exact rawBitStringSignedSum_closed_Xassign_of_localRawBitStringDeltaStepRule
      hlocal hT n
  rawBitStringSignedSum_closed_Xpoly := by
    intro T hT n _
    exact rawBitStringSignedSum_closed_Xpoly_of_localRawBitStringDeltaStepRule
      hlocal hT n
  rawBitStringSignedSum_closed_connected_terms := by
    intro T hT n _
    exact rawBitStringSignedSum_closed_connected_terms_of_localRawBitStringDeltaStepRule
      hlocal hT n
  normalFormSignedSum_closed_connected_terms := by
    intro T hT n _
    exact normalFormSignedSum_closed_connected_terms_of_localRawBitStringDeltaStepRule
      hlocal hT n
  subtreeModelCertificate := by
    intro T hT
    exact subtreeModelCertificate_of_positiveWeights_of_localRawBitStringDeltaStepRule
      hlocal hT
  modelCertificate := by
    intro T hT
    exact modelCertificate_of_positiveWeights_of_localRawBitStringDeltaStepRule
      hlocal hT

theorem localRawBitStringDeltaStepRule_of_completeFormalization
    (h : CompleteFormalization) :
    LocalRawBitStringDeltaStepRule :=
  h.localRawBitStringDeltaStepRule

theorem completeFormalization_iff_localRawBitStringDeltaStepRule :
    CompleteFormalization ↔ LocalRawBitStringDeltaStepRule :=
  ⟨localRawBitStringDeltaStepRule_of_completeFormalization,
    completeFormalization_of_localRawBitStringDeltaStepRule⟩

theorem localRawBitStringDeltaStepRule_iff_completeFormalization :
    LocalRawBitStringDeltaStepRule ↔ CompleteFormalization :=
  completeFormalization_iff_localRawBitStringDeltaStepRule.symm

theorem completeFormalization_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule) :
    CompleteFormalization :=
  completeFormalization_of_localRawBitStringDeltaStepRule
    ((localRawBitStringDeltaStepRule_iff_openRootRawBitStringNodeStepRule).2
      ((localModelCertificateStepRule_iff_openRootRawBitStringNodeStepRule).1
        hlocal))

theorem localModelCertificateStepRule_iff_completeFormalization :
    LocalModelCertificateStepRule ↔ CompleteFormalization := by
  constructor
  · exact completeFormalization_of_localModelCertificateStepRule
  · intro h
    exact h.localModelCertificateStepRule

theorem completeFormalization_of_openRootRawBitStringNodeStepRule
    (hopen : OpenRootRawBitStringNodeStepRule) :
    CompleteFormalization :=
  completeFormalization_of_localRawBitStringDeltaStepRule
    ((localRawBitStringDeltaStepRule_iff_openRootRawBitStringNodeStepRule).2
      hopen)

theorem completeFormalization_iff_openRootRawBitStringNodeStepRule :
    CompleteFormalization ↔ OpenRootRawBitStringNodeStepRule := by
  constructor
  · intro h
    exact h.openRootRawBitStringNodeStepRule
  · exact completeFormalization_of_openRootRawBitStringNodeStepRule

theorem openRootRawBitStringNodeStepRule_iff_completeFormalization :
    OpenRootRawBitStringNodeStepRule ↔ CompleteFormalization :=
  completeFormalization_iff_openRootRawBitStringNodeStepRule.symm

theorem completeFormalization_of_globalRawBitStringClosedAssignmentFactorProduct
    (hglobal : GlobalRawBitStringClosedAssignmentFactorProduct) :
    CompleteFormalization :=
  completeFormalization_of_openRootRawBitStringNodeStepRule
    (openRootRawBitStringNodeStepRule_of_globalRawBitStringClosedAssignmentFactorProduct
      hglobal)

theorem completeFormalization_iff_globalRawBitStringClosedAssignmentFactorProduct :
    CompleteFormalization ↔
      GlobalRawBitStringClosedAssignmentFactorProduct := by
  constructor
  · intro h
    exact h.globalRawBitStringClosedAssignmentFactorProduct
  · exact completeFormalization_of_globalRawBitStringClosedAssignmentFactorProduct

theorem globalRawBitStringClosedAssignmentFactorProduct_iff_completeFormalization :
    GlobalRawBitStringClosedAssignmentFactorProduct ↔
      CompleteFormalization :=
  completeFormalization_iff_globalRawBitStringClosedAssignmentFactorProduct.symm

theorem completeFormalization_of_globalSignedSumClosedAssignmentFactorProduct
    (hglobal : GlobalSignedSumClosedAssignmentFactorProduct) :
    CompleteFormalization :=
  completeFormalization_of_globalRawBitStringClosedAssignmentFactorProduct
    (globalRawAssignmentFactorProduct_of_globalSigned hglobal)

theorem completeFormalization_iff_globalSignedSumClosedAssignmentFactorProduct :
    CompleteFormalization ↔
      GlobalSignedSumClosedAssignmentFactorProduct := by
  constructor
  · intro h
    exact h.globalSignedSumClosedAssignmentFactorProduct
  · exact completeFormalization_of_globalSignedSumClosedAssignmentFactorProduct

theorem globalSignedSumClosedAssignmentFactorProduct_iff_completeFormalization :
    GlobalSignedSumClosedAssignmentFactorProduct ↔
      CompleteFormalization :=
  completeFormalization_iff_globalSignedSumClosedAssignmentFactorProduct.symm

theorem completeFormalization_of_nodeStepRule
    (hstep : NodeStepRule) :
    CompleteFormalization :=
  completeFormalization_of_openRootRawBitStringNodeStepRule
    (openRootRawBitStringNodeStepRule_of_nodeStepRule hstep)

theorem nodeStepRule_of_completeFormalization
    (h : CompleteFormalization) :
    NodeStepRule :=
  nodeStepRule_of_openRootRawBitStringNodeStepRule
    h.openRootRawBitStringNodeStepRule

theorem completeFormalization_iff_nodeStepRule :
    CompleteFormalization ↔ NodeStepRule :=
  ⟨nodeStepRule_of_completeFormalization,
    completeFormalization_of_nodeStepRule⟩

theorem nodeStepRule_iff_completeFormalization :
    NodeStepRule ↔ CompleteFormalization :=
  completeFormalization_iff_nodeStepRule.symm

theorem completeFormalization_of_globalSignedSumRealizesAssignmentExponent
    (hglobal : GlobalSignedSumRealizesAssignmentExponent) :
    CompleteFormalization :=
  completeFormalization_of_nodeStepRule
    ((nodeStepRule_iff_globalSignedSumRealizesAssignmentExponent).2 hglobal)

theorem globalSignedSumRealizesAssignmentExponent_of_completeFormalization
    (h : CompleteFormalization) :
    GlobalSignedSumRealizesAssignmentExponent :=
  (nodeStepRule_iff_globalSignedSumRealizesAssignmentExponent).1
    (nodeStepRule_of_completeFormalization h)

theorem completeFormalization_iff_globalSignedSumRealizesAssignmentExponent :
    CompleteFormalization ↔ GlobalSignedSumRealizesAssignmentExponent :=
  ⟨globalSignedSumRealizesAssignmentExponent_of_completeFormalization,
    completeFormalization_of_globalSignedSumRealizesAssignmentExponent⟩

theorem globalSignedSumRealizesAssignmentExponent_iff_completeFormalization :
    GlobalSignedSumRealizesAssignmentExponent ↔ CompleteFormalization :=
  completeFormalization_iff_globalSignedSumRealizesAssignmentExponent.symm

theorem completeFormalization_of_globalSignedSumClosedDeltaTreeModel
    (hglobal : GlobalSignedSumClosedDeltaTreeModel) :
    CompleteFormalization :=
  completeFormalization_of_globalSignedSumRealizesAssignmentExponent
    (globalSignedSumRealizesAssignmentExponent_of_globalSignedSumClosedDeltaTreeModel
      hglobal)

theorem completeFormalization_iff_globalSignedSumClosedDeltaTreeModel :
    CompleteFormalization ↔ GlobalSignedSumClosedDeltaTreeModel :=
  completeFormalization_iff_globalSignedSumRealizesAssignmentExponent.trans
    globalSignedSumRealizesAssignmentExponent_iff_globalSignedSumClosedDeltaTreeModel

theorem globalSignedSumClosedDeltaTreeModel_iff_completeFormalization :
    GlobalSignedSumClosedDeltaTreeModel ↔ CompleteFormalization :=
  completeFormalization_iff_globalSignedSumClosedDeltaTreeModel.symm

theorem completeFormalization_of_globalSignedSumClosedXpoly
    (hglobal : GlobalSignedSumClosedXpoly) :
    CompleteFormalization :=
  completeFormalization_of_globalSignedSumRealizesAssignmentExponent
    (globalSignedSumRealizesAssignmentExponent_of_globalSignedSumClosedXpoly
      hglobal)

theorem completeFormalization_iff_globalSignedSumClosedXpoly :
    CompleteFormalization ↔ GlobalSignedSumClosedXpoly :=
  completeFormalization_iff_globalSignedSumRealizesAssignmentExponent.trans
    globalSignedSumRealizesAssignmentExponent_iff_globalSignedSumClosedXpoly

theorem globalSignedSumClosedXpoly_iff_completeFormalization :
    GlobalSignedSumClosedXpoly ↔ CompleteFormalization :=
  completeFormalization_iff_globalSignedSumClosedXpoly.symm

theorem completeFormalization_of_globalSignedSumClosedConnectedTerms
    (hglobal : GlobalSignedSumClosedConnectedTerms) :
    CompleteFormalization :=
  completeFormalization_of_globalSignedSumRealizesAssignmentExponent
    (globalSignedSumRealizesAssignmentExponent_of_globalSignedSumClosedConnectedTerms
      hglobal)

theorem completeFormalization_iff_globalSignedSumClosedConnectedTerms :
    CompleteFormalization ↔ GlobalSignedSumClosedConnectedTerms :=
  completeFormalization_iff_globalSignedSumRealizesAssignmentExponent.trans
    globalSignedSumRealizesAssignmentExponent_iff_globalSignedSumClosedConnectedTerms

theorem globalSignedSumClosedConnectedTerms_iff_completeFormalization :
    GlobalSignedSumClosedConnectedTerms ↔ CompleteFormalization :=
  completeFormalization_iff_globalSignedSumClosedConnectedTerms.symm

theorem completeFormalization_of_positiveAssignmentRecursionWitness
    (hwitness : PositiveAssignmentRecursionWitness) :
    CompleteFormalization :=
  completeFormalization_of_globalSignedSumClosedXpoly
    (globalSignedSumClosedXpoly_of_positiveAssignmentRecursionWitness
      hwitness)

theorem completeFormalization_iff_positiveAssignmentRecursionWitness :
    CompleteFormalization ↔ PositiveAssignmentRecursionWitness :=
  completeFormalization_iff_globalSignedSumClosedXpoly.trans
    globalSignedSumClosedXpoly_iff_positiveAssignmentRecursionWitness

theorem positiveAssignmentRecursionWitness_iff_completeFormalization :
    PositiveAssignmentRecursionWitness ↔ CompleteFormalization :=
  completeFormalization_iff_positiveAssignmentRecursionWitness.symm

theorem rawBitStringSignedSum_eq_DeltaTreeModel_of_positiveAssignmentRecursionWitness
    (hwitness : PositiveAssignmentRecursionWitness)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = DeltaTreeModel n T :=
  (completeFormalization_of_positiveAssignmentRecursionWitness
    hwitness).rawBitStringSignedSum_eq_DeltaTreeModel hT n

theorem rawBitStringSignedSum_closed_connected_terms_of_positiveAssignmentRecursionWitness
    (hwitness : PositiveAssignmentRecursionWitness)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  (completeFormalization_of_positiveAssignmentRecursionWitness
    hwitness).rawBitStringSignedSum_closed_connected_terms hT n

theorem normalFormSignedSum_closed_connected_terms_of_positiveAssignmentRecursionWitness
    (hwitness : PositiveAssignmentRecursionWitness)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  (completeFormalization_of_positiveAssignmentRecursionWitness
    hwitness).normalFormSignedSum_closed_connected_terms hT n

theorem modelCertificate_of_positiveWeights_of_positiveAssignmentRecursionWitness
    (hwitness : PositiveAssignmentRecursionWitness)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    ModelCertificate T :=
  (completeFormalization_of_positiveAssignmentRecursionWitness
    hwitness).modelCertificate hT

theorem completeFormalization_of_globalRawBitStringClosedXassign
    (hglobal : GlobalRawBitStringClosedXassign) :
    CompleteFormalization :=
  completeFormalization_of_localRawBitStringDeltaStepRule
    ((localRawBitStringDeltaStepRule_iff_globalRawBitStringClosedXassign).2
      hglobal)

theorem completeFormalization_iff_globalRawBitStringClosedXassign :
    CompleteFormalization ↔ GlobalRawBitStringClosedXassign := by
  constructor
  · intro h
    exact h.globalRawBitStringClosedXassign
  · exact completeFormalization_of_globalRawBitStringClosedXassign

theorem completeFormalization_of_globalRawBitStringClosedXpoly
    (hglobal : GlobalRawBitStringClosedXpoly) :
    CompleteFormalization :=
  completeFormalization_of_localRawBitStringDeltaStepRule
    ((localRawBitStringDeltaStepRule_iff_globalRawBitStringClosedXpoly).2
      hglobal)

theorem completeFormalization_iff_globalRawBitStringClosedXpoly :
    CompleteFormalization ↔ GlobalRawBitStringClosedXpoly := by
  constructor
  · intro h
    exact h.globalRawBitStringClosedXpoly
  · exact completeFormalization_of_globalRawBitStringClosedXpoly

theorem completeFormalization_of_globalRawBitStringClosedConnectedTerms
    (hglobal : GlobalRawBitStringClosedConnectedTerms) :
    CompleteFormalization :=
  completeFormalization_of_localRawBitStringDeltaStepRule
    ((localRawBitStringDeltaStepRule_iff_globalRawBitStringClosedConnectedTerms).2
      hglobal)

theorem completeFormalization_iff_globalRawBitStringClosedConnectedTerms :
    CompleteFormalization ↔ GlobalRawBitStringClosedConnectedTerms := by
  constructor
  · intro h
    exact h.globalRawBitStringClosedConnectedTerms
  · exact completeFormalization_of_globalRawBitStringClosedConnectedTerms

theorem completeFormalization_of_forall_rawBitString_eq_DeltaTreeModel
    (hglobal :
      ∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T = DeltaTreeModel n T) :
    CompleteFormalization :=
  completeFormalization_of_localRawBitStringDeltaStepRule
    ((localRawBitStringDeltaStepRule_iff_forall_rawBitString_eq_DeltaTreeModel).2
      hglobal)

theorem completeFormalization_iff_forall_rawBitString_eq_DeltaTreeModel :
    CompleteFormalization ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T = DeltaTreeModel n T) := by
  constructor
  · intro h
    exact h.rawBitStringSignedSum_eq_DeltaTreeModel
  · exact completeFormalization_of_forall_rawBitString_eq_DeltaTreeModel

theorem completeFormalization_iff_forall_rawBitString_closed_Xassign :
    CompleteFormalization ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xassign n T)) := by
  constructor
  · intro h
    exact h.rawBitStringSignedSum_closed_Xassign
  · exact completeFormalization_of_globalRawBitStringClosedXassign

theorem completeFormalization_iff_forall_rawBitString_closed_Xpoly :
    CompleteFormalization ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xpoly n T)) := by
  constructor
  · intro h
    exact h.rawBitStringSignedSum_closed_Xpoly
  · exact completeFormalization_of_globalRawBitStringClosedXpoly

theorem completeFormalization_iff_forall_rawBitString_closed_connected_terms :
    CompleteFormalization ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))) := by
  constructor
  · intro h
    exact h.rawBitStringSignedSum_closed_connected_terms
  · exact completeFormalization_of_globalRawBitStringClosedConnectedTerms

theorem positiveAssignmentRecursionWitness_iff_forall_rawBitString_eq_DeltaTreeModel :
    PositiveAssignmentRecursionWitness ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T = DeltaTreeModel n T) :=
  positiveAssignmentRecursionWitness_iff_completeFormalization.trans
    completeFormalization_iff_forall_rawBitString_eq_DeltaTreeModel

theorem positiveAssignmentRecursionWitness_iff_forall_rawBitString_closed_Xassign :
    PositiveAssignmentRecursionWitness ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xassign n T)) :=
  positiveAssignmentRecursionWitness_iff_completeFormalization.trans
    completeFormalization_iff_forall_rawBitString_closed_Xassign

theorem positiveAssignmentRecursionWitness_iff_forall_rawBitString_closed_Xpoly :
    PositiveAssignmentRecursionWitness ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xpoly n T)) :=
  positiveAssignmentRecursionWitness_iff_completeFormalization.trans
    completeFormalization_iff_forall_rawBitString_closed_Xpoly

theorem positiveAssignmentRecursionWitness_iff_forall_rawBitString_closed_connected_terms :
    PositiveAssignmentRecursionWitness ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))) :=
  positiveAssignmentRecursionWitness_iff_completeFormalization.trans
    completeFormalization_iff_forall_rawBitString_closed_connected_terms

theorem completeFormalization_of_forall_subtreeModelCertificate
    (hcert :
      ∀ {T : RTree}, RTree.PositiveWeights T → SubtreeModelCertificate T) :
    CompleteFormalization :=
  completeFormalization_of_nodeStepRule
    (by
      intro a cs ha hchildren n _
      have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
        intro C hC
        exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
      have hpos : RTree.PositiveWeights (RTree.node a cs) := by
        have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
          ⟨ha, hchildPos⟩
        simpa [RTree.PositiveWeights] using hnode
      exact SubtreeModelCertificate.signedSum_eq_DeltaTreeModel
        (hcert hpos) n)

theorem completeFormalization_iff_forall_subtreeModelCertificate :
    CompleteFormalization ↔
      (∀ {T : RTree}, RTree.PositiveWeights T → SubtreeModelCertificate T) := by
  constructor
  · intro h T hT
    exact h.subtreeModelCertificate hT
  · exact completeFormalization_of_forall_subtreeModelCertificate

theorem forall_subtreeModelCertificate_iff_completeFormalization :
    (∀ {T : RTree}, RTree.PositiveWeights T → SubtreeModelCertificate T) ↔
      CompleteFormalization :=
  completeFormalization_iff_forall_subtreeModelCertificate.symm

theorem completeFormalization_of_forall_modelCertificate
    (hcert :
      ∀ {T : RTree}, RTree.PositiveWeights T → ModelCertificate T) :
    CompleteFormalization :=
  completeFormalization_of_nodeStepRule
    (by
      intro a cs ha hchildren n _
      have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
        intro C hC
        exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
      have hpos : RTree.PositiveWeights (RTree.node a cs) := by
        have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
          ⟨ha, hchildPos⟩
        simpa [RTree.PositiveWeights] using hnode
      exact ModelCertificate.signedSum_eq_DeltaTreeModel
        (hcert hpos) n)

theorem completeFormalization_iff_forall_modelCertificate :
    CompleteFormalization ↔
      (∀ {T : RTree}, RTree.PositiveWeights T → ModelCertificate T) := by
  constructor
  · intro h T hT
    exact h.modelCertificate hT
  · exact completeFormalization_of_forall_modelCertificate

theorem forall_modelCertificate_iff_completeFormalization :
    (∀ {T : RTree}, RTree.PositiveWeights T → ModelCertificate T) ↔
      CompleteFormalization :=
  completeFormalization_iff_forall_modelCertificate.symm

noncomputable def localCombinatorialNodeExponent
    (n a : Nat) (cs : List RTree) : ℤ :=
  ((independentBranchDimension n cs : Nat) : ℤ) +
    childContribSumWith (Xassign n) n a cs 0

theorem localCombinatorialNodeExponent_eq_openRootNodeExponent
    (n a : Nat) (cs : List RTree) :
    localCombinatorialNodeExponent n a cs =
      openRootNodeExponent n a cs := by
  unfold localCombinatorialNodeExponent openRootNodeExponent
  rw [finrank_openRootMessageSpace]

theorem localCombinatorialNodeExponent_eq_assignmentFactorProduct
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C) :
    localCombinatorialNodeExponent n a cs =
      (((cs.map (fun C =>
        Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
          Nat) : ℤ) +
        childContribSumWith (Xassign n) n a cs 0 := by
  unfold localCombinatorialNodeExponent
  rw [independentBranchDimension_eq_assignmentFactorProduct
    (n := n) hchildren]

theorem localCombinatorialNodeExponent_eq_assignmentFactorProduct_of_positiveWeights
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    localCombinatorialNodeExponent n a cs =
      (((cs.map (fun C =>
        Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
          Nat) : ℤ) +
        childContribSumWith (Xassign n) n a cs 0 := by
  have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
    simpa [RTree.PositiveWeights] using hT
  exact localCombinatorialNodeExponent_eq_assignmentFactorProduct
    (n := n) (a := a) (cs := cs) hnode.2

theorem localCombinatorialNodeExponent_eq_Xassign_of_children
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    localCombinatorialNodeExponent n a cs =
      Xassign n (RTree.node a cs) := by
  rw [localCombinatorialNodeExponent_eq_openRootNodeExponent]
  exact openRootNodeExponent_eq_Xassign_of_children
    (n := n) ha hchildren

theorem DeltaTreeModel_node_eq_localCombinatorialNodeExponent_of_children
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    DeltaTreeModel n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        (localCombinatorialNodeExponent n a cs) := by
  rw [localCombinatorialNodeExponent_eq_Xassign_of_children
    (n := n) ha hchildren]
  rfl

theorem localCombinatorialNodeExponent_eq_Xassign_of_positiveWeights
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    localCombinatorialNodeExponent n a cs =
      Xassign n (RTree.node a cs) := by
  rw [localCombinatorialNodeExponent_eq_openRootNodeExponent]
  exact openRootNodeExponent_eq_Xassign_of_positiveWeights
    (n := n) hT

theorem DeltaTreeModel_node_eq_localCombinatorialNodeExponent_of_positiveWeights
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    DeltaTreeModel n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        (localCombinatorialNodeExponent n a cs) := by
  rw [localCombinatorialNodeExponent_eq_Xassign_of_positiveWeights
    (n := n) hT]
  rfl

def LocalSignedSumCombinatorialStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, SubtreeModelCertificate C) →
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n (RTree.node a cs) =
        (2 : ℤ) ^ Int.toNat
          (localCombinatorialNodeExponent n a cs)

def LocalRawBitStringCombinatorialStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, SubtreeModelCertificate C) →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n (RTree.node a cs) =
        (2 : ℤ) ^ Int.toNat
          (localCombinatorialNodeExponent n a cs)

def PositiveLocalSignedSumCombinatorialStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    RTree.PositiveWeights (RTree.node a cs) →
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n (RTree.node a cs) =
        (2 : ℤ) ^ Int.toNat
          (localCombinatorialNodeExponent n a cs)

def PositiveLocalRawBitStringCombinatorialStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    RTree.PositiveWeights (RTree.node a cs) →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n (RTree.node a cs) =
        (2 : ℤ) ^ Int.toNat
          (localCombinatorialNodeExponent n a cs)

def PositiveLocalRawBitStringDeltaStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    RTree.PositiveWeights (RTree.node a cs) →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n (RTree.node a cs) =
        DeltaTreeModel n (RTree.node a cs)

def PositiveLocalSignedSumDeltaStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    RTree.PositiveWeights (RTree.node a cs) →
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n (RTree.node a cs) =
        DeltaTreeModel n (RTree.node a cs)

def PositiveLocalModelCertificateStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    RTree.PositiveWeights (RTree.node a cs) →
      ModelCertificate (RTree.node a cs)

theorem localSignedSumCombinatorialStepRule_of_nodeStepRule
    (hstep : NodeStepRule) :
    LocalSignedSumCombinatorialStepRule := by
  intro a cs ha hchildren n _
  have hnode := hstep ha hchildren n
  have hdelta :=
    DeltaTreeModel_node_eq_localCombinatorialNodeExponent_of_children
      (n := n) ha hchildren
  exact hnode.trans hdelta

theorem nodeStepRule_of_localSignedSumCombinatorialStepRule
    (hlocal : LocalSignedSumCombinatorialStepRule) :
    NodeStepRule := by
  intro a cs ha hchildren n _
  have hsigned := hlocal ha hchildren n
  have hdelta :=
    DeltaTreeModel_node_eq_localCombinatorialNodeExponent_of_children
      (n := n) ha hchildren
  exact hsigned.trans hdelta.symm

theorem nodeStepRule_iff_localSignedSumCombinatorialStepRule :
    NodeStepRule ↔ LocalSignedSumCombinatorialStepRule :=
  ⟨localSignedSumCombinatorialStepRule_of_nodeStepRule,
    nodeStepRule_of_localSignedSumCombinatorialStepRule⟩

theorem localSignedSumCombinatorialStepRule_iff_nodeStepRule :
    LocalSignedSumCombinatorialStepRule ↔ NodeStepRule :=
  nodeStepRule_iff_localSignedSumCombinatorialStepRule.symm

theorem localRawBitStringCombinatorialStepRule_of_openRootRawBitStringNodeStepRule
    (hopen : OpenRootRawBitStringNodeStepRule) :
    LocalRawBitStringCombinatorialStepRule := by
  intro a cs ha hchildren n _
  rw [localCombinatorialNodeExponent_eq_openRootNodeExponent]
  exact hopen ha hchildren n

theorem openRootRawBitStringNodeStepRule_of_localRawBitStringCombinatorialStepRule
    (hlocal : LocalRawBitStringCombinatorialStepRule) :
    OpenRootRawBitStringNodeStepRule := by
  intro a cs ha hchildren n _
  rw [← localCombinatorialNodeExponent_eq_openRootNodeExponent]
  exact hlocal ha hchildren n

theorem openRootRawBitStringNodeStepRule_iff_localRawBitStringCombinatorialStepRule :
    OpenRootRawBitStringNodeStepRule ↔
      LocalRawBitStringCombinatorialStepRule :=
  ⟨localRawBitStringCombinatorialStepRule_of_openRootRawBitStringNodeStepRule,
    openRootRawBitStringNodeStepRule_of_localRawBitStringCombinatorialStepRule⟩

theorem localRawBitStringCombinatorialStepRule_iff_openRootRawBitStringNodeStepRule :
    LocalRawBitStringCombinatorialStepRule ↔
      OpenRootRawBitStringNodeStepRule :=
  openRootRawBitStringNodeStepRule_iff_localRawBitStringCombinatorialStepRule.symm

theorem completeFormalization_of_localSignedSumCombinatorialStepRule
    (hlocal : LocalSignedSumCombinatorialStepRule) :
    CompleteFormalization :=
  completeFormalization_of_nodeStepRule
    (nodeStepRule_of_localSignedSumCombinatorialStepRule hlocal)

theorem completeFormalization_iff_localSignedSumCombinatorialStepRule :
    CompleteFormalization ↔ LocalSignedSumCombinatorialStepRule := by
  constructor
  · intro h
    exact localSignedSumCombinatorialStepRule_of_nodeStepRule
      (nodeStepRule_of_completeFormalization h)
  · exact completeFormalization_of_localSignedSumCombinatorialStepRule

theorem completeFormalization_of_localRawBitStringCombinatorialStepRule
    (hlocal : LocalRawBitStringCombinatorialStepRule) :
    CompleteFormalization :=
  completeFormalization_of_openRootRawBitStringNodeStepRule
    (openRootRawBitStringNodeStepRule_of_localRawBitStringCombinatorialStepRule
      hlocal)

theorem completeFormalization_iff_localRawBitStringCombinatorialStepRule :
    CompleteFormalization ↔ LocalRawBitStringCombinatorialStepRule := by
  constructor
  · intro h
    exact
      localRawBitStringCombinatorialStepRule_of_openRootRawBitStringNodeStepRule
        h.openRootRawBitStringNodeStepRule
  · exact completeFormalization_of_localRawBitStringCombinatorialStepRule

theorem localRawBitStringCombinatorialStepRule_iff_completeFormalization :
    LocalRawBitStringCombinatorialStepRule ↔ CompleteFormalization :=
  completeFormalization_iff_localRawBitStringCombinatorialStepRule.symm

theorem positiveWeights_node_of_subtreeModelCertificate_children
    {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    RTree.PositiveWeights (RTree.node a cs) := by
  have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
    intro C hC
    exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
  have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
    ⟨ha, hchildPos⟩
  simpa [RTree.PositiveWeights] using hnode

theorem localRawBitStringCombinatorialStepRule_of_localSignedSumCombinatorialStepRule
    (hlocal : LocalSignedSumCombinatorialStepRule) :
    LocalRawBitStringCombinatorialStepRule := by
  intro a cs ha hchildren n _
  have hpos :=
    positiveWeights_node_of_subtreeModelCertificate_children ha hchildren
  have hrawSigned :
      rawBitStringSignedSum n (RTree.node a cs) =
        RawNormal.signedSum n (RTree.node a cs) :=
    rawBitStringSignedSum_eq_signedSum_of_positiveWeights
      (n := n) (T := RTree.node a cs) hpos
  exact hrawSigned.trans (hlocal ha hchildren n)

theorem localSignedSumCombinatorialStepRule_of_localRawBitStringCombinatorialStepRule
    (hlocal : LocalRawBitStringCombinatorialStepRule) :
    LocalSignedSumCombinatorialStepRule := by
  intro a cs ha hchildren n _
  have hpos :=
    positiveWeights_node_of_subtreeModelCertificate_children ha hchildren
  have hrawSigned :
      rawBitStringSignedSum n (RTree.node a cs) =
        RawNormal.signedSum n (RTree.node a cs) :=
    rawBitStringSignedSum_eq_signedSum_of_positiveWeights
      (n := n) (T := RTree.node a cs) hpos
  exact hrawSigned.symm.trans (hlocal ha hchildren n)

theorem localSignedSumCombinatorialStepRule_iff_localRawBitStringCombinatorialStepRule :
    LocalSignedSumCombinatorialStepRule ↔
      LocalRawBitStringCombinatorialStepRule :=
  ⟨localRawBitStringCombinatorialStepRule_of_localSignedSumCombinatorialStepRule,
    localSignedSumCombinatorialStepRule_of_localRawBitStringCombinatorialStepRule⟩

theorem localRawBitStringCombinatorialStepRule_iff_localSignedSumCombinatorialStepRule :
    LocalRawBitStringCombinatorialStepRule ↔
      LocalSignedSumCombinatorialStepRule :=
  localSignedSumCombinatorialStepRule_iff_localRawBitStringCombinatorialStepRule.symm

theorem localRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedXassign :
    LocalRawBitStringCombinatorialStepRule ↔
      GlobalRawBitStringClosedXassign :=
  Iff.trans localRawBitStringCombinatorialStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXassign

theorem localRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedXpoly :
    LocalRawBitStringCombinatorialStepRule ↔
      GlobalRawBitStringClosedXpoly :=
  Iff.trans localRawBitStringCombinatorialStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXpoly

theorem localRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedConnectedTerms :
    LocalRawBitStringCombinatorialStepRule ↔
      GlobalRawBitStringClosedConnectedTerms :=
  Iff.trans localRawBitStringCombinatorialStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedConnectedTerms

theorem localRawBitStringCombinatorialStepRule_iff_forall_rawBitString_closed_Xassign :
    LocalRawBitStringCombinatorialStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xassign n T)) :=
  Iff.trans localRawBitStringCombinatorialStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_forall_rawBitString_closed_Xassign

theorem localRawBitStringCombinatorialStepRule_iff_forall_rawBitString_closed_Xpoly :
    LocalRawBitStringCombinatorialStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xpoly n T)) :=
  Iff.trans localRawBitStringCombinatorialStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_forall_rawBitString_closed_Xpoly

theorem localRawBitStringCombinatorialStepRule_iff_forall_rawBitString_closed_connected_terms :
    LocalRawBitStringCombinatorialStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))) :=
  Iff.trans localRawBitStringCombinatorialStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_forall_rawBitString_closed_connected_terms

theorem localRawBitStringCombinatorialStepRule_iff_forall_rawBitString_eq_DeltaTreeModel :
    LocalRawBitStringCombinatorialStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T = DeltaTreeModel n T) :=
  Iff.trans localRawBitStringCombinatorialStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_forall_rawBitString_eq_DeltaTreeModel

theorem rawBitStringSignedSum_closed_Xassign_of_localRawBitStringCombinatorialStepRule
    (hlocal : LocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xassign n T) :=
  (localRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedXassign.1
    hlocal) hT n

theorem rawBitStringSignedSum_closed_Xpoly_of_localRawBitStringCombinatorialStepRule
    (hlocal : LocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  (localRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedXpoly.1
    hlocal) hT n

theorem rawBitStringSignedSum_closed_connected_terms_of_localRawBitStringCombinatorialStepRule
    (hlocal : LocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  (localRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedConnectedTerms.1
    hlocal) hT n

theorem rawBitStringSignedSum_eq_DeltaTreeModel_of_localRawBitStringCombinatorialStepRule
    (hlocal : LocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = DeltaTreeModel n T :=
  (localRawBitStringCombinatorialStepRule_iff_forall_rawBitString_eq_DeltaTreeModel.1
    hlocal) hT n

theorem normalFormSignedSum_closed_connected_terms_of_localRawBitStringCombinatorialStepRule
    (hlocal : LocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  change rawBitStringSignedSum n T =
    (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))
  exact
    rawBitStringSignedSum_closed_connected_terms_of_localRawBitStringCombinatorialStepRule
      hlocal hT n

theorem rawBitStringClosed_assignmentFactorProduct_of_localCombinatorial
    (hlocal : LocalRawBitStringCombinatorialStepRule)
    {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) := by
  have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
    intro C hC
    exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
  have hraw := hlocal ha hchildren n
  rw [localCombinatorialNodeExponent_eq_assignmentFactorProduct
    (n := n) (a := a) (cs := cs) hchildPos] at hraw
  exact hraw

def LocalAssignmentFactorProductNodeRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, SubtreeModelCertificate C) →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n (RTree.node a cs) =
        (2 : ℤ) ^ Int.toNat
          ((((cs.map (fun C =>
            Int.toNat
              ((nZ n) ^ RTree.totalWeight C -
                (tZ n) * Yassign n C))).prod : Nat) : ℤ) +
            childContribSumWith (Xassign n) n a cs 0)

theorem localRawBitStringCombinatorialStepRule_iff_assignmentFactorProduct_node :
    LocalRawBitStringCombinatorialStepRule ↔
      LocalAssignmentFactorProductNodeRule := by
  constructor
  · intro hlocal a cs ha hchildren n _
    exact
      rawBitStringClosed_assignmentFactorProduct_of_localCombinatorial
        hlocal ha hchildren n
  · intro hfactor a cs ha hchildren n _
    have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
      intro C hC
      exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
    have hraw := hfactor ha hchildren n
    rw [localCombinatorialNodeExponent_eq_assignmentFactorProduct
      (n := n) (a := a) (cs := cs) hchildPos]
    exact hraw

theorem assignmentFactorProductNodeRule_iff_localRawBitStringCombinatorialStepRule :
    LocalAssignmentFactorProductNodeRule ↔
      LocalRawBitStringCombinatorialStepRule :=
  localRawBitStringCombinatorialStepRule_iff_assignmentFactorProduct_node.symm

theorem completeFormalization_iff_localAssignmentFactorProductNodeRule :
    CompleteFormalization ↔ LocalAssignmentFactorProductNodeRule :=
  completeFormalization_iff_localRawBitStringCombinatorialStepRule.trans
    localRawBitStringCombinatorialStepRule_iff_assignmentFactorProduct_node

theorem localAssignmentFactorProductNodeRule_iff_completeFormalization :
    LocalAssignmentFactorProductNodeRule ↔ CompleteFormalization :=
  completeFormalization_iff_localAssignmentFactorProductNodeRule.symm

theorem rawBitStringSignedSum_closed_assignmentFactorProduct_of_completeFormalization_local
    (h : CompleteFormalization)
    {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) :=
  (completeFormalization_iff_localAssignmentFactorProductNodeRule.1 h)
    ha hchildren n

theorem subtreeModelCertificate_of_positiveWeights_of_localRawBitStringCombinatorialStepRule
    (hlocal : LocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    SubtreeModelCertificate T :=
  (completeFormalization_of_localRawBitStringCombinatorialStepRule
    hlocal).subtreeModelCertificate hT

theorem modelCertificate_of_positiveWeights_of_localRawBitStringCombinatorialStepRule
    (hlocal : LocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    ModelCertificate T :=
  (completeFormalization_of_localRawBitStringCombinatorialStepRule
    hlocal).modelCertificate hT

theorem positiveLocalRawBitStringRule_of_positiveLocalSignedSumRule
    (hlocal : PositiveLocalSignedSumCombinatorialStepRule) :
    PositiveLocalRawBitStringCombinatorialStepRule := by
  intro a cs hT n _
  have hrawSigned :
      rawBitStringSignedSum n (RTree.node a cs) =
        RawNormal.signedSum n (RTree.node a cs) :=
    rawBitStringSignedSum_eq_signedSum_of_positiveWeights
      (n := n) (T := RTree.node a cs) hT
  exact hrawSigned.trans (hlocal hT n)

theorem positiveLocalSignedSumRule_of_positiveLocalRawBitStringRule
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule) :
    PositiveLocalSignedSumCombinatorialStepRule := by
  intro a cs hT n _
  have hrawSigned :
      rawBitStringSignedSum n (RTree.node a cs) =
        RawNormal.signedSum n (RTree.node a cs) :=
    rawBitStringSignedSum_eq_signedSum_of_positiveWeights
      (n := n) (T := RTree.node a cs) hT
  exact hrawSigned.symm.trans (hlocal hT n)

theorem positiveLocalSignedSumRule_iff_positiveLocalRawBitStringRule :
    PositiveLocalSignedSumCombinatorialStepRule ↔
      PositiveLocalRawBitStringCombinatorialStepRule :=
  ⟨positiveLocalRawBitStringRule_of_positiveLocalSignedSumRule,
    positiveLocalSignedSumRule_of_positiveLocalRawBitStringRule⟩

theorem positiveLocalRawBitStringRule_iff_positiveLocalSignedSumRule :
    PositiveLocalRawBitStringCombinatorialStepRule ↔
      PositiveLocalSignedSumCombinatorialStepRule :=
  positiveLocalSignedSumRule_iff_positiveLocalRawBitStringRule.symm

theorem positiveLocalRawBitStringCombinatorialStepRule_of_globalRawBitStringClosedXassign
    (hglobal : GlobalRawBitStringClosedXassign) :
    PositiveLocalRawBitStringCombinatorialStepRule := by
  intro a cs hT n _
  have hraw := hglobal (T := RTree.node a cs) hT n
  rw [localCombinatorialNodeExponent_eq_Xassign_of_positiveWeights
    (n := n) hT]
  exact hraw

theorem globalRawBitStringClosedXassign_of_positiveLocalRawBitStringCombinatorialStepRule
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule) :
    GlobalRawBitStringClosedXassign := by
  intro T hT n _
  cases T with
  | node a cs =>
      have hraw := hlocal hT n
      rwa [localCombinatorialNodeExponent_eq_Xassign_of_positiveWeights
        (n := n) hT] at hraw

theorem positiveLocalRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedXassign :
    PositiveLocalRawBitStringCombinatorialStepRule ↔
      GlobalRawBitStringClosedXassign :=
  ⟨globalRawBitStringClosedXassign_of_positiveLocalRawBitStringCombinatorialStepRule,
    positiveLocalRawBitStringCombinatorialStepRule_of_globalRawBitStringClosedXassign⟩

theorem positiveLocalRawBitStringCombinatorialStepRule_iff_forall_rawBitString_closed_Xassign :
    PositiveLocalRawBitStringCombinatorialStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xassign n T)) :=
  positiveLocalRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedXassign

theorem positiveLocalRawBitStringCombinatorialStepRule_iff_forall_rawBitString_closed_Xpoly :
    PositiveLocalRawBitStringCombinatorialStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xpoly n T)) :=
  positiveLocalRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedXassign.trans
    globalRawBitStringClosedXassign_iff_globalRawBitStringClosedXpoly

theorem positiveLocalRawBitStringRule_iff_forall_raw_closed_connected_terms :
    PositiveLocalRawBitStringCombinatorialStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))) :=
  positiveLocalRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedXassign.trans
    globalRawBitStringClosedXassign_iff_globalRawBitStringClosedConnectedTerms

theorem positiveLocalRawBitStringCombinatorialStepRule_iff_forall_rawBitString_eq_DeltaTreeModel :
    PositiveLocalRawBitStringCombinatorialStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T = DeltaTreeModel n T) := by
  exact
    positiveLocalRawBitStringCombinatorialStepRule_iff_globalRawBitStringClosedXassign.trans
      (openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXassign.symm.trans
        openRootRawBitStringNodeStepRule_iff_forall_rawBitString_eq_DeltaTreeModel)

theorem rawBitStringSignedSum_closed_assignmentFactorProduct_of_positiveLocal
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule)
    {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) := by
  have hT : RTree.PositiveWeights (RTree.node a cs) := by
    have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
      ⟨ha, hchildren⟩
    simpa [RTree.PositiveWeights] using hnode
  have hraw := hlocal hT n
  rw [localCombinatorialNodeExponent_eq_assignmentFactorProduct
    (n := n) (a := a) (cs := cs) hchildren] at hraw
  exact hraw

def PositiveAssignmentFactorProductNodeRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RTree.PositiveWeights C) →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n (RTree.node a cs) =
        (2 : ℤ) ^ Int.toNat
          ((((cs.map (fun C =>
            Int.toNat
              ((nZ n) ^ RTree.totalWeight C -
                (tZ n) * Yassign n C))).prod : Nat) : ℤ) +
            childContribSumWith (Xassign n) n a cs 0)

theorem positiveLocalRawBitStringCombinatorialStepRule_iff_assignmentFactorProduct_node :
    PositiveLocalRawBitStringCombinatorialStepRule ↔
      PositiveAssignmentFactorProductNodeRule := by
  constructor
  · intro hlocal a cs ha hchildren n _
    exact
      rawBitStringSignedSum_closed_assignmentFactorProduct_of_positiveLocal
        hlocal ha hchildren n
  · intro hfactor a cs hT n _
    have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
      simpa [RTree.PositiveWeights] using hT
    have hraw := hfactor hnode.1 hnode.2 n
    rw [localCombinatorialNodeExponent_eq_assignmentFactorProduct
      (n := n) (a := a) (cs := cs) hnode.2]
    exact hraw

theorem rawBitStringSignedSum_closed_Xassign_of_positiveLocalRawBitStringCombinatorialStepRule
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xassign n T) :=
  (positiveLocalRawBitStringCombinatorialStepRule_iff_forall_rawBitString_closed_Xassign.1
    hlocal) hT n

theorem rawBitStringSignedSum_closed_Xpoly_of_positiveLocalRawBitStringCombinatorialStepRule
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  (positiveLocalRawBitStringCombinatorialStepRule_iff_forall_rawBitString_closed_Xpoly.1
    hlocal) hT n

theorem rawBitStringSignedSum_closed_connected_terms_of_positiveLocal
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  (positiveLocalRawBitStringRule_iff_forall_raw_closed_connected_terms.1
    hlocal) hT n

theorem rawBitStringSignedSum_eq_DeltaTreeModel_of_positiveLocalRawBitStringCombinatorialStepRule
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = DeltaTreeModel n T :=
  (positiveLocalRawBitStringCombinatorialStepRule_iff_forall_rawBitString_eq_DeltaTreeModel.1
    hlocal) hT n

theorem normalFormSignedSum_closed_connected_terms_of_positiveLocalRawBitStringCombinatorialStepRule
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  change rawBitStringSignedSum n T =
    (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))
  exact
    rawBitStringSignedSum_closed_connected_terms_of_positiveLocal
      hlocal hT n

theorem positiveLocalRawBitStringDeltaStepRule_of_combinatorial
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule) :
    PositiveLocalRawBitStringDeltaStepRule := by
  intro a cs hT n _
  have hraw := hlocal hT n
  have hdelta :=
    DeltaTreeModel_node_eq_localCombinatorialNodeExponent_of_positiveWeights
      (n := n) hT
  exact hraw.trans hdelta.symm

theorem positiveLocalRawBitStringCombinatorialStepRule_of_delta
    (hlocal : PositiveLocalRawBitStringDeltaStepRule) :
    PositiveLocalRawBitStringCombinatorialStepRule := by
  intro a cs hT n _
  have hraw := hlocal hT n
  have hdelta :=
    DeltaTreeModel_node_eq_localCombinatorialNodeExponent_of_positiveWeights
      (n := n) hT
  exact hraw.trans hdelta

theorem positiveLocalRawBitStringCombinatorialStepRule_iff_delta :
    PositiveLocalRawBitStringCombinatorialStepRule ↔
      PositiveLocalRawBitStringDeltaStepRule :=
  ⟨positiveLocalRawBitStringDeltaStepRule_of_combinatorial,
    positiveLocalRawBitStringCombinatorialStepRule_of_delta⟩

theorem positiveLocalRawBitStringDeltaStepRule_iff_combinatorial :
    PositiveLocalRawBitStringDeltaStepRule ↔
      PositiveLocalRawBitStringCombinatorialStepRule :=
  positiveLocalRawBitStringCombinatorialStepRule_iff_delta.symm

theorem positiveLocalRawBitStringDeltaStepRule_of_signedDelta
    (hlocal : PositiveLocalSignedSumDeltaStepRule) :
    PositiveLocalRawBitStringDeltaStepRule := by
  intro a cs hT n _
  have hrawSigned :
      rawBitStringSignedSum n (RTree.node a cs) =
        RawNormal.signedSum n (RTree.node a cs) :=
    rawBitStringSignedSum_eq_signedSum_of_positiveWeights
      (n := n) (T := RTree.node a cs) hT
  exact hrawSigned.trans (hlocal hT n)

theorem positiveLocalSignedSumDeltaStepRule_of_rawDelta
    (hlocal : PositiveLocalRawBitStringDeltaStepRule) :
    PositiveLocalSignedSumDeltaStepRule := by
  intro a cs hT n _
  have hrawSigned :
      rawBitStringSignedSum n (RTree.node a cs) =
        RawNormal.signedSum n (RTree.node a cs) :=
    rawBitStringSignedSum_eq_signedSum_of_positiveWeights
      (n := n) (T := RTree.node a cs) hT
  exact hrawSigned.symm.trans (hlocal hT n)

theorem positiveLocalSignedSumDeltaStepRule_iff_rawDelta :
    PositiveLocalSignedSumDeltaStepRule ↔
      PositiveLocalRawBitStringDeltaStepRule :=
  ⟨positiveLocalRawBitStringDeltaStepRule_of_signedDelta,
    positiveLocalSignedSumDeltaStepRule_of_rawDelta⟩

theorem positiveLocalRawBitStringDeltaStepRule_iff_signedDelta :
    PositiveLocalRawBitStringDeltaStepRule ↔
      PositiveLocalSignedSumDeltaStepRule :=
  positiveLocalSignedSumDeltaStepRule_iff_rawDelta.symm

theorem positiveLocalModelCertificateStepRule_of_signedDelta
    (hlocal : PositiveLocalSignedSumDeltaStepRule) :
    PositiveLocalModelCertificateStepRule := by
  intro a cs hT
  refine
    { positiveWeights := hT
      signedSum_eq_DeltaTreeModel := ?_ }
  intro n _
  exact hlocal hT n

theorem positiveLocalSignedSumDeltaStepRule_of_modelCertificate
    (hlocal : PositiveLocalModelCertificateStepRule) :
    PositiveLocalSignedSumDeltaStepRule := by
  intro a cs hT n _
  exact (hlocal hT).signedSum_eq_DeltaTreeModel n

theorem positiveLocalSignedSumDeltaStepRule_iff_modelCertificate :
    PositiveLocalSignedSumDeltaStepRule ↔
      PositiveLocalModelCertificateStepRule :=
  ⟨positiveLocalModelCertificateStepRule_of_signedDelta,
    positiveLocalSignedSumDeltaStepRule_of_modelCertificate⟩

theorem positiveLocalModelCertificateStepRule_iff_signedDelta :
    PositiveLocalModelCertificateStepRule ↔
      PositiveLocalSignedSumDeltaStepRule :=
  positiveLocalSignedSumDeltaStepRule_iff_modelCertificate.symm

theorem positiveLocalModelCertificateStepRule_iff_forall_modelCertificate :
    PositiveLocalModelCertificateStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T → ModelCertificate T) := by
  constructor
  · intro hlocal T hT
    cases T with
    | node a cs =>
        exact hlocal hT
  · intro hglobal a cs hT
    exact hglobal hT

theorem globalSignedSumClosedDeltaTreeModel_of_positiveLocalSignedSumDeltaStepRule
    (hlocal : PositiveLocalSignedSumDeltaStepRule) :
    GlobalSignedSumClosedDeltaTreeModel := by
  intro T hT n _
  cases T with
  | node a cs =>
      exact hlocal hT n

theorem positiveLocalSignedSumDeltaStepRule_of_globalSignedSumClosedDeltaTreeModel
    (hglobal : GlobalSignedSumClosedDeltaTreeModel) :
    PositiveLocalSignedSumDeltaStepRule := by
  intro a cs hT n _
  exact hglobal (T := RTree.node a cs) hT n

theorem positiveLocalSignedSumDeltaStepRule_iff_globalSignedSumClosedDeltaTreeModel :
    PositiveLocalSignedSumDeltaStepRule ↔
      GlobalSignedSumClosedDeltaTreeModel :=
  ⟨globalSignedSumClosedDeltaTreeModel_of_positiveLocalSignedSumDeltaStepRule,
    positiveLocalSignedSumDeltaStepRule_of_globalSignedSumClosedDeltaTreeModel⟩

theorem globalSignedSumClosedDeltaTreeModel_iff_positiveLocalSignedSumDeltaStepRule :
    GlobalSignedSumClosedDeltaTreeModel ↔
      PositiveLocalSignedSumDeltaStepRule :=
  positiveLocalSignedSumDeltaStepRule_iff_globalSignedSumClosedDeltaTreeModel.symm

theorem positiveLocalRawBitStringDeltaStepRule_iff_globalSignedSumClosedDeltaTreeModel :
    PositiveLocalRawBitStringDeltaStepRule ↔
      GlobalSignedSumClosedDeltaTreeModel :=
  positiveLocalRawBitStringDeltaStepRule_iff_signedDelta.trans
    positiveLocalSignedSumDeltaStepRule_iff_globalSignedSumClosedDeltaTreeModel

theorem globalSignedSumClosedDeltaTreeModel_iff_positiveLocalRawBitStringDeltaStepRule :
    GlobalSignedSumClosedDeltaTreeModel ↔
      PositiveLocalRawBitStringDeltaStepRule :=
  positiveLocalRawBitStringDeltaStepRule_iff_globalSignedSumClosedDeltaTreeModel.symm

theorem positiveLocalSignedSumDeltaStepRule_iff_globalSignedSumRealizesAssignmentExponent :
    PositiveLocalSignedSumDeltaStepRule ↔
      GlobalSignedSumRealizesAssignmentExponent :=
  positiveLocalSignedSumDeltaStepRule_iff_globalSignedSumClosedDeltaTreeModel.trans
    globalSignedSumClosedDeltaTreeModel_iff_globalSignedSumRealizesAssignmentExponent

theorem positiveLocalRawBitStringDeltaStepRule_iff_globalSignedSumRealizesAssignmentExponent :
    PositiveLocalRawBitStringDeltaStepRule ↔
      GlobalSignedSumRealizesAssignmentExponent :=
  positiveLocalRawBitStringDeltaStepRule_iff_signedDelta.trans
    positiveLocalSignedSumDeltaStepRule_iff_globalSignedSumRealizesAssignmentExponent

theorem completeFormalization_of_positiveLocalRawBitStringCombinatorialStepRule
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule) :
    CompleteFormalization :=
  completeFormalization_of_globalRawBitStringClosedXassign
    (globalRawBitStringClosedXassign_of_positiveLocalRawBitStringCombinatorialStepRule
      hlocal)

theorem completeFormalization_iff_positiveLocalRawBitStringCombinatorialStepRule :
    CompleteFormalization ↔ PositiveLocalRawBitStringCombinatorialStepRule := by
  constructor
  · intro h
    exact
      positiveLocalRawBitStringCombinatorialStepRule_of_globalRawBitStringClosedXassign
        h.globalRawBitStringClosedXassign
  · exact completeFormalization_of_positiveLocalRawBitStringCombinatorialStepRule

theorem positiveLocalRawBitStringCombinatorialStepRule_iff_completeFormalization :
    PositiveLocalRawBitStringCombinatorialStepRule ↔ CompleteFormalization :=
  completeFormalization_iff_positiveLocalRawBitStringCombinatorialStepRule.symm

theorem completeFormalization_iff_assignmentFactorProductNodeRule :
    CompleteFormalization ↔ PositiveAssignmentFactorProductNodeRule :=
  completeFormalization_iff_positiveLocalRawBitStringCombinatorialStepRule.trans
    positiveLocalRawBitStringCombinatorialStepRule_iff_assignmentFactorProduct_node

theorem assignmentFactorProductNodeRule_iff_completeFormalization :
    PositiveAssignmentFactorProductNodeRule ↔ CompleteFormalization :=
  completeFormalization_iff_assignmentFactorProductNodeRule.symm

theorem rawBitStringSignedSum_closed_assignmentFactorProduct_of_completeFormalization
    (h : CompleteFormalization)
    {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) :=
  (completeFormalization_iff_assignmentFactorProductNodeRule.1 h)
    ha hchildren n

theorem rawBitStringSignedSum_closed_assignmentFactorProductExponent_of_completeFormalization
    (h : CompleteFormalization)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T) :=
  h.globalRawBitStringClosedAssignmentFactorProduct hT n

theorem signedSum_closed_assignmentFactorProductExponent_of_completeFormalization
    (h : CompleteFormalization)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    RawNormal.signedSum n T =
      (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T) :=
  h.globalSignedSumClosedAssignmentFactorProduct hT n

theorem normalFormSignedSum_closed_assignmentFactorProductExponent_of_completeFormalization
    (h : CompleteFormalization)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T) := by
  change rawBitStringSignedSum n T =
    (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T)
  exact
    rawBitStringSignedSum_closed_assignmentFactorProductExponent_of_completeFormalization
      h hT n

theorem subtreeModelCertificate_of_positiveWeights_of_positiveLocalRawBitStringCombinatorialStepRule
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    SubtreeModelCertificate T :=
  (completeFormalization_of_positiveLocalRawBitStringCombinatorialStepRule
    hlocal).subtreeModelCertificate hT

theorem modelCertificate_of_positiveWeights_of_positiveLocalRawBitStringCombinatorialStepRule
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    ModelCertificate T :=
  (completeFormalization_of_positiveLocalRawBitStringCombinatorialStepRule
    hlocal).modelCertificate hT

theorem completeFormalization_of_positiveLocalRawBitStringDeltaStepRule
    (hlocal : PositiveLocalRawBitStringDeltaStepRule) :
    CompleteFormalization :=
  completeFormalization_of_positiveLocalRawBitStringCombinatorialStepRule
    (positiveLocalRawBitStringCombinatorialStepRule_of_delta hlocal)

theorem completeFormalization_iff_positiveLocalRawBitStringDeltaStepRule :
    CompleteFormalization ↔ PositiveLocalRawBitStringDeltaStepRule :=
  completeFormalization_iff_positiveLocalRawBitStringCombinatorialStepRule.trans
    positiveLocalRawBitStringCombinatorialStepRule_iff_delta

theorem positiveLocalRawBitStringDeltaStepRule_iff_completeFormalization :
    PositiveLocalRawBitStringDeltaStepRule ↔ CompleteFormalization :=
  completeFormalization_iff_positiveLocalRawBitStringDeltaStepRule.symm

theorem completeFormalization_of_positiveLocalSignedSumDeltaStepRule
    (hlocal : PositiveLocalSignedSumDeltaStepRule) :
    CompleteFormalization :=
  completeFormalization_of_positiveLocalRawBitStringDeltaStepRule
    (positiveLocalRawBitStringDeltaStepRule_of_signedDelta hlocal)

theorem completeFormalization_iff_positiveLocalSignedSumDeltaStepRule :
    CompleteFormalization ↔ PositiveLocalSignedSumDeltaStepRule :=
  completeFormalization_iff_positiveLocalRawBitStringDeltaStepRule.trans
    positiveLocalRawBitStringDeltaStepRule_iff_signedDelta

theorem positiveLocalSignedSumDeltaStepRule_iff_completeFormalization :
    PositiveLocalSignedSumDeltaStepRule ↔ CompleteFormalization :=
  completeFormalization_iff_positiveLocalSignedSumDeltaStepRule.symm

theorem completeFormalization_of_positiveLocalModelCertificateStepRule
    (hlocal : PositiveLocalModelCertificateStepRule) :
    CompleteFormalization :=
  completeFormalization_of_positiveLocalSignedSumDeltaStepRule
    (positiveLocalSignedSumDeltaStepRule_of_modelCertificate hlocal)

theorem completeFormalization_iff_positiveLocalModelCertificateStepRule :
    CompleteFormalization ↔ PositiveLocalModelCertificateStepRule :=
  completeFormalization_iff_positiveLocalSignedSumDeltaStepRule.trans
    positiveLocalSignedSumDeltaStepRule_iff_modelCertificate

theorem positiveLocalModelCertificateStepRule_iff_completeFormalization :
    PositiveLocalModelCertificateStepRule ↔ CompleteFormalization :=
  completeFormalization_iff_positiveLocalModelCertificateStepRule.symm

theorem positiveAssignmentRecursionWitness_of_positiveLocalRawBitStringCombinatorialStepRule
    (hlocal : PositiveLocalRawBitStringCombinatorialStepRule) :
    PositiveAssignmentRecursionWitness :=
  completeFormalization_iff_positiveAssignmentRecursionWitness.1
    (completeFormalization_of_positiveLocalRawBitStringCombinatorialStepRule
      hlocal)

theorem positiveLocalRawBitStringCombinatorialStepRule_of_positiveAssignmentRecursionWitness
    (hwitness : PositiveAssignmentRecursionWitness) :
    PositiveLocalRawBitStringCombinatorialStepRule :=
  completeFormalization_iff_positiveLocalRawBitStringCombinatorialStepRule.1
    (completeFormalization_of_positiveAssignmentRecursionWitness hwitness)

theorem positiveAssignmentRecursionWitness_iff_positiveLocalRawBitStringCombinatorialStepRule :
    PositiveAssignmentRecursionWitness ↔
      PositiveLocalRawBitStringCombinatorialStepRule :=
  ⟨positiveLocalRawBitStringCombinatorialStepRule_of_positiveAssignmentRecursionWitness,
    positiveAssignmentRecursionWitness_of_positiveLocalRawBitStringCombinatorialStepRule⟩

theorem positiveLocalRawBitStringCombinatorialStepRule_iff_positiveAssignmentRecursionWitness :
    PositiveLocalRawBitStringCombinatorialStepRule ↔
      PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_iff_positiveLocalRawBitStringCombinatorialStepRule.symm

theorem positiveAssignmentRecursionWitness_iff_assignmentFactorProductNodeRule :
    PositiveAssignmentRecursionWitness ↔ PositiveAssignmentFactorProductNodeRule :=
  positiveAssignmentRecursionWitness_iff_positiveLocalRawBitStringCombinatorialStepRule.trans
    positiveLocalRawBitStringCombinatorialStepRule_iff_assignmentFactorProduct_node

theorem assignmentFactorProductNodeRule_iff_positiveAssignmentRecursionWitness :
    PositiveAssignmentFactorProductNodeRule ↔ PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_iff_assignmentFactorProductNodeRule.symm

theorem positiveAssignmentRecursionWitness_iff_globalRawBitStringClosedAssignmentFactorProduct :
    PositiveAssignmentRecursionWitness ↔
      GlobalRawBitStringClosedAssignmentFactorProduct :=
  positiveAssignmentRecursionWitness_iff_completeFormalization.trans
    completeFormalization_iff_globalRawBitStringClosedAssignmentFactorProduct

theorem globalRawBitStringClosedAssignmentFactorProduct_iff_positiveAssignmentRecursionWitness :
    GlobalRawBitStringClosedAssignmentFactorProduct ↔
      PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_iff_globalRawBitStringClosedAssignmentFactorProduct.symm

theorem positiveAssignmentRecursionWitness_iff_globalSignedSumClosedAssignmentFactorProduct :
    PositiveAssignmentRecursionWitness ↔
      GlobalSignedSumClosedAssignmentFactorProduct :=
  positiveAssignmentRecursionWitness_iff_completeFormalization.trans
    completeFormalization_iff_globalSignedSumClosedAssignmentFactorProduct

theorem globalSignedSumClosedAssignmentFactorProduct_iff_positiveAssignmentRecursionWitness :
    GlobalSignedSumClosedAssignmentFactorProduct ↔
      PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_iff_globalSignedSumClosedAssignmentFactorProduct.symm

theorem rawBitStringSignedSum_closed_assignmentFactorProduct_of_recursionWitness
    (hwitness : PositiveAssignmentRecursionWitness)
    {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) :=
  (positiveAssignmentRecursionWitness_iff_assignmentFactorProductNodeRule.1
    hwitness) ha hchildren n

theorem rawBitStringSignedSum_closed_assignmentFactorProductExponent_of_recursionWitness
    (hwitness : PositiveAssignmentRecursionWitness)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T) :=
  (positiveAssignmentRecursionWitness_iff_globalRawBitStringClosedAssignmentFactorProduct.1
    hwitness) hT n

theorem signedSum_closed_assignmentFactorProductExponent_of_recursionWitness
    (hwitness : PositiveAssignmentRecursionWitness)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    RawNormal.signedSum n T =
      (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T) :=
  (positiveAssignmentRecursionWitness_iff_globalSignedSumClosedAssignmentFactorProduct.1
    hwitness) hT n

theorem normalFormSignedSum_closed_assignmentFactorProductExponent_of_recursionWitness
    (hwitness : PositiveAssignmentRecursionWitness)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T) := by
  change rawBitStringSignedSum n T =
    (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T)
  exact
    rawBitStringSignedSum_closed_assignmentFactorProductExponent_of_recursionWitness
      hwitness hT n

theorem positiveAssignmentRecursionWitness_iff_positiveLocalSignedSumCombinatorialStepRule :
    PositiveAssignmentRecursionWitness ↔
      PositiveLocalSignedSumCombinatorialStepRule :=
  positiveAssignmentRecursionWitness_iff_positiveLocalRawBitStringCombinatorialStepRule.trans
    positiveLocalRawBitStringRule_iff_positiveLocalSignedSumRule

theorem positiveLocalSignedSumCombinatorialStepRule_iff_positiveAssignmentRecursionWitness :
    PositiveLocalSignedSumCombinatorialStepRule ↔
      PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_iff_positiveLocalSignedSumCombinatorialStepRule.symm

theorem positiveAssignmentRecursionWitness_iff_positiveLocalRawBitStringDeltaStepRule :
    PositiveAssignmentRecursionWitness ↔ PositiveLocalRawBitStringDeltaStepRule :=
  positiveAssignmentRecursionWitness_iff_positiveLocalRawBitStringCombinatorialStepRule.trans
    positiveLocalRawBitStringCombinatorialStepRule_iff_delta

theorem positiveLocalRawBitStringDeltaStepRule_iff_positiveAssignmentRecursionWitness :
    PositiveLocalRawBitStringDeltaStepRule ↔ PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_iff_positiveLocalRawBitStringDeltaStepRule.symm

theorem positiveAssignmentRecursionWitness_iff_positiveLocalSignedSumDeltaStepRule :
    PositiveAssignmentRecursionWitness ↔ PositiveLocalSignedSumDeltaStepRule :=
  positiveAssignmentRecursionWitness_iff_positiveLocalRawBitStringDeltaStepRule.trans
    positiveLocalRawBitStringDeltaStepRule_iff_signedDelta

theorem positiveLocalSignedSumDeltaStepRule_iff_positiveAssignmentRecursionWitness :
    PositiveLocalSignedSumDeltaStepRule ↔ PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_iff_positiveLocalSignedSumDeltaStepRule.symm

theorem positiveAssignmentRecursionWitness_iff_positiveLocalModelCertificateStepRule :
    PositiveAssignmentRecursionWitness ↔ PositiveLocalModelCertificateStepRule :=
  positiveAssignmentRecursionWitness_iff_positiveLocalSignedSumDeltaStepRule.trans
    positiveLocalSignedSumDeltaStepRule_iff_modelCertificate

theorem positiveLocalModelCertificateStepRule_iff_positiveAssignmentRecursionWitness :
    PositiveLocalModelCertificateStepRule ↔ PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_iff_positiveLocalModelCertificateStepRule.symm

theorem localRawBitStringCombinatorialStepRule_iff_positiveLocalRawBitStringCombinatorialStepRule :
    LocalRawBitStringCombinatorialStepRule ↔
      PositiveLocalRawBitStringCombinatorialStepRule :=
  localRawBitStringCombinatorialStepRule_iff_completeFormalization.trans
    completeFormalization_iff_positiveLocalRawBitStringCombinatorialStepRule

theorem positiveLocalRawBitStringCombinatorialStepRule_iff_localRawBitStringCombinatorialStepRule :
    PositiveLocalRawBitStringCombinatorialStepRule ↔
      LocalRawBitStringCombinatorialStepRule :=
  localRawBitStringCombinatorialStepRule_iff_positiveLocalRawBitStringCombinatorialStepRule.symm

theorem localRawBitStringDeltaStepRule_iff_positiveLocalRawBitStringDeltaStepRule :
    LocalRawBitStringDeltaStepRule ↔
      PositiveLocalRawBitStringDeltaStepRule :=
  localRawBitStringDeltaStepRule_iff_completeFormalization.trans
    completeFormalization_iff_positiveLocalRawBitStringDeltaStepRule

theorem positiveLocalRawBitStringDeltaStepRule_iff_localRawBitStringDeltaStepRule :
    PositiveLocalRawBitStringDeltaStepRule ↔
      LocalRawBitStringDeltaStepRule :=
  localRawBitStringDeltaStepRule_iff_positiveLocalRawBitStringDeltaStepRule.symm

end RawPrimitive

end TreeGraph
