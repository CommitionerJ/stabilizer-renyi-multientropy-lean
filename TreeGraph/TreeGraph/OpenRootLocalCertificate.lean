import TreeGraph.OpenRootFinal

namespace TreeGraph

namespace RawPrimitive

def LocalModelCertificateStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, SubtreeModelCertificate C) →
    ModelCertificate (RTree.node a cs)

def LocalRawBitStringDeltaStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, SubtreeModelCertificate C) →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n (RTree.node a cs) =
        DeltaTreeModel n (RTree.node a cs)

theorem openRootRawBitStringNodeStep_of_modelCertificate
    {a : Nat} {cs : List RTree}
    (hnode : ModelCertificate (RTree.node a cs))
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat (openRootNodeExponent n a cs) := by
  have hraw :
      rawBitStringSignedSum n (RTree.node a cs) =
        DeltaTreeModel n (RTree.node a cs) :=
    ModelCertificate.rawBitStringSignedSum_eq_DeltaTreeModel hnode n
  exact hraw.trans
    (DeltaTreeModel_node_eq_openRootNodeExponent_of_children
      (n := n) ha hchildren)

theorem modelCertificate_of_openRootRawBitStringNodeStep
    {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C)
    (hopen :
      ∀ (n : Nat) [NeZero n],
        rawBitStringSignedSum n (RTree.node a cs) =
          (2 : ℤ) ^ Int.toNat (openRootNodeExponent n a cs)) :
    ModelCertificate (RTree.node a cs) where
  positiveWeights := by
    have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
      intro C hC
      exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
    have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
      ⟨ha, hchildPos⟩
    simpa [RTree.PositiveWeights] using hnode
  signedSum_eq_DeltaTreeModel := by
    intro n _
    have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
      intro C hC
      exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
    have hpos : RTree.PositiveWeights (RTree.node a cs) := by
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
        ⟨ha, hchildPos⟩
      simpa [RTree.PositiveWeights] using hnode
    have htoSigned :
        rawBitStringSignedSum n (RTree.node a cs) =
          RawNormal.signedSum n (RTree.node a cs) :=
      rawBitStringSignedSum_eq_signedSum_of_positiveWeights
        (n := n) (T := RTree.node a cs) hpos
    have hdelta :=
      DeltaTreeModel_node_eq_openRootNodeExponent_of_children
        (n := n) ha hchildren
    exact htoSigned.symm.trans ((hopen n).trans hdelta.symm)

theorem openRootRawBitStringNodeStepRule_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule) :
    OpenRootRawBitStringNodeStepRule := by
  intro a cs ha hchildren n _
  exact openRootRawBitStringNodeStep_of_modelCertificate
    (hlocal ha hchildren) ha hchildren n

theorem localModelCertificateStepRule_of_openRootRawBitStringNodeStepRule
    (hopen : OpenRootRawBitStringNodeStepRule) :
    LocalModelCertificateStepRule := by
  intro a cs ha hchildren
  exact modelCertificate_of_openRootRawBitStringNodeStep
    ha hchildren (fun n => hopen ha hchildren n)

theorem localModelCertificateStepRule_iff_openRootRawBitStringNodeStepRule :
    LocalModelCertificateStepRule ↔ OpenRootRawBitStringNodeStepRule :=
  ⟨openRootRawBitStringNodeStepRule_of_localModelCertificateStepRule,
    localModelCertificateStepRule_of_openRootRawBitStringNodeStepRule⟩

theorem localRawBitStringDeltaStepRule_of_openRootRawBitStringNodeStepRule
    (hopen : OpenRootRawBitStringNodeStepRule) :
    LocalRawBitStringDeltaStepRule := by
  intro a cs ha hchildren n _
  have hraw := hopen ha hchildren n
  have hdelta :=
    DeltaTreeModel_node_eq_openRootNodeExponent_of_children
      (n := n) ha hchildren
  exact hraw.trans hdelta.symm

theorem openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule
    (hlocal : LocalRawBitStringDeltaStepRule) :
    OpenRootRawBitStringNodeStepRule := by
  intro a cs ha hchildren n _
  have hraw := hlocal ha hchildren n
  have hdelta :=
    DeltaTreeModel_node_eq_openRootNodeExponent_of_children
      (n := n) ha hchildren
  exact hraw.trans hdelta

theorem localRawBitStringDeltaStepRule_iff_openRootRawBitStringNodeStepRule :
    LocalRawBitStringDeltaStepRule ↔ OpenRootRawBitStringNodeStepRule :=
  ⟨openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule,
    localRawBitStringDeltaStepRule_of_openRootRawBitStringNodeStepRule⟩

theorem localModelCertificateStepRule_iff_globalRawBitStringClosedXassign :
    LocalModelCertificateStepRule ↔ GlobalRawBitStringClosedXassign :=
  Iff.trans localModelCertificateStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXassign

theorem localModelCertificateStepRule_iff_globalRawBitStringClosedXpoly :
    LocalModelCertificateStepRule ↔ GlobalRawBitStringClosedXpoly :=
  Iff.trans localModelCertificateStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXpoly

theorem localModelCertificateStepRule_iff_globalRawBitStringClosedConnectedTerms :
    LocalModelCertificateStepRule ↔ GlobalRawBitStringClosedConnectedTerms :=
  Iff.trans localModelCertificateStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedConnectedTerms

theorem localRawBitStringDeltaStepRule_iff_globalRawBitStringClosedXassign :
    LocalRawBitStringDeltaStepRule ↔ GlobalRawBitStringClosedXassign :=
  Iff.trans localRawBitStringDeltaStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXassign

theorem localRawBitStringDeltaStepRule_iff_globalRawBitStringClosedXpoly :
    LocalRawBitStringDeltaStepRule ↔ GlobalRawBitStringClosedXpoly :=
  Iff.trans localRawBitStringDeltaStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXpoly

theorem localRawBitStringDeltaStepRule_iff_globalRawBitStringClosedConnectedTerms :
    LocalRawBitStringDeltaStepRule ↔
      GlobalRawBitStringClosedConnectedTerms :=
  Iff.trans localRawBitStringDeltaStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedConnectedTerms

theorem localRawBitStringDeltaStepRule_iff_forall_rawBitString_closed_Xassign :
    LocalRawBitStringDeltaStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xassign n T)) :=
  Iff.trans localRawBitStringDeltaStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_forall_rawBitString_closed_Xassign

theorem localRawBitStringDeltaStepRule_iff_forall_rawBitString_closed_Xpoly :
    LocalRawBitStringDeltaStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xpoly n T)) :=
  Iff.trans localRawBitStringDeltaStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_forall_rawBitString_closed_Xpoly

theorem localRawBitStringDeltaStepRule_iff_forall_rawBitString_closed_connected_terms :
    LocalRawBitStringDeltaStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))) :=
  Iff.trans localRawBitStringDeltaStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_forall_rawBitString_closed_connected_terms

theorem localRawBitStringDeltaStepRule_iff_forall_rawBitString_eq_DeltaTreeModel :
    LocalRawBitStringDeltaStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T = DeltaTreeModel n T) :=
  Iff.trans localRawBitStringDeltaStepRule_iff_openRootRawBitStringNodeStepRule
    openRootRawBitStringNodeStepRule_iff_forall_rawBitString_eq_DeltaTreeModel

theorem rawBitStringSignedSum_closed_Xassign_of_localRawBitStringDeltaStepRule
    (hlocal : LocalRawBitStringDeltaStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xassign n T) :=
  rawBitStringSignedSum_closed_Xassign_of_openRootRawNodeStep
    (openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule
      hlocal) hT n

theorem rawBitStringSignedSum_closed_Xpoly_of_localRawBitStringDeltaStepRule
    (hlocal : LocalRawBitStringDeltaStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  rawBitStringSignedSum_closed_Xpoly_of_openRootRawNodeStep
    (openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule
      hlocal) hT n

theorem rawBitStringSignedSum_closed_connected_terms_of_localRawBitStringDeltaStepRule
    (hlocal : LocalRawBitStringDeltaStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  rawBitStringSignedSum_closed_connected_terms_of_openRootRawNodeStep
    (openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule
      hlocal) hT n

theorem rawBitStringSignedSum_eq_DeltaTreeModel_of_localRawBitStringDeltaStepRule
    (hlocal : LocalRawBitStringDeltaStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = DeltaTreeModel n T :=
  rawBitStringSignedSum_eq_DeltaTreeModel_of_openRootRawNodeStep
    (openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule
      hlocal) hT n

theorem normalFormSignedSum_closed_connected_terms_of_localRawBitStringDeltaStepRule
    (hlocal : LocalRawBitStringDeltaStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  normalFormSignedSum_closed_connected_terms_of_openRootRawNodeStep
    (openRootRawBitStringNodeStepRule_of_localRawBitStringDeltaStepRule
      hlocal) hT n

theorem nodeStepCertificate_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule)
    {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    NodeStepCertificate a cs where
  positiveRoot := ha
  children := hchildren
  signedSum_eq_DeltaTreeModel := by
    intro n _
    exact (hlocal ha hchildren).signedSum_eq_DeltaTreeModel n

theorem nodeStepCertificate_of_localRawBitStringDeltaStepRule
    (hlocal : LocalRawBitStringDeltaStepRule)
    {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    NodeStepCertificate a cs where
  positiveRoot := ha
  children := hchildren
  signedSum_eq_DeltaTreeModel := by
    intro n _
    have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
      intro C hC
      exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
    have hpos : RTree.PositiveWeights (RTree.node a cs) := by
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
        ⟨ha, hchildPos⟩
      simpa [RTree.PositiveWeights] using hnode
    have hraw := hlocal ha hchildren n
    have htoSigned :
        rawBitStringSignedSum n (RTree.node a cs) =
          RawNormal.signedSum n (RTree.node a cs) :=
      rawBitStringSignedSum_eq_signedSum_of_positiveWeights
        (n := n) (T := RTree.node a cs) hpos
    exact htoSigned.symm.trans hraw

theorem subtreeModelCertificate_of_positiveWeights_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    SubtreeModelCertificate T := by
  induction T using rootedTerms.induct with
  | case1 a cs ih =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      have hchildren : ∀ C ∈ cs, SubtreeModelCertificate C := by
        intro C hC
        exact ih C hC (hnode.2 C hC)
      exact subtreeModelCertificate_node_of_step
        (nodeStepCertificate_of_localModelCertificateStepRule
          hlocal hnode.1 hchildren)

theorem subtreeModelCertificate_of_positiveWeights_of_localRawBitStringDeltaStepRule
    (hlocal : LocalRawBitStringDeltaStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    SubtreeModelCertificate T := by
  induction T using rootedTerms.induct with
  | case1 a cs ih =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      have hchildren : ∀ C ∈ cs, SubtreeModelCertificate C := by
        intro C hC
        exact ih C hC (hnode.2 C hC)
      exact subtreeModelCertificate_node_of_step
        (nodeStepCertificate_of_localRawBitStringDeltaStepRule
          hlocal hnode.1 hchildren)

theorem modelCertificate_of_positiveWeights_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    ModelCertificate T :=
  SubtreeModelCertificate.root
    (subtreeModelCertificate_of_positiveWeights_of_localModelCertificateStepRule
      hlocal hT)

theorem modelCertificate_of_positiveWeights_of_localRawBitStringDeltaStepRule
    (hlocal : LocalRawBitStringDeltaStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    ModelCertificate T :=
  SubtreeModelCertificate.root
    (subtreeModelCertificate_of_positiveWeights_of_localRawBitStringDeltaStepRule
      hlocal hT)

theorem rawBitStringSignedSum_closed_Xassign_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xassign n T) :=
  rawBitStringSignedSum_closed_Xassign_of_openRootRawNodeStep
    (openRootRawBitStringNodeStepRule_of_localModelCertificateStepRule
      hlocal) hT n

theorem rawBitStringSignedSum_closed_Xpoly_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  rawBitStringSignedSum_closed_Xpoly_of_openRootRawNodeStep
    (openRootRawBitStringNodeStepRule_of_localModelCertificateStepRule
      hlocal) hT n

theorem rawBitStringSignedSum_closed_connected_terms_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  rawBitStringSignedSum_closed_connected_terms_of_openRootRawNodeStep
    (openRootRawBitStringNodeStepRule_of_localModelCertificateStepRule
      hlocal) hT n

theorem rawBitStringSignedSum_eq_DeltaTreeModel_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = DeltaTreeModel n T :=
  rawBitStringSignedSum_eq_DeltaTreeModel_of_openRootRawNodeStep
    (openRootRawBitStringNodeStepRule_of_localModelCertificateStepRule
      hlocal) hT n

theorem normalFormSignedSum_closed_connected_terms_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  normalFormSignedSum_closed_connected_terms_of_openRootRawNodeStep
    (openRootRawBitStringNodeStepRule_of_localModelCertificateStepRule
      hlocal) hT n

theorem rawBitStringSignedSum_closed_assignmentFactorProduct_of_modelCertificate
    {a n : Nat} {cs : List RTree} [NeZero n]
    (hnode : ModelCertificate (RTree.node a cs))
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) := by
  have hraw :=
    openRootRawBitStringNodeStep_of_modelCertificate
      hnode ha hchildren n
  rw [openRootNodeExponent_eq_assignmentFactorProduct_of_children
    (n := n) (a := a) (cs := cs) hchildren] at hraw
  exact hraw

theorem rawBitStringSignedSum_closed_assignmentFactorProduct_of_localModelCertificateStepRule
    (hlocal : LocalModelCertificateStepRule)
    {a n : Nat} {cs : List RTree} [NeZero n]
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) :=
  rawBitStringSignedSum_closed_assignmentFactorProduct_of_modelCertificate
    (hlocal ha hchildren) ha hchildren

theorem openRootRawBitStringNodeStep_leaf
    {a n : Nat} [NeZero n] (ha : 0 < a) :
    rawBitStringSignedSum n (RTree.node a []) =
      (2 : ℤ) ^ Int.toNat (openRootNodeExponent n a []) := by
  exact openRootRawBitStringNodeStep_of_modelCertificate
    (modelCertificate_leaf a ha) ha (by
      intro C hC
      cases hC) n

theorem openRootRawBitStringNodeStep_edge
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    rawBitStringSignedSum n (RTree.node a [RTree.node b []]) =
      (2 : ℤ) ^ Int.toNat
        (openRootNodeExponent n a [RTree.node b []]) := by
  exact openRootRawBitStringNodeStep_of_modelCertificate
    (modelCertificate_edge a b ha hb) ha (by
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rw [hC]
      exact subtreeModelCertificate_leaf b hb) n

theorem openRootRawBitStringNodeStep_star
    {a b c n : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    rawBitStringSignedSum n (StarTree a b c) =
      (2 : ℤ) ^ Int.toNat
        (openRootNodeExponent n a
          [RTree.node b [], RTree.node c []]) := by
  exact openRootRawBitStringNodeStep_of_modelCertificate
    (modelCertificate_star a b c ha hb hc) ha (by
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with hC | hC
      · rw [hC]
        exact subtreeModelCertificate_leaf b hb
      · rw [hC]
        exact subtreeModelCertificate_leaf c hc) n

theorem rawBitStringSignedSum_leaf_closed_assignmentFactorProduct
    {a n : Nat} [NeZero n] (ha : 0 < a) :
    rawBitStringSignedSum n (RTree.node a []) =
      (2 : ℤ) ^ Int.toNat
        ((((([] : List RTree).map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a [] 0) := by
  have hraw := openRootRawBitStringNodeStep_leaf (n := n) ha
  rw [openRootNodeExponent_eq_assignmentFactorProduct
    (n := n) (a := a) (cs := ([] : List RTree)) (by
      intro C hC
      cases hC)] at hraw
  exact hraw

theorem rawBitStringSignedSum_edge_closed_assignmentFactorProduct
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    rawBitStringSignedSum n (RTree.node a [RTree.node b []]) =
      (2 : ℤ) ^ Int.toNat
        ((((([RTree.node b []] : List RTree).map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a [RTree.node b []] 0) := by
  have hchildren :
      ∀ C ∈ ([RTree.node b []] : List RTree), RTree.PositiveWeights C := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rw [hC]
    exact SubtreeModelCertificate.positiveWeights
      (subtreeModelCertificate_leaf b hb)
  have hraw := openRootRawBitStringNodeStep_edge
    (n := n) ha hb
  rw [openRootNodeExponent_eq_assignmentFactorProduct
    (n := n) (a := a) (cs := [RTree.node b []]) hchildren] at hraw
  exact hraw

theorem rawBitStringSignedSum_star_closed_assignmentFactorProduct
    {a b c n : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    rawBitStringSignedSum n (StarTree a b c) =
      (2 : ℤ) ^ Int.toNat
        ((((([RTree.node b [], RTree.node c []] : List RTree).map
          (fun C =>
            Int.toNat
              ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a
            [RTree.node b [], RTree.node c []] 0) := by
  have hchildren :
      ∀ C ∈ ([RTree.node b [], RTree.node c []] : List RTree),
        RTree.PositiveWeights C := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with hC | hC
    · rw [hC]
      exact SubtreeModelCertificate.positiveWeights
        (subtreeModelCertificate_leaf b hb)
    · rw [hC]
      exact SubtreeModelCertificate.positiveWeights
        (subtreeModelCertificate_leaf c hc)
  have hraw := openRootRawBitStringNodeStep_star
    (n := n) ha hb hc
  rw [openRootNodeExponent_eq_assignmentFactorProduct
    (n := n) (a := a)
    (cs := [RTree.node b [], RTree.node c []]) hchildren] at hraw
  exact hraw

end RawPrimitive

end TreeGraph
