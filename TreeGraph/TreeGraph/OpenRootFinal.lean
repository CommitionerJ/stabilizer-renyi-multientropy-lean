import TreeGraph.OpenRootNode

namespace TreeGraph

namespace RawPrimitive

theorem openRootNodeExponent_eq_Xpoly_of_children
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    openRootNodeExponent n a cs = Xpoly n (RTree.node a cs) := by
  simpa [Xassign] using
    openRootNodeExponent_eq_Xassign_of_children
      (n := n) ha hchildren

theorem openRootNodeExponent_eq_connected_terms_of_children
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    openRootNodeExponent n a cs =
      termSum n (allTerms (RTree.node a cs)) := by
  rw [openRootNodeExponent_eq_Xpoly_of_children
    (n := n) ha hchildren]
  exact Xpoly_eq_allTerms n (RTree.node a cs)

theorem openRootRawBitStringNodeStepRule_of_globalRawBitStringClosedXassign
    (hglobal : GlobalRawBitStringClosedXassign) :
    OpenRootRawBitStringNodeStepRule :=
  openRootRawBitStringNodeStepRule_of_nodeStepRule
    ((nodeStepRule_iff_globalRawBitStringClosedXassign).2 hglobal)

theorem globalRawBitStringClosedXassign_of_openRootRawBitStringNodeStepRule
    (hopen : OpenRootRawBitStringNodeStepRule) :
    GlobalRawBitStringClosedXassign :=
  globalRawBitStringClosedXassign_of_globalSignedSumRealizesAssignmentExponent
    (globalSignedSumRealizesAssignmentExponent_of_nodeStepRule
      (nodeStepRule_of_openRootRawBitStringNodeStepRule hopen))

theorem openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXassign :
    OpenRootRawBitStringNodeStepRule ↔ GlobalRawBitStringClosedXassign :=
  ⟨globalRawBitStringClosedXassign_of_openRootRawBitStringNodeStepRule,
    openRootRawBitStringNodeStepRule_of_globalRawBitStringClosedXassign⟩

theorem openRootRawBitStringNodeStepRule_of_globalRawBitStringClosedXpoly
    (hglobal : GlobalRawBitStringClosedXpoly) :
    OpenRootRawBitStringNodeStepRule :=
  openRootRawBitStringNodeStepRule_of_nodeStepRule
    (nodeStepRule_of_globalRawBitStringClosedXpoly hglobal)

theorem globalRawBitStringClosedXpoly_of_openRootRawBitStringNodeStepRule
    (hopen : OpenRootRawBitStringNodeStepRule) :
    GlobalRawBitStringClosedXpoly :=
  globalRawBitStringClosedXpoly_of_globalRawBitStringClosedXassign
    (globalRawBitStringClosedXassign_of_openRootRawBitStringNodeStepRule
      hopen)

theorem openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXpoly :
    OpenRootRawBitStringNodeStepRule ↔ GlobalRawBitStringClosedXpoly :=
  ⟨globalRawBitStringClosedXpoly_of_openRootRawBitStringNodeStepRule,
    openRootRawBitStringNodeStepRule_of_globalRawBitStringClosedXpoly⟩

theorem openRootRawBitStringNodeStepRule_of_globalRawBitStringClosedConnectedTerms
    (hglobal : GlobalRawBitStringClosedConnectedTerms) :
    OpenRootRawBitStringNodeStepRule :=
  openRootRawBitStringNodeStepRule_of_nodeStepRule
    (nodeStepRule_of_globalRawBitStringClosedConnectedTerms hglobal)

theorem globalRawBitStringClosedConnectedTerms_of_openRootRawBitStringNodeStepRule
    (hopen : OpenRootRawBitStringNodeStepRule) :
    GlobalRawBitStringClosedConnectedTerms :=
  globalRawBitStringClosedConnectedTerms_of_globalRawBitStringClosedXassign
    (globalRawBitStringClosedXassign_of_openRootRawBitStringNodeStepRule
      hopen)

theorem openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedConnectedTerms :
    OpenRootRawBitStringNodeStepRule ↔
      GlobalRawBitStringClosedConnectedTerms :=
  ⟨globalRawBitStringClosedConnectedTerms_of_openRootRawBitStringNodeStepRule,
    openRootRawBitStringNodeStepRule_of_globalRawBitStringClosedConnectedTerms⟩

theorem openRootRawBitStringNodeStepRule_iff_forall_rawBitString_closed_Xassign :
    OpenRootRawBitStringNodeStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xassign n T)) :=
  openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXassign

theorem openRootRawBitStringNodeStepRule_iff_forall_rawBitString_closed_Xpoly :
    OpenRootRawBitStringNodeStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (Xpoly n T)) :=
  openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedXpoly

theorem openRootRawBitStringNodeStepRule_iff_forall_rawBitString_closed_connected_terms :
    OpenRootRawBitStringNodeStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T =
            (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))) :=
  openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedConnectedTerms

theorem openRootRawBitStringNodeStepRule_iff_forall_rawBitString_eq_DeltaTreeModel :
    OpenRootRawBitStringNodeStepRule ↔
      (∀ {T : RTree}, RTree.PositiveWeights T →
        ∀ (n : Nat) [NeZero n],
          rawBitStringSignedSum n T = DeltaTreeModel n T) := by
  constructor
  · intro hopen T hT n _
    simpa [DeltaTreeModel] using
      globalRawBitStringClosedXassign_of_openRootRawBitStringNodeStepRule
        hopen hT n
  · intro hglobal
    refine openRootRawBitStringNodeStepRule_of_nodeStepRule ?_
    intro a cs ha hchildren n _
    have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
      intro C hC
      exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
    have hpos : RTree.PositiveWeights (RTree.node a cs) := by
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
        ⟨ha, hchildPos⟩
      simpa [RTree.PositiveWeights] using hnode
    have hraw := hglobal (T := RTree.node a cs) hpos n
    have htoSigned :
        rawBitStringSignedSum n (RTree.node a cs) =
          RawNormal.signedSum n (RTree.node a cs) :=
      rawBitStringSignedSum_eq_signedSum_of_positiveWeights
        (n := n) (T := RTree.node a cs) hpos
    exact htoSigned.symm.trans hraw

theorem rawBitStringSignedSum_closed_Xassign_of_openRootRawNodeStep
    (hopen : OpenRootRawBitStringNodeStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xassign n T) :=
  globalRawBitStringClosedXassign_of_openRootRawBitStringNodeStepRule
    hopen hT n

theorem rawBitStringSignedSum_closed_assignmentFactorProduct_of_openRootRawNodeStep
    (hopen : OpenRootRawBitStringNodeStepRule)
    {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) := by
  have hraw :=
    rawBitStringSignedSum_closed_Xassign_of_openRootRawNodeStep
      hopen hT n
  have hX :=
    openRootNodeExponent_eq_Xassign_of_positiveWeights
      (n := n) hT
  have hprod :=
    openRootNodeExponent_eq_assignmentFactorProduct_of_positiveWeights
      (n := n) hT
  rw [← hX, hprod] at hraw
  exact hraw

def GlobalRawBitStringClosedAssignmentFactorProduct : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n T =
        (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T)

theorem globalRawBitStringClosedAssignmentFactorProduct_of_openRootRawBitStringNodeStepRule
    (hopen : OpenRootRawBitStringNodeStepRule) :
    GlobalRawBitStringClosedAssignmentFactorProduct := by
  intro T hT n _
  cases T with
  | node a cs =>
      simpa [assignmentFactorProductExponent] using
        rawBitStringSignedSum_closed_assignmentFactorProduct_of_openRootRawNodeStep
          hopen (a := a) (cs := cs) hT n

theorem openRootRawBitStringNodeStepRule_of_globalRawBitStringClosedAssignmentFactorProduct
    (hglobal : GlobalRawBitStringClosedAssignmentFactorProduct) :
    OpenRootRawBitStringNodeStepRule := by
  intro a cs ha hchildren n _
  have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
    intro C hC
    exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
  have hpos : RTree.PositiveWeights (RTree.node a cs) := by
    have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
      ⟨ha, hchildPos⟩
    simpa [RTree.PositiveWeights] using hnode
  have hraw := hglobal (T := RTree.node a cs) hpos n
  rw [← openRootNodeExponent_eq_assignmentFactorProductExponent_of_children
    (n := n) (a := a) (cs := cs) hchildren] at hraw
  exact hraw

theorem openRootRawBitStringNodeStepRule_iff_globalRawBitStringClosedAssignmentFactorProduct :
    OpenRootRawBitStringNodeStepRule ↔
      GlobalRawBitStringClosedAssignmentFactorProduct :=
  ⟨globalRawBitStringClosedAssignmentFactorProduct_of_openRootRawBitStringNodeStepRule,
    openRootRawBitStringNodeStepRule_of_globalRawBitStringClosedAssignmentFactorProduct⟩

def GlobalSignedSumClosedAssignmentFactorProduct : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n T =
        (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T)

theorem globalSignedAssignmentFactorProduct_of_globalRaw
    (hglobal : GlobalRawBitStringClosedAssignmentFactorProduct) :
    GlobalSignedSumClosedAssignmentFactorProduct := by
  intro T hT n _
  have hraw := hglobal hT n
  have htoSigned :
      rawBitStringSignedSum n T = RawNormal.signedSum n T :=
    rawBitStringSignedSum_eq_signedSum_of_positiveWeights
      (n := n) (T := T) hT
  exact htoSigned.symm.trans hraw

theorem globalRawAssignmentFactorProduct_of_globalSigned
    (hglobal : GlobalSignedSumClosedAssignmentFactorProduct) :
    GlobalRawBitStringClosedAssignmentFactorProduct := by
  intro T hT n _
  rw [rawBitStringSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := T) hT]
  exact hglobal hT n

theorem globalSignedAssignmentFactorProduct_iff_globalRaw :
    GlobalSignedSumClosedAssignmentFactorProduct ↔
      GlobalRawBitStringClosedAssignmentFactorProduct :=
  ⟨globalRawAssignmentFactorProduct_of_globalSigned,
    globalSignedAssignmentFactorProduct_of_globalRaw⟩

theorem globalRawAssignmentFactorProduct_iff_globalSigned :
    GlobalRawBitStringClosedAssignmentFactorProduct ↔
      GlobalSignedSumClosedAssignmentFactorProduct :=
  globalSignedAssignmentFactorProduct_iff_globalRaw.symm

theorem globalSignedAssignmentFactorProduct_of_openRootRawNodeStep
    (hopen : OpenRootRawBitStringNodeStepRule) :
    GlobalSignedSumClosedAssignmentFactorProduct :=
  globalSignedAssignmentFactorProduct_of_globalRaw
    (globalRawBitStringClosedAssignmentFactorProduct_of_openRootRawBitStringNodeStepRule
      hopen)

namespace ModelCertificate

theorem rawBitStringSignedSum_closed_assignmentFactorProduct_node
    {a n : Nat} {cs : List RTree} [NeZero n]
    (hnode : ModelCertificate (RTree.node a cs)) :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) := by
  have hraw :
      rawBitStringSignedSum n (RTree.node a cs) =
        (2 : ℤ) ^ Int.toNat (Xassign n (RTree.node a cs)) := by
    simpa [Xassign] using
      ModelCertificate.rawBitStringSignedSum_closed_Xpoly hnode n
  have hX :=
    openRootNodeExponent_eq_Xassign_of_positiveWeights
      (n := n) hnode.positiveWeights
  have hprod :=
    openRootNodeExponent_eq_assignmentFactorProduct_of_positiveWeights
      (n := n) hnode.positiveWeights
  rw [← hX, hprod] at hraw
  exact hraw

end ModelCertificate

namespace ModelCertificate

theorem rawBitStringSignedSum_closed_assignmentFactorProduct
    {T : RTree} (hnode : ModelCertificate T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T) := by
  cases T with
  | node a cs =>
      exact rawBitStringSignedSum_closed_assignmentFactorProduct_node hnode

end ModelCertificate

namespace SubtreeModelCertificate

theorem rawBitStringSignedSum_closed_assignmentFactorProduct_node
    {a n : Nat} {cs : List RTree} [NeZero n]
    (hnode : SubtreeModelCertificate (RTree.node a cs)) :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) :=
  ModelCertificate.rawBitStringSignedSum_closed_assignmentFactorProduct_node
    (SubtreeModelCertificate.root hnode)

end SubtreeModelCertificate

namespace SubtreeModelCertificate

theorem rawBitStringSignedSum_closed_assignmentFactorProduct
    {T : RTree} (hnode : SubtreeModelCertificate T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T) :=
  ModelCertificate.rawBitStringSignedSum_closed_assignmentFactorProduct
    (SubtreeModelCertificate.root hnode) n

end SubtreeModelCertificate

namespace NodeStepCertificate

theorem rawBitStringSignedSum_closed_assignmentFactorProduct
    {a n : Nat} {cs : List RTree} [NeZero n]
    (hnode : NodeStepCertificate a cs) :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) :=
  ModelCertificate.rawBitStringSignedSum_closed_assignmentFactorProduct_node
    hnode.modelCertificate

end NodeStepCertificate

theorem verifiedShape_rawBitStringSignedSum_closed_assignmentFactorProduct_node
    {a n : Nat} {cs : List RTree} [NeZero n]
    (hshape : VerifiedShape (RTree.node a cs)) :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat
        ((((cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
            Nat) : ℤ) +
          childContribSumWith (Xassign n) n a cs 0) :=
  ModelCertificate.rawBitStringSignedSum_closed_assignmentFactorProduct_node
    (modelCertificate_of_verifiedShape hshape)

theorem verifiedShape_rawBitStringSignedSum_closed_assignmentFactorProduct
    {T : RTree} (hshape : VerifiedShape T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T) := by
  cases T with
  | node a cs =>
      exact
        verifiedShape_rawBitStringSignedSum_closed_assignmentFactorProduct_node
          (n := n) hshape

theorem rawBitStringSignedSum_closed_Xpoly_of_openRootRawNodeStep
    (hopen : OpenRootRawBitStringNodeStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  globalRawBitStringClosedXpoly_of_openRootRawBitStringNodeStepRule
    hopen hT n

theorem rawBitStringSignedSum_closed_connected_terms_of_openRootRawNodeStep
    (hopen : OpenRootRawBitStringNodeStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  globalRawBitStringClosedConnectedTerms_of_openRootRawBitStringNodeStepRule
    hopen hT n

theorem rawBitStringSignedSum_eq_DeltaTreeModel_of_openRootRawNodeStep
    (hopen : OpenRootRawBitStringNodeStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = DeltaTreeModel n T := by
  rw [rawBitStringSignedSum_closed_Xassign_of_openRootRawNodeStep
    hopen hT n]
  rfl

theorem normalFormSignedSum_closed_connected_terms_of_openRootRawNodeStep
    (hopen : OpenRootRawBitStringNodeStepRule)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  change rawBitStringSignedSum n T =
    (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))
  exact rawBitStringSignedSum_closed_connected_terms_of_openRootRawNodeStep
    hopen hT n

end RawPrimitive

end TreeGraph
