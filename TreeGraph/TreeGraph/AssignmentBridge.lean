import TreeGraph.AssignmentRecursion

namespace TreeGraph

theorem satisfiesAssignmentRecursion_Xpoly (n : Nat) :
    SatisfiesAssignmentRecursion n (Ypoly n) (Xpoly n) := by
  intro a cs
  constructor
  · simp [branchProductWith, Ypoly]
  · rw [childContribSumWith_Xpoly n a cs 0]
    simp [Xpoly]

theorem satisfiesAssignmentRecursion_Xassign (n : Nat) :
    SatisfiesAssignmentRecursion n (Yassign n) (Xassign n) := by
  simpa [Yassign, Xassign] using satisfiesAssignmentRecursion_Xpoly n

namespace RawPrimitive

def PositiveSignedSumRealizesAssignmentExponent
    (n : Nat) [NeZero n] (X : RTree → ℤ) : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    RawNormal.signedSum n T = (2 : ℤ) ^ Int.toNat (X T)

def PositiveAssignmentRecursionWitness : Prop :=
  ∀ (n : Nat) [NeZero n], ∃ Y X : RTree → ℤ,
    SatisfiesAssignmentRecursion n Y X ∧
      PositiveSignedSumRealizesAssignmentExponent n X

theorem positiveSignedSumRealizesAssignmentExponent_of_global
    {n : Nat} [NeZero n] {X : RTree → ℤ}
    (hglobal : SignedSumRealizesAssignmentExponent n X) :
    PositiveSignedSumRealizesAssignmentExponent n X := by
  intro T _hT
  exact hglobal T

theorem rawBitStringSignedSum_closed_Xpoly_of_positiveAssignmentRecursion
    {n : Nat} [NeZero n] {Y X : RTree → ℤ}
    (hrec : SatisfiesAssignmentRecursion n Y X)
    (hsigned : PositiveSignedSumRealizesAssignmentExponent n X)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    rawBitStringSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [rawBitStringSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := T) hT]
  rw [hsigned hT]
  rw [assignmentRecursion_unique_X hrec T]

theorem rawBitStringSignedSum_closed_connected_terms_of_positiveAssignmentRecursion
    {n : Nat} [NeZero n] {Y X : RTree → ℤ}
    (hrec : SatisfiesAssignmentRecursion n Y X)
    (hsigned : PositiveSignedSumRealizesAssignmentExponent n X)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [rawBitStringSignedSum_closed_Xpoly_of_positiveAssignmentRecursion
    (n := n) hrec hsigned hT]
  rw [Xpoly_eq_allTerms n T]

def GlobalSignedSumRealizesAssignmentExponent : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n T =
        (2 : ℤ) ^ Int.toNat (Xassign n T)

def GlobalSignedSumClosedDeltaTreeModel : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n T = DeltaTreeModel n T

def GlobalSignedSumClosedXpoly : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n T =
        (2 : ℤ) ^ Int.toNat (Xpoly n T)

def GlobalSignedSumClosedConnectedTerms : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n T =
        (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))

theorem globalSignedSumClosedDeltaTreeModel_of_globalSignedSumRealizesAssignmentExponent
    (hglobal : GlobalSignedSumRealizesAssignmentExponent) :
    GlobalSignedSumClosedDeltaTreeModel := by
  intro T hT n _
  simpa [DeltaTreeModel] using hglobal (T := T) hT n

theorem globalSignedSumRealizesAssignmentExponent_of_globalSignedSumClosedDeltaTreeModel
    (hglobal : GlobalSignedSumClosedDeltaTreeModel) :
    GlobalSignedSumRealizesAssignmentExponent := by
  intro T hT n _
  simpa [DeltaTreeModel] using hglobal (T := T) hT n

theorem globalSignedSumRealizesAssignmentExponent_iff_globalSignedSumClosedDeltaTreeModel :
    GlobalSignedSumRealizesAssignmentExponent ↔
      GlobalSignedSumClosedDeltaTreeModel :=
  ⟨globalSignedSumClosedDeltaTreeModel_of_globalSignedSumRealizesAssignmentExponent,
    globalSignedSumRealizesAssignmentExponent_of_globalSignedSumClosedDeltaTreeModel⟩

theorem globalSignedSumClosedDeltaTreeModel_iff_globalSignedSumRealizesAssignmentExponent :
    GlobalSignedSumClosedDeltaTreeModel ↔
      GlobalSignedSumRealizesAssignmentExponent :=
  globalSignedSumRealizesAssignmentExponent_iff_globalSignedSumClosedDeltaTreeModel.symm

theorem globalSignedSumClosedXpoly_of_globalSignedSumRealizesAssignmentExponent
    (hglobal : GlobalSignedSumRealizesAssignmentExponent) :
    GlobalSignedSumClosedXpoly := by
  intro T hT n _
  simpa [Xassign] using hglobal (T := T) hT n

theorem globalSignedSumRealizesAssignmentExponent_of_globalSignedSumClosedXpoly
    (hglobal : GlobalSignedSumClosedXpoly) :
    GlobalSignedSumRealizesAssignmentExponent := by
  intro T hT n _
  simpa [Xassign] using hglobal (T := T) hT n

theorem globalSignedSumRealizesAssignmentExponent_iff_globalSignedSumClosedXpoly :
    GlobalSignedSumRealizesAssignmentExponent ↔
      GlobalSignedSumClosedXpoly :=
  ⟨globalSignedSumClosedXpoly_of_globalSignedSumRealizesAssignmentExponent,
    globalSignedSumRealizesAssignmentExponent_of_globalSignedSumClosedXpoly⟩

theorem globalSignedSumClosedXpoly_iff_globalSignedSumRealizesAssignmentExponent :
    GlobalSignedSumClosedXpoly ↔
      GlobalSignedSumRealizesAssignmentExponent :=
  globalSignedSumRealizesAssignmentExponent_iff_globalSignedSumClosedXpoly.symm

theorem globalSignedSumClosedConnectedTerms_of_globalSignedSumRealizesAssignmentExponent
    (hglobal : GlobalSignedSumRealizesAssignmentExponent) :
    GlobalSignedSumClosedConnectedTerms := by
  intro T hT n _
  simpa [Xassign, Xpoly_eq_allTerms n T] using hglobal (T := T) hT n

theorem globalSignedSumRealizesAssignmentExponent_of_globalSignedSumClosedConnectedTerms
    (hglobal : GlobalSignedSumClosedConnectedTerms) :
    GlobalSignedSumRealizesAssignmentExponent := by
  intro T hT n _
  simpa [Xassign, Xpoly_eq_allTerms n T] using hglobal (T := T) hT n

theorem globalSignedSumRealizesAssignmentExponent_iff_globalSignedSumClosedConnectedTerms :
    GlobalSignedSumRealizesAssignmentExponent ↔
      GlobalSignedSumClosedConnectedTerms :=
  ⟨globalSignedSumClosedConnectedTerms_of_globalSignedSumRealizesAssignmentExponent,
    globalSignedSumRealizesAssignmentExponent_of_globalSignedSumClosedConnectedTerms⟩

theorem globalSignedSumClosedConnectedTerms_iff_globalSignedSumRealizesAssignmentExponent :
    GlobalSignedSumClosedConnectedTerms ↔
      GlobalSignedSumRealizesAssignmentExponent :=
  globalSignedSumRealizesAssignmentExponent_iff_globalSignedSumClosedConnectedTerms.symm

theorem globalSignedSumClosedXpoly_of_positiveAssignmentRecursionWitness
    (hwitness : PositiveAssignmentRecursionWitness) :
    GlobalSignedSumClosedXpoly := by
  intro T hT n _
  rcases hwitness n with ⟨Y, X, hrec, hsigned⟩
  calc
    RawNormal.signedSum n T = (2 : ℤ) ^ Int.toNat (X T) :=
      hsigned hT
    _ = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
      rw [assignmentRecursion_unique_X hrec T]

theorem positiveAssignmentRecursionWitness_of_globalSignedSumClosedXpoly
    (hglobal : GlobalSignedSumClosedXpoly) :
    PositiveAssignmentRecursionWitness := by
  intro n _
  refine ⟨Yassign n, Xassign n, satisfiesAssignmentRecursion_Xassign n, ?_⟩
  intro T hT
  simpa [Xassign] using hglobal (T := T) hT n

theorem positiveAssignmentRecursionWitness_iff_globalSignedSumClosedXpoly :
    PositiveAssignmentRecursionWitness ↔ GlobalSignedSumClosedXpoly :=
  ⟨globalSignedSumClosedXpoly_of_positiveAssignmentRecursionWitness,
    positiveAssignmentRecursionWitness_of_globalSignedSumClosedXpoly⟩

theorem globalSignedSumClosedXpoly_iff_positiveAssignmentRecursionWitness :
    GlobalSignedSumClosedXpoly ↔ PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_iff_globalSignedSumClosedXpoly.symm

theorem globalSignedSumRealizesAssignmentExponent_of_positiveAssignmentRecursionWitness
    (hwitness : PositiveAssignmentRecursionWitness) :
    GlobalSignedSumRealizesAssignmentExponent :=
  globalSignedSumRealizesAssignmentExponent_of_globalSignedSumClosedXpoly
    (globalSignedSumClosedXpoly_of_positiveAssignmentRecursionWitness
      hwitness)

theorem positiveAssignmentRecursionWitness_of_globalSignedSumRealizesAssignmentExponent
    (hglobal : GlobalSignedSumRealizesAssignmentExponent) :
    PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_of_globalSignedSumClosedXpoly
    (globalSignedSumClosedXpoly_of_globalSignedSumRealizesAssignmentExponent
      hglobal)

theorem positiveAssignmentRecursionWitness_iff_globalSignedSumRealizesAssignmentExponent :
    PositiveAssignmentRecursionWitness ↔
      GlobalSignedSumRealizesAssignmentExponent :=
  positiveAssignmentRecursionWitness_iff_globalSignedSumClosedXpoly.trans
    globalSignedSumClosedXpoly_iff_globalSignedSumRealizesAssignmentExponent

theorem globalSignedSumRealizesAssignmentExponent_iff_positiveAssignmentRecursionWitness :
    GlobalSignedSumRealizesAssignmentExponent ↔
      PositiveAssignmentRecursionWitness :=
  positiveAssignmentRecursionWitness_iff_globalSignedSumRealizesAssignmentExponent.symm

theorem globalSignedSumRealizesAssignmentExponent_of_nodeStepRule
    (hstep : NodeStepRule) :
    GlobalSignedSumRealizesAssignmentExponent := by
  intro T hT n _
  have hcert :=
    subtreeModelCertificate_of_positiveWeights_of_nodeStepRule hstep hT
  rw [SubtreeModelCertificate.signedSum_eq_DeltaTreeModel hcert n]
  rfl

theorem nodeStepRule_of_globalSignedSumRealizesAssignmentExponent
    (hglobal : GlobalSignedSumRealizesAssignmentExponent) :
    NodeStepRule := by
  intro a cs ha hchildren n _
  have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
    intro C hC
    exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
  have hpos : RTree.PositiveWeights (RTree.node a cs) := by
    have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
      ⟨ha, hchildPos⟩
    simpa [RTree.PositiveWeights] using hnode
  simpa [DeltaTreeModel] using
    hglobal (T := RTree.node a cs) hpos n

theorem nodeStepRule_iff_globalSignedSumRealizesAssignmentExponent :
    NodeStepRule ↔ GlobalSignedSumRealizesAssignmentExponent :=
  ⟨globalSignedSumRealizesAssignmentExponent_of_nodeStepRule,
    nodeStepRule_of_globalSignedSumRealizesAssignmentExponent⟩

theorem globalSignedSumRealizesAssignmentExponent_iff_nodeStepRule :
    GlobalSignedSumRealizesAssignmentExponent ↔ NodeStepRule :=
  nodeStepRule_iff_globalSignedSumRealizesAssignmentExponent.symm

theorem positiveSignedSumRealizesAssignmentExponent_Xassign_of_nodeStepRule
    (hstep : NodeStepRule) (n : Nat) [NeZero n] :
    PositiveSignedSumRealizesAssignmentExponent n (Xassign n) := by
  intro T hT
  exact globalSignedSumRealizesAssignmentExponent_of_nodeStepRule
    hstep hT n

def GlobalRawBitStringClosedXassign : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n T =
        (2 : ℤ) ^ Int.toNat (Xassign n T)

theorem globalRawBitStringClosedXassign_of_globalSignedSumRealizesAssignmentExponent
    (hglobal : GlobalSignedSumRealizesAssignmentExponent) :
    GlobalRawBitStringClosedXassign := by
  intro T hT n _
  rw [rawBitStringSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := T) hT]
  exact hglobal hT n

theorem globalSignedSumRealizesAssignmentExponent_of_globalRawBitStringClosedXassign
    (hglobal : GlobalRawBitStringClosedXassign) :
    GlobalSignedSumRealizesAssignmentExponent := by
  intro T hT n _
  have hraw := hglobal hT n
  have htoSigned :
      rawBitStringSignedSum n T = RawNormal.signedSum n T :=
    rawBitStringSignedSum_eq_signedSum_of_positiveWeights
      (n := n) (T := T) hT
  rw [htoSigned] at hraw
  exact hraw

theorem globalSignedSumRealizesAssignmentExponent_iff_globalRawBitStringClosedXassign :
    GlobalSignedSumRealizesAssignmentExponent ↔
      GlobalRawBitStringClosedXassign :=
  ⟨globalRawBitStringClosedXassign_of_globalSignedSumRealizesAssignmentExponent,
    globalSignedSumRealizesAssignmentExponent_of_globalRawBitStringClosedXassign⟩

theorem globalRawBitStringClosedXassign_iff_globalSignedSumRealizesAssignmentExponent :
    GlobalRawBitStringClosedXassign ↔
      GlobalSignedSumRealizesAssignmentExponent :=
  globalSignedSumRealizesAssignmentExponent_iff_globalRawBitStringClosedXassign.symm

theorem globalRawBitStringClosedXpoly_of_globalRawBitStringClosedXassign
    (hglobal : GlobalRawBitStringClosedXassign) :
    GlobalRawBitStringClosedXpoly := by
  intro T hT n _
  simpa [Xassign] using hglobal (T := T) hT n

theorem globalRawBitStringClosedXassign_of_globalRawBitStringClosedXpoly
    (hglobal : GlobalRawBitStringClosedXpoly) :
    GlobalRawBitStringClosedXassign := by
  intro T hT n _
  simpa [Xassign] using hglobal (T := T) hT n

theorem globalRawBitStringClosedXassign_iff_globalRawBitStringClosedXpoly :
    GlobalRawBitStringClosedXassign ↔ GlobalRawBitStringClosedXpoly :=
  ⟨globalRawBitStringClosedXpoly_of_globalRawBitStringClosedXassign,
    globalRawBitStringClosedXassign_of_globalRawBitStringClosedXpoly⟩

theorem globalRawBitStringClosedXpoly_iff_globalRawBitStringClosedXassign :
    GlobalRawBitStringClosedXpoly ↔ GlobalRawBitStringClosedXassign :=
  globalRawBitStringClosedXassign_iff_globalRawBitStringClosedXpoly.symm

theorem globalRawBitStringClosedConnectedTerms_of_globalRawBitStringClosedXassign
    (hglobal : GlobalRawBitStringClosedXassign) :
    GlobalRawBitStringClosedConnectedTerms := by
  intro T hT n _
  simpa [Xassign, Xpoly_eq_allTerms n T] using hglobal (T := T) hT n

theorem globalRawBitStringClosedXassign_of_globalRawBitStringClosedConnectedTerms
    (hglobal : GlobalRawBitStringClosedConnectedTerms) :
    GlobalRawBitStringClosedXassign := by
  intro T hT n _
  simpa [Xassign, Xpoly_eq_allTerms n T] using hglobal (T := T) hT n

theorem globalRawBitStringClosedXassign_iff_globalRawBitStringClosedConnectedTerms :
    GlobalRawBitStringClosedXassign ↔
      GlobalRawBitStringClosedConnectedTerms :=
  ⟨globalRawBitStringClosedConnectedTerms_of_globalRawBitStringClosedXassign,
    globalRawBitStringClosedXassign_of_globalRawBitStringClosedConnectedTerms⟩

theorem globalRawBitStringClosedConnectedTerms_iff_globalRawBitStringClosedXassign :
    GlobalRawBitStringClosedConnectedTerms ↔
      GlobalRawBitStringClosedXassign :=
  globalRawBitStringClosedXassign_iff_globalRawBitStringClosedConnectedTerms.symm

theorem globalSignedSumRealizesAssignmentExponent_iff_globalRawBitStringClosedXpoly :
    GlobalSignedSumRealizesAssignmentExponent ↔
      GlobalRawBitStringClosedXpoly := by
  exact
    globalSignedSumRealizesAssignmentExponent_iff_globalRawBitStringClosedXassign.trans
      globalRawBitStringClosedXassign_iff_globalRawBitStringClosedXpoly

theorem globalSignedSumRealizesAssignmentExponent_iff_globalRawBitStringClosedConnectedTerms :
    GlobalSignedSumRealizesAssignmentExponent ↔
      GlobalRawBitStringClosedConnectedTerms := by
  exact
    globalSignedSumRealizesAssignmentExponent_iff_globalRawBitStringClosedXassign.trans
      globalRawBitStringClosedXassign_iff_globalRawBitStringClosedConnectedTerms

theorem nodeStepRule_iff_globalRawBitStringClosedXassign :
    NodeStepRule ↔ GlobalRawBitStringClosedXassign := by
  exact
    nodeStepRule_iff_globalSignedSumRealizesAssignmentExponent.trans
      globalSignedSumRealizesAssignmentExponent_iff_globalRawBitStringClosedXassign

theorem rawBitStringSignedSum_closed_Xpoly_of_globalSignedSumAssignment
    (hglobal : GlobalSignedSumRealizesAssignmentExponent)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  exact rawBitStringSignedSum_closed_Xpoly_of_positiveAssignmentRecursion
    (satisfiesAssignmentRecursion_Xassign n)
    (by
      intro U hU
      exact hglobal hU n)
    hT

theorem rawBitStringSignedSum_closed_connected_terms_of_globalSignedSumAssignment
    (hglobal : GlobalSignedSumRealizesAssignmentExponent)
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [rawBitStringSignedSum_closed_Xpoly_of_globalSignedSumAssignment
    hglobal hT n]
  rw [Xpoly_eq_allTerms n T]

end RawPrimitive

end TreeGraph
