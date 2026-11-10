import TreeGraph.ModelCertificate

namespace TreeGraph

namespace RawPrimitive

def SubtreeModelCertificate : RTree → Prop
  | RTree.node a cs =>
      ModelCertificate (RTree.node a cs) ∧
        ∀ C ∈ cs, SubtreeModelCertificate C

namespace SubtreeModelCertificate

theorem root {T : RTree} (hT : SubtreeModelCertificate T) :
    ModelCertificate T := by
  cases T with
  | node a cs =>
      have h :
          ModelCertificate (RTree.node a cs) ∧
            (∀ C ∈ cs, SubtreeModelCertificate C) := by
        simpa [SubtreeModelCertificate] using hT
      exact h.1

theorem children {a : Nat} {cs : List RTree}
    (hT : SubtreeModelCertificate (RTree.node a cs))
    {C : RTree} (hC : C ∈ cs) :
    SubtreeModelCertificate C := by
  have h :
      ModelCertificate (RTree.node a cs) ∧
        (∀ C ∈ cs, SubtreeModelCertificate C) := by
    simpa [SubtreeModelCertificate] using hT
  exact h.2 C hC

theorem positiveWeights {T : RTree} (hT : SubtreeModelCertificate T) :
    RTree.PositiveWeights T :=
  (root hT).positiveWeights

theorem signedSum_eq_DeltaTreeModel
    {T : RTree} (hT : SubtreeModelCertificate T)
    (n : Nat) [NeZero n] :
    RawNormal.signedSum n T = DeltaTreeModel n T :=
  (root hT).signedSum_eq_DeltaTreeModel n

theorem rawBitStringSignedSum_closed_Xpoly
    {T : RTree} (hT : SubtreeModelCertificate T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  ModelCertificate.rawBitStringSignedSum_closed_Xpoly (root hT) n

theorem rawBitStringSignedSum_closed_connected_terms
    {T : RTree} (hT : SubtreeModelCertificate T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  ModelCertificate.rawBitStringSignedSum_closed_connected_terms (root hT) n

end SubtreeModelCertificate

structure NodeStepCertificate (a : Nat) (cs : List RTree) : Prop where
  positiveRoot : 0 < a
  children : ∀ C ∈ cs, SubtreeModelCertificate C
  signedSum_eq_DeltaTreeModel :
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n (RTree.node a cs) =
        DeltaTreeModel n (RTree.node a cs)

def NodeStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, SubtreeModelCertificate C) →
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n (RTree.node a cs) =
        DeltaTreeModel n (RTree.node a cs)

def GlobalRawBitStringClosedXpoly : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T)

def GlobalRawBitStringClosedConnectedTerms : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n T =
        (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))

namespace NodeStepCertificate

theorem positiveWeights {a : Nat} {cs : List RTree}
    (h : NodeStepCertificate a cs) :
    RTree.PositiveWeights (RTree.node a cs) := by
  have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
    refine ⟨h.positiveRoot, ?_⟩
    intro C hC
    exact SubtreeModelCertificate.positiveWeights (h.children C hC)
  simpa [RTree.PositiveWeights] using hnode

theorem modelCertificate {a : Nat} {cs : List RTree}
    (h : NodeStepCertificate a cs) :
    ModelCertificate (RTree.node a cs) where
  positiveWeights := h.positiveWeights
  signedSum_eq_DeltaTreeModel := by
    intro n _
    exact h.signedSum_eq_DeltaTreeModel n

end NodeStepCertificate

theorem nodeStepCertificate_of_rule
    (hstep : NodeStepRule) {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    NodeStepCertificate a cs where
  positiveRoot := ha
  children := hchildren
  signedSum_eq_DeltaTreeModel := by
    intro n _
    exact hstep ha hchildren n

theorem subtreeModelCertificate_node_of_step {a : Nat} {cs : List RTree}
    (h : NodeStepCertificate a cs) :
    SubtreeModelCertificate (RTree.node a cs) := by
  simpa [SubtreeModelCertificate] using
    (show
      ModelCertificate (RTree.node a cs) ∧
        (∀ C ∈ cs, SubtreeModelCertificate C) from
      ⟨h.modelCertificate, h.children⟩)

theorem nodeStepCertificate_rawBitStringSignedSum_closed_Xpoly
    {a : Nat} {cs : List RTree} (h : NodeStepCertificate a cs)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat (Xpoly n (RTree.node a cs)) :=
  SubtreeModelCertificate.rawBitStringSignedSum_closed_Xpoly
    (subtreeModelCertificate_node_of_step h) n

theorem nodeStepCertificate_rawBitStringSignedSum_closed_connected_terms
    {a : Nat} {cs : List RTree} (h : NodeStepCertificate a cs)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms (RTree.node a cs))) :=
  SubtreeModelCertificate.rawBitStringSignedSum_closed_connected_terms
    (subtreeModelCertificate_node_of_step h) n

theorem subtreeModelCertificate_of_positiveWeights_of_nodeStepRule
    (hstep : NodeStepRule) {T : RTree} (hT : RTree.PositiveWeights T) :
    SubtreeModelCertificate T := by
  induction T using rootedTerms.induct with
  | case1 a cs ih =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      have hchildren : ∀ C ∈ cs, SubtreeModelCertificate C := by
        intro C hC
        exact ih C hC (hnode.2 C hC)
      exact subtreeModelCertificate_node_of_step
        (nodeStepCertificate_of_rule hstep hnode.1 hchildren)

theorem modelCertificate_of_positiveWeights_of_nodeStepRule
    (hstep : NodeStepRule) {T : RTree} (hT : RTree.PositiveWeights T) :
    ModelCertificate T :=
  SubtreeModelCertificate.root
    (subtreeModelCertificate_of_positiveWeights_of_nodeStepRule hstep hT)

theorem rawBitStringSignedSum_closed_Xpoly_of_nodeStepRule
    (hstep : NodeStepRule) {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  SubtreeModelCertificate.rawBitStringSignedSum_closed_Xpoly
    (subtreeModelCertificate_of_positiveWeights_of_nodeStepRule hstep hT) n

theorem rawBitStringSignedSum_closed_connected_terms_of_nodeStepRule
    (hstep : NodeStepRule) {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  SubtreeModelCertificate.rawBitStringSignedSum_closed_connected_terms
    (subtreeModelCertificate_of_positiveWeights_of_nodeStepRule hstep hT) n

theorem globalRawBitStringClosedXpoly_of_nodeStepRule
    (hstep : NodeStepRule) :
    GlobalRawBitStringClosedXpoly := by
  intro T hT n
  exact rawBitStringSignedSum_closed_Xpoly_of_nodeStepRule hstep hT n

theorem globalRawBitStringClosedConnectedTerms_of_nodeStepRule
    (hstep : NodeStepRule) :
    GlobalRawBitStringClosedConnectedTerms := by
  intro T hT n
  exact rawBitStringSignedSum_closed_connected_terms_of_nodeStepRule hstep hT n

theorem nodeStepRule_of_globalRawBitStringClosedXpoly
    (hglobal : GlobalRawBitStringClosedXpoly) :
    NodeStepRule := by
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
  rw [htoSigned] at hraw
  exact hraw.trans (DeltaTreeModel_closed_Xpoly n (RTree.node a cs)).symm

theorem nodeStepRule_of_globalRawBitStringClosedConnectedTerms
    (hglobal : GlobalRawBitStringClosedConnectedTerms) :
    NodeStepRule := by
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
  rw [htoSigned] at hraw
  exact hraw.trans (DeltaTreeModel_closed n (RTree.node a cs)).symm

theorem nodeStepRule_iff_globalRawBitStringClosedXpoly :
    NodeStepRule ↔ GlobalRawBitStringClosedXpoly :=
  ⟨globalRawBitStringClosedXpoly_of_nodeStepRule,
    nodeStepRule_of_globalRawBitStringClosedXpoly⟩

theorem nodeStepRule_iff_globalRawBitStringClosedConnectedTerms :
    NodeStepRule ↔ GlobalRawBitStringClosedConnectedTerms :=
  ⟨globalRawBitStringClosedConnectedTerms_of_nodeStepRule,
    nodeStepRule_of_globalRawBitStringClosedConnectedTerms⟩

theorem nodeStepCertificate_leaf (a : Nat) (ha : 0 < a) :
    NodeStepCertificate a [] where
  positiveRoot := ha
  children := by
    intro C hC
    cases hC
  signedSum_eq_DeltaTreeModel := by
    intro n _
    exact RawNormal.signedSum_leaf_eq_DeltaTreeModel n a

theorem subtreeModelCertificate_leaf (a : Nat) (ha : 0 < a) :
    SubtreeModelCertificate (RTree.node a []) :=
  subtreeModelCertificate_node_of_step (nodeStepCertificate_leaf a ha)

theorem nodeStepCertificate_edge (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    NodeStepCertificate a [RTree.node b []] where
  positiveRoot := ha
  children := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rw [hC]
    exact subtreeModelCertificate_leaf b hb
  signedSum_eq_DeltaTreeModel := by
    intro n _
    exact signedSum_edge_eq_DeltaTreeModel ha hb

theorem subtreeModelCertificate_edge
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    SubtreeModelCertificate (RTree.node a [RTree.node b []]) :=
  subtreeModelCertificate_node_of_step
    (nodeStepCertificate_edge a b ha hb)

theorem nodeStepCertificate_star
    (a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    NodeStepCertificate a [RTree.node b [], RTree.node c []] where
  positiveRoot := ha
  children := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with hC | hC
    · rw [hC]
      exact subtreeModelCertificate_leaf b hb
    · rw [hC]
      exact subtreeModelCertificate_leaf c hc
  signedSum_eq_DeltaTreeModel := by
    intro n _
    exact signedSum_star_eq_DeltaTreeModel ha hb hc

theorem subtreeModelCertificate_star
    (a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    SubtreeModelCertificate (StarTree a b c) := by
  exact subtreeModelCertificate_node_of_step
    (nodeStepCertificate_star a b c ha hb hc)

end RawPrimitive

end TreeGraph
