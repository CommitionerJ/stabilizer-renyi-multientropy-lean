import TreeGraph.IndependentBranch

namespace TreeGraph

namespace RawPrimitive

theorem childContribSumWith_Xassign
    (n a : Nat) (cs : List RTree) (left : Nat) :
    childContribSumWith (Xassign n) n a cs left =
      childContribSum n a cs left := by
  simpa [Xassign] using childContribSumWith_Xpoly n a cs left

noncomputable def openRootNodeExponent
    (n a : Nat) (cs : List RTree) : ℤ :=
  ((Module.finrank F2 (OpenRootMessageSpace n cs) : Nat) : ℤ) +
    childContribSumWith (Xassign n) n a cs 0

noncomputable def assignmentFactorProductExponent
    (n : Nat) : RTree → ℤ
  | RTree.node a cs =>
      ((((cs.map (fun C =>
        Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
          Nat) : ℤ) +
        childContribSumWith (Xassign n) n a cs 0)

theorem assignmentFactorProductExponent_node
    (n a : Nat) (cs : List RTree) :
    assignmentFactorProductExponent n (RTree.node a cs) =
      ((((cs.map (fun C =>
        Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
          Nat) : ℤ) +
        childContribSumWith (Xassign n) n a cs 0) := by
  rfl

theorem openRootNodeExponent_eq_assignmentFactorProduct
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C) :
    openRootNodeExponent n a cs =
      ((((cs.map (fun C =>
        Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
          Nat) : ℤ) +
        childContribSumWith (Xassign n) n a cs 0) := by
  unfold openRootNodeExponent
  rw [finrank_openRootMessageSpace_eq_assignmentFactorProduct
    (n := n) hchildren]

theorem openRootNodeExponent_eq_assignmentFactorProductExponent
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C) :
    openRootNodeExponent n a cs =
      assignmentFactorProductExponent n (RTree.node a cs) := by
  simpa [assignmentFactorProductExponent] using
    openRootNodeExponent_eq_assignmentFactorProduct
      (n := n) (a := a) (cs := cs) hchildren

theorem openRootNodeExponent_eq_assignmentFactorProduct_of_children
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    openRootNodeExponent n a cs =
      ((((cs.map (fun C =>
        Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
          Nat) : ℤ) +
        childContribSumWith (Xassign n) n a cs 0) := by
  have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
    intro C hC
    exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
  exact openRootNodeExponent_eq_assignmentFactorProduct
    (n := n) (a := a) (cs := cs) hchildPos

theorem openRootNodeExponent_eq_assignmentFactorProductExponent_of_children
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    openRootNodeExponent n a cs =
      assignmentFactorProductExponent n (RTree.node a cs) := by
  have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
    intro C hC
    exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
  exact openRootNodeExponent_eq_assignmentFactorProductExponent
    (n := n) (a := a) (cs := cs) hchildPos

theorem openRootNodeExponent_eq_assignmentFactorProduct_of_positiveWeights
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    openRootNodeExponent n a cs =
      ((((cs.map (fun C =>
        Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod :
          Nat) : ℤ) +
        childContribSumWith (Xassign n) n a cs 0) := by
  have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
    simpa [RTree.PositiveWeights] using hT
  exact openRootNodeExponent_eq_assignmentFactorProduct
    (n := n) (a := a) (cs := cs) hnode.2

theorem openRootNodeExponent_eq_assignmentFactorProductExponent_of_positiveWeights
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    openRootNodeExponent n a cs =
      assignmentFactorProductExponent n (RTree.node a cs) := by
  have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
    simpa [RTree.PositiveWeights] using hT
  exact openRootNodeExponent_eq_assignmentFactorProductExponent
    (n := n) (a := a) (cs := cs) hnode.2

theorem openRootNodeExponent_eq_Xassign_of_positiveWeights
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    openRootNodeExponent n a cs = Xassign n (RTree.node a cs) := by
  have hopen :=
    openRootMessageSpace_finrank_eq_Yassign_of_positiveWeights
      (n := n) hT
  have hchild := childContribSumWith_Xassign n a cs 0
  unfold openRootNodeExponent
  rw [hopen, hchild]
  exact (Xassign_node n a cs).symm

theorem assignmentFactorProductExponent_eq_Xassign_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree}
    (hT : RTree.PositiveWeights T) :
    assignmentFactorProductExponent n T = Xassign n T := by
  cases T with
  | node a cs =>
      exact
        (openRootNodeExponent_eq_assignmentFactorProductExponent_of_positiveWeights
          (n := n) (a := a) (cs := cs) hT).symm.trans
          (openRootNodeExponent_eq_Xassign_of_positiveWeights
            (n := n) (a := a) (cs := cs) hT)

theorem DeltaTreeModel_closed_assignmentFactorProductExponent
    {n : Nat} [NeZero n] {T : RTree}
    (hT : RTree.PositiveWeights T) :
    DeltaTreeModel n T =
      (2 : ℤ) ^ Int.toNat (assignmentFactorProductExponent n T) := by
  rw [DeltaTreeModel,
    assignmentFactorProductExponent_eq_Xassign_of_positiveWeights
      (n := n) hT]

theorem openRootNodeExponent_eq_Xassign_of_children
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    openRootNodeExponent n a cs = Xassign n (RTree.node a cs) := by
  have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
    intro C hC
    exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
  have hT : RTree.PositiveWeights (RTree.node a cs) := by
    have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
      ⟨ha, hchildPos⟩
    simpa [RTree.PositiveWeights] using hnode
  exact openRootNodeExponent_eq_Xassign_of_positiveWeights
    (n := n) hT

theorem DeltaTreeModel_node_eq_openRootNodeExponent_of_children
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, SubtreeModelCertificate C) :
    DeltaTreeModel n (RTree.node a cs) =
      (2 : ℤ) ^ Int.toNat (openRootNodeExponent n a cs) := by
  have hX :=
    openRootNodeExponent_eq_Xassign_of_children
      (n := n) ha hchildren
  rw [DeltaTreeModel, ← hX]

def OpenRootNodeStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, SubtreeModelCertificate C) →
    ∀ (n : Nat) [NeZero n],
      RawNormal.signedSum n (RTree.node a cs) =
        (2 : ℤ) ^ Int.toNat (openRootNodeExponent n a cs)

theorem openRootNodeStepRule_of_nodeStepRule
    (hstep : NodeStepRule) :
    OpenRootNodeStepRule := by
  intro a cs ha hchildren n _
  have hsigned := hstep ha hchildren n
  have hdelta :=
    DeltaTreeModel_node_eq_openRootNodeExponent_of_children
      (n := n) ha hchildren
  exact hsigned.trans hdelta

theorem nodeStepRule_of_openRootNodeStepRule
    (hopen : OpenRootNodeStepRule) :
    NodeStepRule := by
  intro a cs ha hchildren n _
  have hsigned := hopen ha hchildren n
  have hdelta :=
    DeltaTreeModel_node_eq_openRootNodeExponent_of_children
      (n := n) ha hchildren
  exact hsigned.trans hdelta.symm

theorem nodeStepRule_iff_openRootNodeStepRule :
    NodeStepRule ↔ OpenRootNodeStepRule :=
  ⟨openRootNodeStepRule_of_nodeStepRule,
    nodeStepRule_of_openRootNodeStepRule⟩

def OpenRootRawBitStringNodeStepRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, SubtreeModelCertificate C) →
    ∀ (n : Nat) [NeZero n],
      rawBitStringSignedSum n (RTree.node a cs) =
        (2 : ℤ) ^ Int.toNat (openRootNodeExponent n a cs)

theorem openRootRawBitStringNodeStepRule_of_nodeStepRule
    (hstep : NodeStepRule) :
    OpenRootRawBitStringNodeStepRule := by
  intro a cs ha hchildren n _
  have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
    intro C hC
    exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
  have hT : RTree.PositiveWeights (RTree.node a cs) := by
    have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
      ⟨ha, hchildPos⟩
    simpa [RTree.PositiveWeights] using hnode
  rw [rawBitStringSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := RTree.node a cs) hT]
  exact openRootNodeStepRule_of_nodeStepRule hstep ha hchildren n

theorem nodeStepRule_of_openRootRawBitStringNodeStepRule
    (hopen : OpenRootRawBitStringNodeStepRule) :
    NodeStepRule := by
  intro a cs ha hchildren n _
  have hchildPos : ∀ C ∈ cs, RTree.PositiveWeights C := by
    intro C hC
    exact SubtreeModelCertificate.positiveWeights (hchildren C hC)
  have hT : RTree.PositiveWeights (RTree.node a cs) := by
    have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
      ⟨ha, hchildPos⟩
    simpa [RTree.PositiveWeights] using hnode
  have hraw := hopen ha hchildren n
  have htoSigned :
      rawBitStringSignedSum n (RTree.node a cs) =
        RawNormal.signedSum n (RTree.node a cs) :=
    rawBitStringSignedSum_eq_signedSum_of_positiveWeights
      (n := n) (T := RTree.node a cs) hT
  have hdelta :=
    DeltaTreeModel_node_eq_openRootNodeExponent_of_children
      (n := n) ha hchildren
  exact htoSigned.symm.trans (hraw.trans hdelta.symm)

theorem nodeStepRule_iff_openRootRawBitStringNodeStepRule :
    NodeStepRule ↔ OpenRootRawBitStringNodeStepRule :=
  ⟨openRootRawBitStringNodeStepRule_of_nodeStepRule,
    nodeStepRule_of_openRootRawBitStringNodeStepRule⟩

end RawPrimitive

end TreeGraph
