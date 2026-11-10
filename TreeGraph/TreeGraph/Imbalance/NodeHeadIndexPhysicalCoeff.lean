import TreeGraph.Imbalance.NodeHeadPhaseProduct

namespace TreeGraph
namespace Imbalance

noncomputable def headChildRFull
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C) :
    BranchField n C →ₗ[F2]
      (Rep n → Module.Dual F2 (BoundaryField n C)) := by
  cases C with
  | node b ds =>
      exact PiFull n
        (rootWeight_pos_of_positiveWeights hC)
        (Copen n (RTree.node b ds))

@[simp] theorem headChildRFull_node_apply
    (n b : Nat) [NeZero n]
    (ds : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (h : BranchField n (RTree.node b ds)) (s : Rep n) :
    headChildRFull n (RTree.node b ds) hC h s =
      PiFull n
        (rootWeight_pos_of_positiveWeights hC)
        (Copen n (RTree.node b ds)) h s := by
  rfl

theorem headChildRFull_headParentRootBranch_node_apply
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : CoordsList n rest)
    (s : Rep n) (μ : BoundaryField n (RTree.node b ds)) :
    headChildRFull n (RTree.node b ds) hC
        (headParentRootBranchFieldFromRoot n a
          (RTree.node b ds) rest root tail) s μ =
      ∑ y : Copen n (RTree.node b ds),
        μ y *
          (∑ x : Block n b,
            if diag n b x = s then
              headParentRootBoundaryFieldFromRoot n a
                (RTree.node b ds) rest root ((x, y), tail)
            else 0) := by
  rw [headChildRFull_node_apply]
  rw [PiFull_apply]
  change
    (∑ y : Copen n (RTree.node b ds),
      μ y *
        PiCoeff n (rootWeight_pos_of_positiveWeights hC)
          (Copen n (RTree.node b ds))
          (headParentRootBranchFieldFromRoot n a
            (RTree.node b ds) rest root tail) (s, y)) =
      ∑ y : Copen n (RTree.node b ds),
        μ y *
          (∑ x : Block n b,
            if diag n b x = s then
              headParentRootBoundaryFieldFromRoot n a
                (RTree.node b ds) rest root ((x, y), tail)
            else 0)
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [PiCoeff_apply]
  rfl

theorem headChildR_apply_eq_fullBoundary
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (h : BranchField n C) (s : Rep n)
    (μ : P.boundaryMessageSpace) :
    headChildR n C hC P h s μ =
      headChildRFull n C hC h s μ.1 := by
  cases C with
  | node b ds =>
      rfl

noncomputable def headChildIndexFullBoundaryCoeff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (_P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest) :
    Module.Dual F2 (BoundaryField n C) :=
  branchMessageCoeff n
    (CoordsList n rest)
    (BranchField n C)
    (BoundaryField n C)
    (headChildRFull n C hC)
    (headParentRootBranchFieldFromRoot n a C rest root)
    (headChildIndexTail idx, headChildIndexRootDiag idx)

theorem headChildIndexFullBoundaryCoeff_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest)
    (μ : BoundaryField n C) :
    headChildIndexFullBoundaryCoeff n a C rest hC P root idx μ =
      (headChildRFull n C hC
          (headParentRootBranchFieldFromRoot n a C rest root
            (headChildIndexTail idx))
          (headChildIndexRootDiag idx) +
        headChildRFull n C hC
          (headParentRootBranchFieldFromRoot n a C rest root
            (headChildIndexTail idx))
          (headChildIndexRootDiag idx + 1)) μ := by
  unfold headChildIndexFullBoundaryCoeff branchMessageCoeff
  simp [familyCycDiff_apply, RtildeAbstract_apply]

theorem headChildIndexFullBoundaryCoeff_restrict_message
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest) (μ : P.boundaryMessageSpace) :
    headChildIndexFullBoundaryCoeff n a C rest hC P root idx μ.1 =
      headChildIndexBranchCoeff n a C rest hC P root idx μ := by
  change
    (familyCycDiff n (CoordsList n rest)
      (Module.Dual F2 (BoundaryField n C))
      (RtildeAbstract n (CoordsList n rest) (BranchField n C)
        (BoundaryField n C)
        (headChildRFull n C hC)
        (headParentRootBranchFieldFromRoot n a C rest root))
      (headChildIndexTail idx, headChildIndexRootDiag idx)) μ.1 =
    (familyCycDiff n (CoordsList n rest)
      (Module.Dual F2 P.boundaryMessageSpace)
      (RtildeAbstract n (CoordsList n rest) (BranchField n C)
        P.boundaryMessageSpace
        (headChildR n C hC P)
        (headParentRootBranchFieldFromRoot n a C rest root))
      (headChildIndexTail idx, headChildIndexRootDiag idx)) μ
  simp only [familyCycDiff_apply, RtildeAbstract_apply]
  have h0 :=
    headChildR_apply_eq_fullBoundary n C hC P
      (headParentRootBranchFieldFromRoot n a C rest root
        (headChildIndexTail idx))
      (headChildIndexRootDiag idx) μ
  have h1 :=
    headChildR_apply_eq_fullBoundary n C hC P
      (headParentRootBranchFieldFromRoot n a C rest root
        (headChildIndexTail idx))
      (headChildIndexRootDiag idx + 1) μ
  change
    ((headChildRFull n C hC)
          (headParentRootBranchFieldFromRoot n a C rest root
            (headChildIndexTail idx))
          (headChildIndexRootDiag idx) μ.1 +
        (headChildRFull n C hC)
          (headParentRootBranchFieldFromRoot n a C rest root
            (headChildIndexTail idx))
          (headChildIndexRootDiag idx + 1) μ.1) =
      ((headChildR n C hC P)
          (headParentRootBranchFieldFromRoot n a C rest root
            (headChildIndexTail idx))
          (headChildIndexRootDiag idx) μ +
        (headChildR n C hC P)
          (headParentRootBranchFieldFromRoot n a C rest root
            (headChildIndexTail idx))
          (headChildIndexRootDiag idx + 1) μ)
  rw [h0, h1]

noncomputable def headIndexPhysicalPairWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest)
    (pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C) :
    ℤ :=
  weightClean C (closeOpenNormalAssignmentClean pair.1 pair.2) *
    chi (headChildIndexFullBoundaryCoeff n a C rest hC P root idx
      (P.rootCopenBridge.linearEquiv pair.1))

theorem headIndexPhysicalPairWeight_eq_messageWeight_of_mem
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest)
    (r : RootFieldAssignmentClean n C)
    (Aopen : OpenNormalAssignmentClean n C)
    (hr : r ∈ P.openBridge.rootMessageSpace) :
    headIndexPhysicalPairWeight n a C rest hC P root idx (r, Aopen) =
      weightClean C (closeOpenNormalAssignmentClean r Aopen) *
        chi (headChildIndexBranchCoeff n a C rest hC P root idx
          (P.rootMessageEquivBoundaryMessage ⟨r, hr⟩)) := by
  rw [headIndexPhysicalPairWeight]
  congr 1
  congr 1
  have hμ :
      (P.rootMessageEquivBoundaryMessage ⟨r, hr⟩ :
        P.boundaryMessageSpace).1 =
        P.rootCopenBridge.linearEquiv r := by
    exact P.rootMessageEquivBoundaryMessage_apply ⟨r, hr⟩
  rw [← hμ]
  exact headChildIndexFullBoundaryCoeff_restrict_message
    n a C rest hC P root idx
    (P.rootMessageEquivBoundaryMessage ⟨r, hr⟩)

end Imbalance
end TreeGraph
