import TreeGraph.Imbalance.NodeHeadIndexPhysicalCoeff

namespace TreeGraph
namespace Imbalance

private theorem sum_rootMessageSubtype_eq_boundary_sum_fullCoeff
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (scalar : ℤ)
    (f : P.boundaryMessageSpace → ℤ) :
    (∑ r : P.openBridge.rootMessageSpace,
        scalar * f (P.rootMessageEquivBoundaryMessage r)) =
      scalar * ∑ μ : P.boundaryMessageSpace, f μ := by
  classical
  rw [← Finset.mul_sum]
  rw [Equiv.sum_comp P.rootMessageEquivBoundaryMessage f]

private theorem sum_if_rootMessage_eq_boundary_sum_fullCoeff
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (scalar : ℤ)
    (f : P.boundaryMessageSpace → ℤ) :
    (by
      classical
      exact
        ∑ r : RootFieldAssignmentClean n C,
          if hr : r ∈ P.openBridge.rootMessageSpace then
            scalar * f (P.rootMessageEquivBoundaryMessage ⟨r, hr⟩)
          else
            0) =
      scalar * ∑ μ : P.boundaryMessageSpace, f μ := by
  classical
  let g : RootFieldAssignmentClean n C → ℤ := fun r =>
    if hr : r ∈ P.openBridge.rootMessageSpace then
      scalar * f (P.rootMessageEquivBoundaryMessage ⟨r, hr⟩)
    else
      0
  calc
    (∑ r : RootFieldAssignmentClean n C,
        if hr : r ∈ P.openBridge.rootMessageSpace then
          scalar * f (P.rootMessageEquivBoundaryMessage ⟨r, hr⟩)
        else
          0) =
        ∑ r : RootFieldAssignmentClean n C, g r := by
          rfl
    _ =
        ∑ r ∈ (Finset.univ.filter
          (fun r : RootFieldAssignmentClean n C =>
            r ∈ P.openBridge.rootMessageSpace)), g r := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro r _
          by_cases hr : r ∈ P.openBridge.rootMessageSpace
          · simp [g, hr]
          · simp [g, hr]
    _ =
        ∑ r : P.openBridge.rootMessageSpace, g r := by
          rw [Finset.sum_subtype
            (Finset.univ.filter
              (fun r : RootFieldAssignmentClean n C =>
                r ∈ P.openBridge.rootMessageSpace))]
          · intro r
            simp
    _ =
        ∑ r : P.openBridge.rootMessageSpace,
          scalar * f (P.rootMessageEquivBoundaryMessage r) := by
          refine Finset.sum_congr rfl ?_
          intro r _
          simp [g, r.2]
    _ =
        scalar * ∑ μ : P.boundaryMessageSpace, f μ := by
          exact sum_rootMessageSubtype_eq_boundary_sum_fullCoeff
            n C hC P scalar f

theorem headIndexPhysicalPairSum_eq_messageSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest) :
    (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
      headIndexPhysicalPairWeight n a C rest hC P root idx pair) =
        (2 : ℤ) ^ (Xdim n C - Ydim n C hC) *
          (∑ μ : P.boundaryMessageSpace,
            chi (headChildIndexBranchCoeff n a C rest hC P root idx μ)) := by
  classical
  let scalar : ℤ := (2 : ℤ) ^ (Xdim n C - Ydim n C hC)
  calc
    (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
      headIndexPhysicalPairWeight n a C rest hC P root idx pair) =
        ∑ r : RootFieldAssignmentClean n C,
          (∑ Aopen : OpenNormalAssignmentClean n C,
            weightClean C (closeOpenNormalAssignmentClean r Aopen)) *
            chi (headChildIndexFullBoundaryCoeff
              n a C rest hC P root idx
              (P.rootCopenBridge.linearEquiv r)) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [Finset.sum_mul]
          rfl
    _ =
        ∑ r : RootFieldAssignmentClean n C,
          openNormalSignedSumClean n C r *
            chi (headChildIndexFullBoundaryCoeff
              n a C rest hC P root idx
              (P.rootCopenBridge.linearEquiv r)) := by
          rfl
    _ =
        ∑ r : RootFieldAssignmentClean n C,
          if hr : r ∈ P.openBridge.rootMessageSpace then
            scalar *
              chi (headChildIndexBranchCoeff
                n a C rest hC P root idx
                (P.rootMessageEquivBoundaryMessage ⟨r, hr⟩))
          else
            0 := by
          refine Finset.sum_congr rfl ?_
          intro r _
          by_cases hr : r ∈ P.openBridge.rootMessageSpace
          · rw [P.openBridge.open_signed_sum_eq r]
            rw [if_pos hr]
            have hμ :
                (P.rootMessageEquivBoundaryMessage ⟨r, hr⟩ :
                  P.boundaryMessageSpace).1 =
                  P.rootCopenBridge.linearEquiv r := by
              exact P.rootMessageEquivBoundaryMessage_apply ⟨r, hr⟩
            rw [← hμ]
            rw [headChildIndexFullBoundaryCoeff_restrict_message]
            simp [scalar, hr]
          · rw [P.openBridge.open_signed_sum_eq r]
            rw [if_neg hr]
            simp [hr]
    _ =
        scalar *
          ∑ μ : P.boundaryMessageSpace,
            chi (headChildIndexBranchCoeff
              n a C rest hC P root idx μ) := by
          exact sum_if_rootMessage_eq_boundary_sum_fullCoeff
            n C hC P scalar
            (fun μ : P.boundaryMessageSpace =>
              chi (headChildIndexBranchCoeff
                n a C rest hC P root idx μ))
    _ =
        (2 : ℤ) ^ (Xdim n C - Ydim n C hC) *
          (∑ μ : P.boundaryMessageSpace,
            chi (headChildIndexBranchCoeff
              n a C rest hC P root idx μ)) := by
          rfl

end Imbalance
end TreeGraph
