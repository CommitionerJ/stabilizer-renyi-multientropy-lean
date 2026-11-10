import TreeGraph.Imbalance.NodeHeadTotalShearData
import TreeGraph.Imbalance.NodeHeadIndexSumBridge

namespace TreeGraph
namespace Imbalance

noncomputable def headChildRShearedFull
    (n : Nat) [NeZero n]
    (C : RTree) (_hC : RTree.PositiveWeights C) :
    BranchField n C →ₗ[F2]
      (Rep n → Module.Dual F2 (BoundaryField n C)) := by
  cases C with
  | node b ds =>
      refine
        { toFun := fun h α =>
            TreeGraph.dotLinear (Copen n (RTree.node b ds))
              (fun y =>
                ∑ x : Block n b,
                  if diag n b x +
                      copenTotalDiag n (RTree.node b ds) y = α then
                    h (x, y)
                  else
                    0)
          map_add' := ?_
          map_smul' := ?_ }
      · intro h k
        funext α
        apply LinearMap.ext
        intro μ
        change
          (∑ y : Copen n (RTree.node b ds), μ y *
            (∑ x : Block n b,
              if diag n b x +
                  copenTotalDiag n (RTree.node b ds) y = α then
                h (x, y) + k (x, y)
              else
                0)) =
            (∑ y : Copen n (RTree.node b ds), μ y *
              (∑ x : Block n b,
                if diag n b x +
                    copenTotalDiag n (RTree.node b ds) y = α then
                  h (x, y)
                else
                  0)) +
              ∑ y : Copen n (RTree.node b ds), μ y *
                (∑ x : Block n b,
                  if diag n b x +
                      copenTotalDiag n (RTree.node b ds) y = α then
                    k (x, y)
                  else
                    0)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [← mul_add]
        congr 1
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro x _
        by_cases hx :
            diag n b x + copenTotalDiag n (RTree.node b ds) y = α
        · simp [hx]
        · simp [hx]
      · intro r h
        funext α
        apply LinearMap.ext
        intro μ
        change
          (∑ y : Copen n (RTree.node b ds), μ y *
            (∑ x : Block n b,
              if diag n b x +
                  copenTotalDiag n (RTree.node b ds) y = α then
                r * h (x, y)
              else
                0)) =
            r *
              ∑ y : Copen n (RTree.node b ds), μ y *
                (∑ x : Block n b,
                  if diag n b x +
                      copenTotalDiag n (RTree.node b ds) y = α then
                    h (x, y)
                  else
                    0)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro y _
        have hinner :
            (∑ x : Block n b,
              if diag n b x +
                  copenTotalDiag n (RTree.node b ds) y = α then
                r * h (x, y)
              else
                0) =
              r * ∑ x : Block n b,
                if diag n b x +
                    copenTotalDiag n (RTree.node b ds) y = α then
                  h (x, y)
                else
                  0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x _
          by_cases hx :
              diag n b x + copenTotalDiag n (RTree.node b ds) y = α
          · simp [hx]
          · simp [hx]
        rw [hinner]
        ring

@[simp] theorem headChildRShearedFull_node_apply
    (n b : Nat) [NeZero n]
    (ds : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (h : BranchField n (RTree.node b ds)) (α : Rep n)
    (μ : BoundaryField n (RTree.node b ds)) :
    headChildRShearedFull n (RTree.node b ds) hC h α μ =
      ∑ y : Copen n (RTree.node b ds),
        μ y *
          (∑ x : Block n b,
            if diag n b x +
                copenTotalDiag n (RTree.node b ds) y = α then
              h (x, y)
            else
              0) := by
  rfl

noncomputable def headChildIndexShearedFullBoundaryCoeff
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
    (headChildRShearedFull n C hC)
    (headParentRootBranchFieldFromRoot n a C rest root)
    (headChildIndexTail idx, headChildIndexRootDiag idx)

theorem headChildIndexShearedFullBoundaryCoeff_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest)
    (μ : BoundaryField n C) :
    headChildIndexShearedFullBoundaryCoeff n a C rest hC P root idx μ =
      (headChildRShearedFull n C hC
          (headParentRootBranchFieldFromRoot n a C rest root
            (headChildIndexTail idx))
          (headChildIndexRootDiag idx) +
        headChildRShearedFull n C hC
          (headParentRootBranchFieldFromRoot n a C rest root
            (headChildIndexTail idx))
          (headChildIndexRootDiag idx + 1)) μ := by
  unfold headChildIndexShearedFullBoundaryCoeff branchMessageCoeff
  simp [familyCycDiff_apply, RtildeAbstract_apply]

noncomputable def headIndexShearedPhysicalPairWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest)
    (pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C) :
    ℤ :=
  weightClean C (closeOpenNormalAssignmentClean pair.1 pair.2) *
    chi (headChildIndexShearedFullBoundaryCoeff
      n a C rest hC P root idx
      (P.rootCopenBridge.linearEquiv pair.1))

theorem sum_rootMessageSubtype_eq_boundary_sum_for_dual
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

theorem sum_if_rootMessage_eq_boundary_sum_for_dual
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
          exact sum_rootMessageSubtype_eq_boundary_sum_for_dual
            n C hC P scalar f

theorem openPackage_pairSum_eq_messageSum_for_dual
    (n : Nat) [NeZero n]
    (C : RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (L : Module.Dual F2 (BoundaryField n C)) :
    (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
      weightClean C (closeOpenNormalAssignmentClean pair.1 pair.2) *
        chi (L (P.rootCopenBridge.linearEquiv pair.1))) =
      (2 : ℤ) ^ (Xdim n C - Ydim n C hC) *
        (∑ μ : P.boundaryMessageSpace, chi (L μ.1)) := by
  classical
  let scalar : ℤ := (2 : ℤ) ^ (Xdim n C - Ydim n C hC)
  calc
    (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
      weightClean C (closeOpenNormalAssignmentClean pair.1 pair.2) *
        chi (L (P.rootCopenBridge.linearEquiv pair.1))) =
        ∑ r : RootFieldAssignmentClean n C,
          (∑ Aopen : OpenNormalAssignmentClean n C,
            weightClean C (closeOpenNormalAssignmentClean r Aopen)) *
            chi (L (P.rootCopenBridge.linearEquiv r)) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [Finset.sum_mul]
    _ =
        ∑ r : RootFieldAssignmentClean n C,
          openNormalSignedSumClean n C r *
            chi (L (P.rootCopenBridge.linearEquiv r)) := by
          rfl
    _ =
        ∑ r : RootFieldAssignmentClean n C,
          if hr : r ∈ P.openBridge.rootMessageSpace then
            scalar *
              chi (L
                (P.rootMessageEquivBoundaryMessage ⟨r, hr⟩).1)
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
            simp [scalar, hr]
          · rw [P.openBridge.open_signed_sum_eq r]
            rw [if_neg hr]
            simp [hr]
    _ =
        scalar *
          ∑ μ : P.boundaryMessageSpace, chi (L μ.1) := by
          exact sum_if_rootMessage_eq_boundary_sum_for_dual
            n C hC P scalar
            (fun μ : P.boundaryMessageSpace => chi (L μ.1))
    _ =
        (2 : ℤ) ^ (Xdim n C - Ydim n C hC) *
          (∑ μ : P.boundaryMessageSpace, chi (L μ.1)) := by
          rfl

theorem headIndexShearedPhysicalPairSum_eq_messageSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest) :
    (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
      headIndexShearedPhysicalPairWeight n a C rest hC P root idx pair) =
        (2 : ℤ) ^ (Xdim n C - Ydim n C hC) *
          (∑ μ : P.boundaryMessageSpace,
            chi (headChildIndexShearedFullBoundaryCoeff
              n a C rest hC P root idx μ.1)) := by
  exact openPackage_pairSum_eq_messageSum_for_dual n C hC P
    (headChildIndexShearedFullBoundaryCoeff
      n a C rest hC P root idx)

end Imbalance
end TreeGraph
