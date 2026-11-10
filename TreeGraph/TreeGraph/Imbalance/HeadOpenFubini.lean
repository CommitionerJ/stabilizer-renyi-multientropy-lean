import TreeGraph.Imbalance.OpenPackageMessageEquiv
import TreeGraph.Imbalance.NodeHeadPhysicalReduction

namespace TreeGraph
namespace Imbalance

theorem headChildOpenDataRootMessage_eq_rootMessageEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (r : RootFieldAssignmentClean n C)
    (hr : r ∈ P.openBridge.rootMessageSpace) :
    headChildOpenDataRootMessage n a C rest hC P root r =
      P.rootMessageEquivBoundaryMessage ⟨r, hr⟩ := by
  apply Subtype.ext
  simp [headChildOpenDataRootMessage, hr,
    OpenNormalCleanPackage.rootMessageEquivBoundaryMessage_apply]

private theorem sum_rootMessageSubtype_eq_boundary_sum
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

private theorem sum_if_rootMessage_eq_boundary_sum
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
          exact sum_rootMessageSubtype_eq_boundary_sum n C hC P scalar f

theorem headChild_oneIndex_sum_eq
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (coeff : Module.Dual F2 P.boundaryMessageSpace) :
    (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
        weightClean C (closeOpenNormalAssignmentClean pair.1 pair.2) *
          chi (coeff
            (headChildOpenDataRootMessage n a C rest hC P root pair.1)))
      =
        (2 : ℤ) ^ (Xdim n C - Ydim n C hC) *
          (∑ μ : P.boundaryMessageSpace, chi (coeff μ)) := by
  classical
  let scalar : ℤ := (2 : ℤ) ^ (Xdim n C - Ydim n C hC)
  calc
    (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
        weightClean C (closeOpenNormalAssignmentClean pair.1 pair.2) *
          chi (coeff
            (headChildOpenDataRootMessage n a C rest hC P root pair.1))) =
        ∑ r : RootFieldAssignmentClean n C,
          (∑ Aopen : OpenNormalAssignmentClean n C,
            weightClean C (closeOpenNormalAssignmentClean r Aopen)) *
            chi (coeff
              (headChildOpenDataRootMessage n a C rest hC P root r)) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [Finset.sum_mul]
    _ =
        ∑ r : RootFieldAssignmentClean n C,
          openNormalSignedSumClean n C r *
            chi (coeff
              (headChildOpenDataRootMessage n a C rest hC P root r)) := by
          rfl
    _ =
        ∑ r : RootFieldAssignmentClean n C,
          if hr : r ∈ P.openBridge.rootMessageSpace then
            scalar *
              chi (coeff
                (P.rootMessageEquivBoundaryMessage ⟨r, hr⟩))
          else
            0 := by
          refine Finset.sum_congr rfl ?_
          intro r _
          by_cases hr : r ∈ P.openBridge.rootMessageSpace
          · rw [P.openBridge.open_signed_sum_eq r]
            rw [if_pos hr]
            rw [headChildOpenDataRootMessage_eq_rootMessageEquiv
              n a C rest hC P root r hr]
            simp [scalar, hr]
          · rw [P.openBridge.open_signed_sum_eq r]
            rw [if_neg hr]
            simp [hr]
    _ =
        scalar * ∑ μ : P.boundaryMessageSpace, chi (coeff μ) := by
          exact sum_if_rootMessage_eq_boundary_sum n C hC P scalar
            (fun μ : P.boundaryMessageSpace => chi (coeff μ))
    _ =
        (2 : ℤ) ^ (Xdim n C - Ydim n C hC) *
          (∑ μ : P.boundaryMessageSpace, chi (coeff μ)) := by
          rfl

noncomputable def headChildIndexBranchCoeff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest) :
    Module.Dual F2 P.boundaryMessageSpace :=
  branchMessageCoeff n
    (CoordsList n rest)
    (BranchField n C)
    P.boundaryMessageSpace
    (headChildR n C hC P)
    (headParentRootBranchFieldFromRoot n a C rest root)
    (headChildIndexTail idx, headChildIndexRootDiag idx)

private theorem chi_sum_finset
    {ι : Type} (s : Finset ι) (f : ι → F2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

theorem chi_sum_univ_apply
    {ι : Type} [Fintype ι] (f : ι → F2) :
    chi (∑ i, f i) = ∏ i, chi (f i) := by
  classical
  simpa using chi_sum_finset (Finset.univ : Finset ι) f

theorem headChildOpenDataBoundaryExponent_eq_sum_index
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataBoundaryExponent n a C rest hC P root data =
      ∑ idx : HeadChildIndex n a rest,
        headChildIndexBranchCoeff n a C rest hC P root idx
          (headChildOpenDataRootMessage
            n a C rest hC P root (data idx).1) := by
  classical
  unfold headChildOpenDataBoundaryExponent multiplicityExponent
    multiplicitySum headChildIndexBranchCoeff headChildIndexTail
    headChildIndexRootDiag
  let coeff :=
    branchMessageCoeff n (CoordsList n rest) (BranchField n C)
      P.boundaryMessageSpace (headChildR n C hC P)
      (headParentRootBranchFieldFromRoot n a C rest root)
  let msg : HeadChildIndex n a rest → P.boundaryMessageSpace := fun idx =>
    headChildOpenDataRootMessage n a C rest hC P root (data idx).1
  change
    (∑ et : CoordsList n rest × Rep n,
      coeff et (∑ q : Block n (a - 1), msg (q, et.1, et.2))) =
    ∑ idx : Block n (a - 1) × CoordsList n rest × Rep n,
      coeff (idx.2.1, idx.2.2) (msg idx)
  calc
    (∑ et : CoordsList n rest × Rep n,
      coeff et (∑ q : Block n (a - 1), msg (q, et.1, et.2))) =
        ∑ et : CoordsList n rest × Rep n,
          ∑ q : Block n (a - 1),
            coeff et (msg (q, et.1, et.2)) := by
          refine Finset.sum_congr rfl ?_
          intro et _
          rw [map_sum]
    _ =
        ∑ q : Block n (a - 1),
          ∑ et : CoordsList n rest × Rep n,
            coeff et (msg (q, et.1, et.2)) := by
          rw [Finset.sum_comm]
    _ =
        ∑ idx : Block n (a - 1) × CoordsList n rest × Rep n,
      coeff (idx.2.1, idx.2.2) (msg idx) := by
          rw [Fintype.sum_prod_type]

private theorem sum_pi_prod_factorized
    {ι α : Type} [DecidableEq ι] [Fintype ι] [Fintype α]
    (w : ι → α → ℤ) :
    (∑ f : ι → α, ∏ i : ι, w i (f i)) =
      ∏ i : ι, ∑ x : α, w i x := by
  classical
  have h :=
    Finset.prod_univ_sum
      (fun _ : ι => (Finset.univ : Finset α))
      (fun i x => w i x)
  simpa [Finset.univ_pi_univ] using h.symm

theorem sum_headChildOpenData_factorized
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataSignedSum n a C rest hC P root =
      ∏ idx : HeadChildIndex n a rest,
        (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
          weightClean C (closeOpenNormalAssignmentClean pair.1 pair.2) *
            chi (headChildIndexBranchCoeff n a C rest hC P root idx
              (headChildOpenDataRootMessage
                n a C rest hC P root pair.1))) := by
  classical
  let w :
      HeadChildIndex n a rest →
        RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C → ℤ :=
    fun idx pair =>
      weightClean C (closeOpenNormalAssignmentClean pair.1 pair.2) *
        chi (headChildIndexBranchCoeff n a C rest hC P root idx
          (headChildOpenDataRootMessage n a C rest hC P root pair.1))
  unfold headChildOpenDataSignedSum headChildOpenDataInternalWeight
  change
    (∑ data : HeadChildOpenData n a C rest,
      (∏ idx : HeadChildIndex n a rest,
        weightClean C (closeOpenNormalAssignmentClean
          (data idx).1 (data idx).2)) *
        chi (headChildOpenDataBoundaryExponent
          n a C rest hC P root data)) =
      ∏ idx : HeadChildIndex n a rest,
        ∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
          w idx pair
  calc
    (∑ data : HeadChildOpenData n a C rest,
      (∏ idx : HeadChildIndex n a rest,
        weightClean C (closeOpenNormalAssignmentClean
          (data idx).1 (data idx).2)) *
        chi (headChildOpenDataBoundaryExponent
          n a C rest hC P root data)) =
        ∑ data : HeadChildOpenData n a C rest,
          ∏ idx : HeadChildIndex n a rest, w idx (data idx) := by
          refine Finset.sum_congr rfl ?_
          intro data _
          rw [headChildOpenDataBoundaryExponent_eq_sum_index]
          rw [chi_sum_univ_apply]
          rw [← Finset.prod_mul_distrib]
    _ =
      ∏ idx : HeadChildIndex n a rest,
        ∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
          w idx pair := by
        exact sum_pi_prod_factorized w

theorem headBranchMessageExponent_eq_sum_index
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (μ : HeadChildIndex n a rest → P.boundaryMessageSpace) :
    multiplicityExponent n (Q := Block n (a - 1))
      (branchMessageCoeff n (CoordsList n rest) (BranchField n C)
        P.boundaryMessageSpace (headChildR n C hC P)
        (headParentRootBranchFieldFromRoot n a C rest root)) μ =
      ∑ idx : HeadChildIndex n a rest,
        headChildIndexBranchCoeff n a C rest hC P root idx (μ idx) := by
  classical
  unfold multiplicityExponent multiplicitySum headChildIndexBranchCoeff
    headChildIndexTail headChildIndexRootDiag
  let coeff :=
    branchMessageCoeff n (CoordsList n rest) (BranchField n C)
      P.boundaryMessageSpace (headChildR n C hC P)
      (headParentRootBranchFieldFromRoot n a C rest root)
  change
    (∑ et : CoordsList n rest × Rep n,
      coeff et (∑ q : Block n (a - 1), μ (q, et.1, et.2))) =
    ∑ idx : Block n (a - 1) × CoordsList n rest × Rep n,
      coeff (idx.2.1, idx.2.2) (μ idx)
  calc
    (∑ et : CoordsList n rest × Rep n,
      coeff et (∑ q : Block n (a - 1), μ (q, et.1, et.2))) =
        ∑ et : CoordsList n rest × Rep n,
          ∑ q : Block n (a - 1), coeff et (μ (q, et.1, et.2)) := by
          refine Finset.sum_congr rfl ?_
          intro et _
          rw [map_sum]
    _ =
        ∑ q : Block n (a - 1),
          ∑ et : CoordsList n rest × Rep n,
            coeff et (μ (q, et.1, et.2)) := by
          rw [Finset.sum_comm]
    _ =
        ∑ idx : Block n (a - 1) × CoordsList n rest × Rep n,
          coeff (idx.2.1, idx.2.2) (μ idx) := by
          rw [Fintype.sum_prod_type]

theorem headBranchMessageSignedSum_factorized
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headBranchMessageSignedSum n a C rest hC P root =
      ∏ idx : HeadChildIndex n a rest,
        ∑ μ : P.boundaryMessageSpace,
          chi (headChildIndexBranchCoeff n a C rest hC P root idx μ) := by
  classical
  let w : HeadChildIndex n a rest → P.boundaryMessageSpace → ℤ := fun idx μ =>
    chi (headChildIndexBranchCoeff n a C rest hC P root idx μ)
  unfold headBranchMessageSignedSum branchMessageSignedSum
  change
    (∑ μ : HeadChildIndex n a rest → P.boundaryMessageSpace,
      chi (multiplicityExponent n (Q := Block n (a - 1))
        (branchMessageCoeff n (CoordsList n rest) (BranchField n C)
          P.boundaryMessageSpace (headChildR n C hC P)
          (headParentRootBranchFieldFromRoot n a C rest root)) μ)) =
      ∏ idx : HeadChildIndex n a rest,
        ∑ μ : P.boundaryMessageSpace, w idx μ
  calc
    (∑ μ : HeadChildIndex n a rest → P.boundaryMessageSpace,
      chi (multiplicityExponent n (Q := Block n (a - 1))
        (branchMessageCoeff n (CoordsList n rest) (BranchField n C)
          P.boundaryMessageSpace (headChildR n C hC P)
          (headParentRootBranchFieldFromRoot n a C rest root)) μ)) =
        ∑ μ : HeadChildIndex n a rest → P.boundaryMessageSpace,
          ∏ idx : HeadChildIndex n a rest, w idx (μ idx) := by
          refine Finset.sum_congr rfl ?_
          intro μ _
          rw [headBranchMessageExponent_eq_sum_index]
          rw [chi_sum_univ_apply]
    _ = ∏ idx : HeadChildIndex n a rest,
        ∑ μ : P.boundaryMessageSpace, w idx μ := by
          exact sum_pi_prod_factorized w

theorem headChildOpenDataSignedSum_eq_descScalar_mul_messageSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataSignedSum n a C rest hC P root =
      (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest hC *
        headBranchMessageSignedSum n a C rest hC P root := by
  classical
  let scalar : ℤ := (2 : ℤ) ^ (Xdim n C - Ydim n C hC)
  let S : HeadChildIndex n a rest → ℤ := fun idx =>
    ∑ μ : P.boundaryMessageSpace,
      chi (headChildIndexBranchCoeff n a C rest hC P root idx μ)
  have hpow :
      scalar ^ Fintype.card (HeadChildIndex n a rest) =
        (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest hC := by
    subst scalar
    rw [← pow_mul]
    rw [Nat.mul_comm (Xdim n C - Ydim n C hC)]
    rw [headChildOpenData_descendant_exponent_eq]
  calc
    headChildOpenDataSignedSum n a C rest hC P root =
        ∏ idx : HeadChildIndex n a rest,
          (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
            weightClean C (closeOpenNormalAssignmentClean pair.1 pair.2) *
              chi (headChildIndexBranchCoeff n a C rest hC P root idx
                (headChildOpenDataRootMessage
                  n a C rest hC P root pair.1))) := by
          exact sum_headChildOpenData_factorized n a C rest hC P root
    _ = ∏ idx : HeadChildIndex n a rest, scalar * S idx := by
          refine Finset.prod_congr rfl ?_
          intro idx _
          have hidx :=
            headChild_oneIndex_sum_eq n a C rest hC P root
              (headChildIndexBranchCoeff n a C rest hC P root idx)
          simpa [scalar, S] using hidx
    _ = (∏ idx : HeadChildIndex n a rest, scalar) *
          ∏ idx : HeadChildIndex n a rest, S idx := by
          simpa using
            (Finset.prod_mul_distrib
              (s := (Finset.univ : Finset (HeadChildIndex n a rest)))
              (f := fun _ : HeadChildIndex n a rest => scalar)
              (g := S))
    _ = scalar ^ Fintype.card (HeadChildIndex n a rest) *
          ∏ idx : HeadChildIndex n a rest, S idx := by
          have hconst :
              (∏ idx : HeadChildIndex n a rest, scalar) =
                scalar ^ Fintype.card (HeadChildIndex n a rest) := by
            simp
          rw [hconst]
    _ = (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest hC *
          ∏ idx : HeadChildIndex n a rest, S idx := by
          rw [hpow]
    _ = (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest hC *
          headBranchMessageSignedSum n a C rest hC P root := by
          rw [← headBranchMessageSignedSum_factorized n a C rest hC P root]

end Imbalance
end TreeGraph
