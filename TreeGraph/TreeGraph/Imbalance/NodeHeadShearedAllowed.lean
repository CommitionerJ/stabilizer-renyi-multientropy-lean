import TreeGraph.Imbalance.NodeHeadShearedFullSignedSum
import TreeGraph.Imbalance.NodeHeadBranchCharacterSum

namespace TreeGraph
namespace Imbalance

noncomputable def headChildRSheared
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    BranchField n C →ₗ[F2]
      (Rep n → Module.Dual F2 P.boundaryMessageSpace) :=
  { toFun := fun h alpha =>
      (headChildRShearedFull n C hC h alpha).comp
        P.boundaryMessageSpace.subtype
    map_add' := by
      intro h k
      funext alpha
      ext mu
      simp
    map_smul' := by
      intro r h
      funext alpha
      ext mu
      simp }

@[simp] theorem headChildRSheared_apply
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (h : BranchField n C) (alpha : Rep n)
    (mu : P.boundaryMessageSpace) :
    headChildRSheared n C hC P h alpha mu =
      headChildRShearedFull n C hC h alpha mu.1 :=
  rfl

noncomputable def headChildIndexShearedBranchCoeff
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
    (headChildRSheared n C hC P)
    (headParentRootBranchFieldFromRoot n a C rest root)
    (headChildIndexTail idx, headChildIndexRootDiag idx)

theorem headChildIndexShearedFullBoundaryCoeff_restrict_message
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : HeadChildIndex n a rest) (mu : P.boundaryMessageSpace) :
    headChildIndexShearedFullBoundaryCoeff n a C rest hC P root idx mu.1 =
      headChildIndexShearedBranchCoeff n a C rest hC P root idx mu := by
  change
    (familyCycDiff n (CoordsList n rest)
      (Module.Dual F2 (BoundaryField n C))
      (RtildeAbstract n (CoordsList n rest) (BranchField n C)
        (BoundaryField n C)
        (headChildRShearedFull n C hC)
        (headParentRootBranchFieldFromRoot n a C rest root))
      (headChildIndexTail idx, headChildIndexRootDiag idx)) mu.1 =
    (familyCycDiff n (CoordsList n rest)
      (Module.Dual F2 P.boundaryMessageSpace)
      (RtildeAbstract n (CoordsList n rest) (BranchField n C)
        P.boundaryMessageSpace
        (headChildRSheared n C hC P)
        (headParentRootBranchFieldFromRoot n a C rest root))
      (headChildIndexTail idx, headChildIndexRootDiag idx)) mu
  simp only [familyCycDiff_apply, RtildeAbstract_apply]
  rfl

noncomputable def headShearedAllowedBoundarySpace
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Submodule F2 (BoundaryField n (RTree.node a (C :: rest))) :=
  (rtildeVisibleKernel n
      (CoordsList n rest)
      (BranchField n C)
      P.boundaryMessageSpace
      (headChildRSheared n C hC P)).comap
    (boundaryHeadSliceLinearEquiv n a C rest).toLinearMap

noncomputable def headShearedBranchMessageSignedSumBranch
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) : ℤ :=
  by
    classical
    letI : Fintype P.boundaryMessageSpace :=
      Fintype.ofFinite P.boundaryMessageSpace
    exact
      branchMessageSignedSum n
        (Block n (a - 1))
        (CoordsList n rest)
        (BranchField n C)
        P.boundaryMessageSpace
        (headChildRSheared n C hC P)
        (headParentRootBranchFieldFromRoot n a C rest root)

theorem headParentRootBranch_mem_shearedKernel_iff_headShearedAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBranchFieldFromRoot n a C rest root ∈
        rtildeVisibleKernel n (CoordsList n rest)
          (BranchField n C) P.boundaryMessageSpace
          (headChildRSheared n C hC P) ↔
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headShearedAllowedBoundarySpace n a C rest hC P := by
  rfl

private theorem sum_pi_prod_factorized_sheared_branch
    {iota alpha : Type} [DecidableEq iota] [Fintype iota] [Fintype alpha]
    (w : iota → alpha → ℤ) :
    (∑ f : iota → alpha, ∏ i : iota, w i (f i)) =
      ∏ i : iota, ∑ x : alpha, w i x := by
  classical
  have h :=
    Finset.prod_univ_sum
      (fun _ : iota => (Finset.univ : Finset alpha))
      (fun i x => w i x)
  simpa [Finset.univ_pi_univ] using h.symm

theorem headShearedBranchMessageExponent_eq_sum_index
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (mu : HeadChildIndex n a rest → P.boundaryMessageSpace) :
    multiplicityExponent n (Q := Block n (a - 1))
      (branchMessageCoeff n (CoordsList n rest) (BranchField n C)
        P.boundaryMessageSpace (headChildRSheared n C hC P)
        (headParentRootBranchFieldFromRoot n a C rest root)) mu =
      ∑ idx : HeadChildIndex n a rest,
        headChildIndexShearedBranchCoeff n a C rest hC P root idx
          (mu idx) := by
  classical
  unfold multiplicityExponent multiplicitySum
    headChildIndexShearedBranchCoeff headChildIndexTail
    headChildIndexRootDiag
  let coeff :=
    branchMessageCoeff n (CoordsList n rest) (BranchField n C)
      P.boundaryMessageSpace (headChildRSheared n C hC P)
      (headParentRootBranchFieldFromRoot n a C rest root)
  change
    (∑ et : CoordsList n rest × Rep n,
      coeff et (∑ q : Block n (a - 1), mu (q, et.1, et.2))) =
    ∑ idx : Block n (a - 1) × CoordsList n rest × Rep n,
      coeff (idx.2.1, idx.2.2) (mu idx)
  calc
    (∑ et : CoordsList n rest × Rep n,
      coeff et (∑ q : Block n (a - 1), mu (q, et.1, et.2))) =
        ∑ et : CoordsList n rest × Rep n,
          ∑ q : Block n (a - 1), coeff et (mu (q, et.1, et.2)) := by
          refine Finset.sum_congr rfl ?_
          intro et _
          rw [map_sum]
    _ =
        ∑ q : Block n (a - 1),
          ∑ et : CoordsList n rest × Rep n,
            coeff et (mu (q, et.1, et.2)) := by
          rw [Finset.sum_comm]
    _ =
        ∑ idx : Block n (a - 1) × CoordsList n rest × Rep n,
          coeff (idx.2.1, idx.2.2) (mu idx) := by
          rw [Fintype.sum_prod_type]

theorem headShearedBranchMessageSignedSumBranch_factorized
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headShearedBranchMessageSignedSumBranch n a C rest hC P root =
      ∏ idx : HeadChildIndex n a rest,
        ∑ mu : P.boundaryMessageSpace,
          chi (headChildIndexShearedBranchCoeff n a C rest hC P root idx
            mu) := by
  classical
  letI : Fintype P.boundaryMessageSpace :=
    Fintype.ofFinite P.boundaryMessageSpace
  let w : HeadChildIndex n a rest → P.boundaryMessageSpace → ℤ :=
    fun idx mu =>
      chi (headChildIndexShearedBranchCoeff n a C rest hC P root idx mu)
  unfold headShearedBranchMessageSignedSumBranch branchMessageSignedSum
  change
    (∑ mu : HeadChildIndex n a rest → P.boundaryMessageSpace,
      chi (multiplicityExponent n (Q := Block n (a - 1))
        (branchMessageCoeff n (CoordsList n rest) (BranchField n C)
          P.boundaryMessageSpace (headChildRSheared n C hC P)
          (headParentRootBranchFieldFromRoot n a C rest root)) mu)) =
      ∏ idx : HeadChildIndex n a rest,
        ∑ mu : P.boundaryMessageSpace, w idx mu
  calc
    (∑ mu : HeadChildIndex n a rest → P.boundaryMessageSpace,
      chi (multiplicityExponent n (Q := Block n (a - 1))
        (branchMessageCoeff n (CoordsList n rest) (BranchField n C)
          P.boundaryMessageSpace (headChildRSheared n C hC P)
          (headParentRootBranchFieldFromRoot n a C rest root)) mu)) =
        ∑ mu : HeadChildIndex n a rest → P.boundaryMessageSpace,
          ∏ idx : HeadChildIndex n a rest, w idx (mu idx) := by
          refine Finset.sum_congr rfl ?_
          intro mu _
          rw [headShearedBranchMessageExponent_eq_sum_index]
          rw [chi_sum_univ_apply]
    _ = ∏ idx : HeadChildIndex n a rest,
        ∑ mu : P.boundaryMessageSpace, w idx mu := by
          exact sum_pi_prod_factorized_sheared_branch w

theorem headShearedBranchMessageSignedSumBranch_eq_product
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headShearedBranchMessageSignedSumBranch n a C rest hC P root =
      headShearedBranchMessageSignedSum n a C rest hC P root := by
  classical
  letI : Fintype P.boundaryMessageSpace :=
    Fintype.ofFinite P.boundaryMessageSpace
  rw [headShearedBranchMessageSignedSumBranch_factorized]
  unfold headShearedBranchMessageSignedSum
  refine Finset.prod_congr rfl ?_
  intro idx _
  refine Finset.sum_congr rfl ?_
  intro mu _
  rw [headChildIndexShearedFullBoundaryCoeff_restrict_message]

theorem headShearedBranchMessageSignedSum_eq_if_headShearedAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headShearedBranchMessageSignedSum n a C rest hC P root =
      (by
        classical
        exact
          if headParentRootBoundaryFieldFromRoot n a C rest root ∈
              headShearedAllowedBoundarySpace n a C rest hC P then
            (2 : ℤ) ^
              (Fintype.card (Block n (a - 1)) *
                Fintype.card (CoordsList n rest) * n *
                Module.finrank F2 P.boundaryMessageSpace)
          else
            0) := by
  classical
  letI : Fintype P.boundaryMessageSpace :=
    Fintype.ofFinite P.boundaryMessageSpace
  by_cases hhead :
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headShearedAllowedBoundarySpace n a C rest hC P
  · have hbranch :
        headParentRootBranchFieldFromRoot n a C rest root ∈
          rtildeVisibleKernel n (CoordsList n rest)
            (BranchField n C) P.boundaryMessageSpace
            (headChildRSheared n C hC P) :=
      (headParentRootBranch_mem_shearedKernel_iff_headShearedAllowed
        n a C rest hC P root).2 hhead
    have hsum :=
      branchMessageSignedSum_of_mem n
        (Block n (a - 1))
        (CoordsList n rest)
        (BranchField n C)
        P.boundaryMessageSpace
        (headChildRSheared n C hC P)
        (headParentRootBranchFieldFromRoot n a C rest root)
        hbranch
    have hprod :=
      headShearedBranchMessageSignedSumBranch_eq_product
        n a C rest hC P root
    rw [← hprod]
    simpa [headShearedBranchMessageSignedSumBranch, hhead] using hsum
  · have hbranch :
        headParentRootBranchFieldFromRoot n a C rest root ∉
          rtildeVisibleKernel n (CoordsList n rest)
            (BranchField n C) P.boundaryMessageSpace
            (headChildRSheared n C hC P) := by
      intro hmem
      exact hhead
        ((headParentRootBranch_mem_shearedKernel_iff_headShearedAllowed
          n a C rest hC P root).1 hmem)
    have hsum :=
      branchMessageSignedSum_of_not_mem n
        (Block n (a - 1))
        (CoordsList n rest)
        (BranchField n C)
        P.boundaryMessageSpace
        (headChildRSheared n C hC P)
        (headParentRootBranchFieldFromRoot n a C rest root)
        hbranch
    have hprod :=
      headShearedBranchMessageSignedSumBranch_eq_product
        n a C rest hC P root
    rw [← hprod]
    simpa [headShearedBranchMessageSignedSumBranch, hhead] using hsum

theorem headShearedBranchMessageSignedSum_eq_if_headShearedAllowed_branchScalar
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headShearedBranchMessageSignedSum n a C rest hC P root =
      (by
        classical
        exact
          if headParentRootBoundaryFieldFromRoot n a C rest root ∈
              headShearedAllowedBoundarySpace n a C rest hC P then
            (2 : ℤ) ^ branchMessageScalarExponent n a 0 C rest hC
          else
            0) := by
  rw [headShearedBranchMessageSignedSum_eq_if_headShearedAllowed]
  rw [headBranchMessageExponent_eq_branchMessageScalarExponent]

theorem headShearedBranchMessageSignedSum_of_head_notShearedAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBoundaryFieldFromRoot n a C rest root ∉
        headShearedAllowedBoundarySpace n a C rest hC P →
      headShearedBranchMessageSignedSum n a C rest hC P root = 0 := by
  intro hhead
  simpa [hhead] using
    headShearedBranchMessageSignedSum_eq_if_headShearedAllowed_branchScalar
      n a C rest hC P root

end Imbalance
end TreeGraph
