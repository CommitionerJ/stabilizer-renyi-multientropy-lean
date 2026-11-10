import TreeGraph.Imbalance.NodeHeadIndexSumBridge

namespace TreeGraph
namespace Imbalance

noncomputable def headChildOpenDataFullBoundaryExponent
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) : F2 :=
  ∑ idx : HeadChildIndex n a rest,
    headChildIndexFullBoundaryCoeff n a C rest hC P root idx
      (P.rootCopenBridge.linearEquiv (data idx).1)

noncomputable def headChildOpenDataFullWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) : ℤ :=
  headChildOpenDataInternalWeight n a C rest data *
    chi (headChildOpenDataFullBoundaryExponent
      n a C rest hC P root data)

noncomputable def headChildOpenDataFullProductWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) : ℤ :=
  ∏ idx : HeadChildIndex n a rest,
    headIndexPhysicalPairWeight n a C rest hC P root idx (data idx)

theorem headChildOpenDataFullWeight_eq_prod_index
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataFullWeight n a C rest hC P root data =
      headChildOpenDataFullProductWeight n a C rest hC P root data := by
  classical
  unfold headChildOpenDataFullWeight headChildOpenDataFullProductWeight
    headChildOpenDataInternalWeight headChildOpenDataFullBoundaryExponent
    headIndexPhysicalPairWeight
  rw [chi_sum_univ_apply]
  rw [← Finset.prod_mul_distrib]

noncomputable def headChildOpenDataFullSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) : ℤ :=
  by
    classical
    letI : Fintype (HeadChildOpenData n a C rest) := Pi.instFintype
    exact
      ∑ data : HeadChildOpenData n a C rest,
        headChildOpenDataFullWeight n a C rest hC P root data

private theorem sum_pi_prod_factorized_full
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

theorem headChildOpenDataFullSignedSum_factorized
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataFullSignedSum n a C rest hC P root =
      ∏ idx : HeadChildIndex n a rest,
        ∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
          headIndexPhysicalPairWeight n a C rest hC P root idx pair := by
  classical
  let w :
      HeadChildIndex n a rest →
        RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C → ℤ :=
    fun idx pair =>
      headIndexPhysicalPairWeight n a C rest hC P root idx pair
  unfold headChildOpenDataFullSignedSum
  calc
    (∑ data : HeadChildOpenData n a C rest,
        headChildOpenDataFullWeight n a C rest hC P root data) =
        ∑ data : HeadChildOpenData n a C rest,
          ∏ idx : HeadChildIndex n a rest, w idx (data idx) := by
          refine Finset.sum_congr rfl ?_
          intro data _
          rw [headChildOpenDataFullWeight_eq_prod_index]
          rfl
    _ =
      ∏ idx : HeadChildIndex n a rest,
        ∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
          w idx pair := by
        exact sum_pi_prod_factorized_full w

theorem headChildOpenDataFullSignedSum_eq_descScalar_mul_messageSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataFullSignedSum n a C rest hC P root =
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
    headChildOpenDataFullSignedSum n a C rest hC P root =
        ∏ idx : HeadChildIndex n a rest,
          (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
            headIndexPhysicalPairWeight n a C rest hC P root idx pair) := by
          exact headChildOpenDataFullSignedSum_factorized
            n a C rest hC P root
    _ = ∏ idx : HeadChildIndex n a rest, scalar * S idx := by
          refine Finset.prod_congr rfl ?_
          intro idx _
          have hidx :=
            headIndexPhysicalPairSum_eq_messageSum
              n a C rest hC P root idx
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
