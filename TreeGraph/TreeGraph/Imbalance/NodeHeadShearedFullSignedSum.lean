import TreeGraph.Imbalance.NodeHeadShearedProjection

namespace TreeGraph
namespace Imbalance

noncomputable def headChildOpenDataShearedFullBoundaryExponent
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) : F2 :=
  ∑ idx : HeadChildIndex n a rest,
    headChildIndexShearedFullBoundaryCoeff n a C rest hC P root idx
      (P.rootCopenBridge.linearEquiv (data idx).1)

noncomputable def headChildOpenDataShearedFullWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) : ℤ :=
  headChildOpenDataInternalWeight n a C rest data *
    chi (headChildOpenDataShearedFullBoundaryExponent
      n a C rest hC P root data)

noncomputable def headChildOpenDataShearedFullProductWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) : ℤ :=
  ∏ idx : HeadChildIndex n a rest,
    headIndexShearedPhysicalPairWeight n a C rest hC P root idx (data idx)

theorem headChildOpenDataShearedFullWeight_eq_prod_index
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataShearedFullWeight n a C rest hC P root data =
      headChildOpenDataShearedFullProductWeight
        n a C rest hC P root data := by
  classical
  unfold headChildOpenDataShearedFullWeight
    headChildOpenDataShearedFullProductWeight
    headChildOpenDataInternalWeight
    headChildOpenDataShearedFullBoundaryExponent
    headIndexShearedPhysicalPairWeight
  rw [chi_sum_univ_apply]
  rw [← Finset.prod_mul_distrib]

noncomputable def headChildOpenDataShearedFullSignedSum
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
        headChildOpenDataShearedFullWeight n a C rest hC P root data

noncomputable def headShearedBranchMessageSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) : ℤ :=
  ∏ idx : HeadChildIndex n a rest,
    ∑ μ : P.boundaryMessageSpace,
      chi (headChildIndexShearedFullBoundaryCoeff
        n a C rest hC P root idx μ.1)

private theorem sum_pi_prod_factorized_sheared
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

theorem headChildOpenDataShearedFullSignedSum_factorized
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataShearedFullSignedSum n a C rest hC P root =
      ∏ idx : HeadChildIndex n a rest,
        ∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
          headIndexShearedPhysicalPairWeight n a C rest hC P root idx pair := by
  classical
  let w :
      HeadChildIndex n a rest →
        RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C → ℤ :=
    fun idx pair =>
      headIndexShearedPhysicalPairWeight n a C rest hC P root idx pair
  unfold headChildOpenDataShearedFullSignedSum
  calc
    (∑ data : HeadChildOpenData n a C rest,
        headChildOpenDataShearedFullWeight
          n a C rest hC P root data) =
        ∑ data : HeadChildOpenData n a C rest,
          ∏ idx : HeadChildIndex n a rest, w idx (data idx) := by
          refine Finset.sum_congr rfl ?_
          intro data _
          rw [headChildOpenDataShearedFullWeight_eq_prod_index]
          rfl
    _ =
      ∏ idx : HeadChildIndex n a rest,
        ∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
          w idx pair := by
        exact sum_pi_prod_factorized_sheared w

theorem headChildOpenDataShearedFullSignedSum_eq_descScalar_mul_shearedMessageSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataShearedFullSignedSum n a C rest hC P root =
      (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest hC *
        headShearedBranchMessageSignedSum n a C rest hC P root := by
  classical
  let scalar : ℤ := (2 : ℤ) ^ (Xdim n C - Ydim n C hC)
  let S : HeadChildIndex n a rest → ℤ := fun idx =>
    ∑ μ : P.boundaryMessageSpace,
      chi (headChildIndexShearedFullBoundaryCoeff
        n a C rest hC P root idx μ.1)
  have hpow :
      scalar ^ Fintype.card (HeadChildIndex n a rest) =
        (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest hC := by
    subst scalar
    rw [← pow_mul]
    rw [Nat.mul_comm (Xdim n C - Ydim n C hC)]
    rw [headChildOpenData_descendant_exponent_eq]
  calc
    headChildOpenDataShearedFullSignedSum n a C rest hC P root =
        ∏ idx : HeadChildIndex n a rest,
          (∑ pair : RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C,
            headIndexShearedPhysicalPairWeight n a C rest hC P root idx pair) := by
          exact headChildOpenDataShearedFullSignedSum_factorized
            n a C rest hC P root
    _ = ∏ idx : HeadChildIndex n a rest, scalar * S idx := by
          refine Finset.prod_congr rfl ?_
          intro idx _
          have hidx :=
            headIndexShearedPhysicalPairSum_eq_messageSum
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
          headShearedBranchMessageSignedSum n a C rest hC P root := by
          rfl

end Imbalance
end TreeGraph
