import TreeGraph.Imbalance.NodeHeadActualToFullSum
import TreeGraph.Imbalance.NodeHeadShearedFullSignedSum

namespace TreeGraph
namespace Imbalance

theorem headChildOpenDataShearedFullSignedSum_eq_sum_productWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataShearedFullSignedSum n a C rest hC P root =
      ∑ data : HeadChildOpenData n a C rest,
        headChildOpenDataShearedFullProductWeight
          n a C rest hC P root data := by
  classical
  unfold headChildOpenDataShearedFullSignedSum
  refine Finset.sum_congr rfl ?_
  intro data _
  exact headChildOpenDataShearedFullWeight_eq_prod_index
    n a C rest hC P root data

theorem parentActualHeadDataSignedSumAtTail_eq_shearedFullSignedSum_of_equiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataShearedFullProductWeight
            n a C rest hC P root (e data)) :
    parentActualHeadDataSignedSumAtTail n a C rest hC P root tail =
      headChildOpenDataShearedFullSignedSum n a C rest hC P root := by
  classical
  unfold parentActualHeadDataSignedSumAtTail
  rw [headChildOpenDataShearedFullSignedSum_eq_sum_productWeight]
  let F : HeadChildOpenData n a C rest → ℤ := fun data =>
    headChildOpenDataShearedFullProductWeight
      n a C rest hC P root data
  calc
    (∑ data : HeadChildOpenData n a C rest,
        parentActualHeadDataWeightAtTail
          n a C rest hC P root tail data) =
        ∑ data : HeadChildOpenData n a C rest, F (e data) := by
          refine Finset.sum_congr rfl ?_
          intro data _
          exact hweight data
    _ = ∑ data : HeadChildOpenData n a C rest, F data := by
          exact Equiv.sum_comp e F

theorem parentActualHeadDiagDataSignedSumAtTail_eq_shearedFullSignedSum_of_equiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDiagDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataShearedFullProductWeight
            n a C rest hC P root (e data)) :
    parentActualHeadDiagDataSignedSumAtTail n a C rest hC P root tail =
      headChildOpenDataShearedFullSignedSum n a C rest hC P root := by
  classical
  unfold parentActualHeadDiagDataSignedSumAtTail
  rw [headChildOpenDataShearedFullSignedSum_eq_sum_productWeight]
  let F : HeadChildOpenData n a C rest → ℤ := fun data =>
    headChildOpenDataShearedFullProductWeight
      n a C rest hC P root data
  calc
    (∑ data : HeadChildOpenData n a C rest,
        parentActualHeadDiagDataWeightAtTail
          n a C rest hC P root tail data) =
        ∑ data : HeadChildOpenData n a C rest, F (e data) := by
          refine Finset.sum_congr rfl ?_
          intro data _
          exact hweight data
    _ = ∑ data : HeadChildOpenData n a C rest, F data := by
          exact Equiv.sum_comp e F

theorem parentActualHeadPhaseSignedSumAtTail_eq_shearedFullSignedSum_of_equiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataShearedFullProductWeight
            n a C rest hC P root (e data)) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      headChildOpenDataShearedFullSignedSum n a C rest hC P root := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_dataSignedSum]
  exact parentActualHeadDataSignedSumAtTail_eq_shearedFullSignedSum_of_equiv
    n a C rest hC P root tail e hweight

theorem parentActualHeadPhaseSignedSumAtTail_eq_shearedFullSignedSum_of_diagEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDiagDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataShearedFullProductWeight
            n a C rest hC P root (e data)) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      headChildOpenDataShearedFullSignedSum n a C rest hC P root := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_diagDataSignedSum]
  exact parentActualHeadDiagDataSignedSumAtTail_eq_shearedFullSignedSum_of_equiv
    n a C rest hC P root tail e hweight

theorem parentActualHeadPhaseSignedSumAtTail_eq_descScalar_mul_shearedMessageSum_of_equiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataShearedFullProductWeight
            n a C rest hC P root (e data)) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest hC *
        headShearedBranchMessageSignedSum n a C rest hC P root := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_shearedFullSignedSum_of_equiv
    n a C rest hC P root tail e hweight]
  exact headChildOpenDataShearedFullSignedSum_eq_descScalar_mul_shearedMessageSum
    n a C rest hC P root

theorem parentActualHeadPhaseSignedSumAtTail_eq_descScalar_mul_shearedMessageSum_of_diagEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (e : HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : HeadChildOpenData n a C rest,
        parentActualHeadDiagDataWeightAtTail n a C rest hC P root tail data =
          headChildOpenDataShearedFullProductWeight
            n a C rest hC P root (e data)) :
    parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      (2 : ℤ) ^ branchDescendantScalarExponent n a 0 C rest hC *
        headShearedBranchMessageSignedSum n a C rest hC P root := by
  rw [parentActualHeadPhaseSignedSumAtTail_eq_shearedFullSignedSum_of_diagEquiv
    n a C rest hC P root tail e hweight]
  exact headChildOpenDataShearedFullSignedSum_eq_descScalar_mul_shearedMessageSum
    n a C rest hC P root

end Imbalance
end TreeGraph
