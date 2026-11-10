import TreeGraph.Imbalance.NodeHeadActualToShearedCanonical
import TreeGraph.Imbalance.NodeHeadShearedAllowed

namespace TreeGraph
namespace Imbalance

theorem parentActualHeadPhaseSignedSumAtTail_eq_if_headShearedAllowed_branchScalar_of_canonical
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (ha : 0 < a)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (hP : P.IsCanonical)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest) :
    parentActualHeadPhaseSignedSumAtTail
        n a (RTree.node b ds) rest root tail =
      (by
        classical
        exact
          if headParentRootBoundaryFieldFromRoot
              n a (RTree.node b ds) rest root ∈
              headShearedAllowedBoundarySpace
                n a (RTree.node b ds) rest hC P then
            (2 : ℤ) ^
              branchScalarExponent n a 0 (RTree.node b ds) rest
          else
            0) := by
  classical
  rw [
    actualHeadPhaseSum_eq_descScalar_mul_shearedMessageSum_of_canonical
      n a b ds rest hC P hP root tail]
  rw [
    headShearedBranchMessageSignedSum_eq_if_headShearedAllowed_branchScalar
      n a (RTree.node b ds) rest hC P root]
  by_cases hhead :
      headParentRootBoundaryFieldFromRoot n a (RTree.node b ds) rest root ∈
        headShearedAllowedBoundarySpace n a (RTree.node b ds) rest hC P
  · rw [if_pos hhead, if_pos hhead]
    rw [← pow_add]
    rw [branchScalarExponent_split n a 0 (RTree.node b ds) rest ha hC]
  · rw [if_neg hhead, if_neg hhead]
    rw [mul_zero]

theorem parentActualHeadPhaseSignedSumAtTail_of_head_shearedAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (ha : 0 < a)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (hP : P.IsCanonical)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest) :
    headParentRootBoundaryFieldFromRoot n a (RTree.node b ds) rest root ∈
        headShearedAllowedBoundarySpace n a (RTree.node b ds) rest hC P →
      parentActualHeadPhaseSignedSumAtTail
          n a (RTree.node b ds) rest root tail =
        (2 : ℤ) ^
          branchScalarExponent n a 0 (RTree.node b ds) rest := by
  intro hhead
  rw [
    parentActualHeadPhaseSignedSumAtTail_eq_if_headShearedAllowed_branchScalar_of_canonical
      n a b ds rest ha hC P hP root tail]
  rw [if_pos hhead]

theorem parentActualHeadPhaseSignedSumAtTail_of_head_notShearedAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (ha : 0 < a)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (hP : P.IsCanonical)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : ParentOpenTailFields n a (RTree.node b ds) rest) :
    headParentRootBoundaryFieldFromRoot n a (RTree.node b ds) rest root ∉
        headShearedAllowedBoundarySpace n a (RTree.node b ds) rest hC P →
      parentActualHeadPhaseSignedSumAtTail
          n a (RTree.node b ds) rest root tail = 0 := by
  intro hhead
  rw [
    parentActualHeadPhaseSignedSumAtTail_eq_if_headShearedAllowed_branchScalar_of_canonical
      n a b ds rest ha hC P hP root tail]
  rw [if_neg hhead]

end Imbalance
end TreeGraph
