import TreeGraph.Imbalance.NodeOpenHeadTailReindex
import TreeGraph.Imbalance.NodePackageRecursion

namespace TreeGraph
namespace Imbalance

theorem Xdim_sub_Ydim_node_eq_childContrib
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    Xdim n (RTree.node a cs) - Ydim n (RTree.node a cs) hT =
      XdimChildContrib n a cs 0 := by
  rw [Xdim_node_eq_Ydim_add_childContrib n a cs hT]
  exact Nat.add_sub_cancel_left
    (Ydim n (RTree.node a cs) hT)
    (XdimChildContrib n a cs 0)

theorem two_pow_Xdim_sub_Ydim_node_eq_childBranchScalarProduct
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    (2 : ℤ) ^ (Xdim n (RTree.node a cs) -
        Ydim n (RTree.node a cs) hT) =
      childBranchScalarProduct n a cs 0 := by
  rw [Xdim_sub_Ydim_node_eq_childContrib n a cs hT]
  rw [childBranchScalarProduct_eq_two_pow_contrib]

theorem two_pow_Xdim_sub_Ydim_node_cons_eq_head_mul_shiftedTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest))) :
    (2 : ℤ) ^ (Xdim n (RTree.node a (C :: rest)) -
        Ydim n (RTree.node a (C :: rest)) hT) =
      (2 : ℤ) ^ branchScalarExponent n a 0 C rest *
        (2 : ℤ) ^
          XdimChildContrib n a rest (RTree.totalWeight C) := by
  rw [Xdim_sub_Ydim_node_eq_childContrib n a (C :: rest) hT]
  rw [XdimChildContrib_cons_branchScalar]
  rw [pow_add]
  simp

theorem childBranchScalarProduct_cons_zero
    (n a : Nat) (C : RTree) (rest : List RTree) :
    childBranchScalarProduct n a (C :: rest) 0 =
      (2 : ℤ) ^ branchScalarExponent n a 0 C rest *
        childBranchScalarProduct n a rest (RTree.totalWeight C) := by
  rw [childBranchScalarProduct_cons]
  simp

theorem two_pow_Xdim_sub_Ydim_node_cons_eq_childBranchScalarProduct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest))) :
    (2 : ℤ) ^ (Xdim n (RTree.node a (C :: rest)) -
        Ydim n (RTree.node a (C :: rest)) hT) =
      (2 : ℤ) ^ branchScalarExponent n a 0 C rest *
        childBranchScalarProduct n a rest (RTree.totalWeight C) := by
  rw [two_pow_Xdim_sub_Ydim_node_cons_eq_head_mul_shiftedTail
    n a C rest hT]
  rw [childBranchScalarProduct_eq_two_pow_contrib]

theorem packageNodeNormalSum_eq_allowed_mul_openScalar
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    packageNodeNormalSum n a cs hT I =
      packageNodeAllowedSum n a cs hT I *
        (2 : ℤ) ^ (Xdim n (RTree.node a cs) -
          Ydim n (RTree.node a cs) hT) := by
  unfold packageNodeNormalSum
  rw [two_pow_Xdim_sub_Ydim_node_eq_childBranchScalarProduct]

theorem packageNodeNormalSum_cons_eq_allowed_mul_head_mul_shiftedTail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT) :
    packageNodeNormalSum n a (C :: rest) hT I =
      packageNodeAllowedSum n a (C :: rest) hT I *
        ((2 : ℤ) ^ branchScalarExponent n a 0 C rest *
          childBranchScalarProduct n a rest (RTree.totalWeight C)) := by
  unfold packageNodeNormalSum
  rw [childBranchScalarProduct_cons_zero]

end Imbalance
end TreeGraph
