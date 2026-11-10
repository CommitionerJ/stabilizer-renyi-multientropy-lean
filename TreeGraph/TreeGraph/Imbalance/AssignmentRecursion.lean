import TreeGraph.Imbalance.NormalForm

namespace TreeGraph
namespace Imbalance

noncomputable def childBranchScalarProduct
    (n a : Nat) : List RTree → Nat → ℤ
  | [], _ => 1
  | C :: rest, left =>
      (2 : ℤ) ^ branchScalarExponent n a left C rest *
        childBranchScalarProduct n a rest
          (left + RTree.totalWeight C)

@[simp] theorem childBranchScalarProduct_nil
    (n a left : Nat) :
    childBranchScalarProduct n a [] left = 1 := by
  simp [childBranchScalarProduct]

theorem childBranchScalarProduct_cons
    (n a left : Nat) (C : RTree) (rest : List RTree) :
    childBranchScalarProduct n a (C :: rest) left =
      (2 : ℤ) ^ branchScalarExponent n a left C rest *
        childBranchScalarProduct n a rest
          (left + RTree.totalWeight C) := by
  simp [childBranchScalarProduct]

theorem two_pow_XdimChildContrib_cons
    (n a left : Nat) (C : RTree) (rest : List RTree) :
    (2 : ℤ) ^ XdimChildContrib n a (C :: rest) left =
      (2 : ℤ) ^ branchScalarExponent n a left C rest *
        (2 : ℤ) ^ XdimChildContrib n a rest
          (left + RTree.totalWeight C) := by
  rw [XdimChildContrib_cons_branchScalar]
  rw [pow_add]

theorem childBranchScalarProduct_eq_two_pow_contrib
    (n a : Nat) : ∀ (cs : List RTree) (left : Nat),
    childBranchScalarProduct n a cs left =
      (2 : ℤ) ^ XdimChildContrib n a cs left
  | [], left => by
      simp [childBranchScalarProduct]
  | C :: rest, left => by
      rw [childBranchScalarProduct_cons]
      rw [childBranchScalarProduct_eq_two_pow_contrib n a rest]
      rw [two_pow_XdimChildContrib_cons]

noncomputable def childBranchScalarAssignments
    (n a : Nat) : List RTree → Nat → Type
  | [], _ => PUnit
  | C :: rest, left =>
      (Fin (branchScalarExponent n a left C rest) → F2) ×
        childBranchScalarAssignments n a rest
          (left + RTree.totalWeight C)

@[reducible] noncomputable instance childBranchScalarAssignmentsFintype
    (n a : Nat) : (cs : List RTree) → (left : Nat) →
      Fintype (childBranchScalarAssignments n a cs left)
  | [], _ => by
      change Fintype PUnit
      infer_instance
  | C :: rest, left => by
      change Fintype
        ((Fin (branchScalarExponent n a left C rest) → F2) ×
          childBranchScalarAssignments n a rest
            (left + RTree.totalWeight C))
      letI := childBranchScalarAssignmentsFintype n a rest
        (left + RTree.totalWeight C)
      infer_instance

theorem card_branchScalarBits (d : Nat) :
    Fintype.card (Fin d → F2) = 2 ^ d := by
  classical
  rw [Fintype.card_fun]
  simp [F2]

theorem childBranchScalarAssignments_card
    (n a : Nat) : ∀ (cs : List RTree) (left : Nat),
    ((Fintype.card (childBranchScalarAssignments n a cs left) : Nat) : ℤ) =
      childBranchScalarProduct n a cs left
  | [], _ => by
      change ((Fintype.card PUnit : Nat) : ℤ) = 1
      simp
  | C :: rest, left => by
      rw [childBranchScalarProduct_cons]
      change ((Fintype.card
        ((Fin (branchScalarExponent n a left C rest) → F2) ×
          childBranchScalarAssignments n a rest
            (left + RTree.totalWeight C)) : Nat) : ℤ) =
        (2 : ℤ) ^ branchScalarExponent n a left C rest *
          childBranchScalarProduct n a rest
            (left + RTree.totalWeight C)
      rw [Fintype.card_prod]
      rw [Nat.cast_mul]
      rw [childBranchScalarAssignments_card n a rest]
      have hbits :
          Fintype.card
              (Fin (branchScalarExponent n a left C rest) → F2) =
            2 ^ branchScalarExponent n a left C rest := by
        exact card_branchScalarBits
          (branchScalarExponent n a left C rest)
      rw [hbits]
      rw [Nat.cast_pow]
      norm_num

theorem childBranchScalarAssignments_card_eq_two_pow_contrib
    (n a : Nat) (cs : List RTree) (left : Nat) :
    ((Fintype.card (childBranchScalarAssignments n a cs left) : Nat) : ℤ) =
      (2 : ℤ) ^ XdimChildContrib n a cs left := by
  rw [childBranchScalarAssignments_card]
  rw [childBranchScalarProduct_eq_two_pow_contrib]

theorem two_pow_Xdim_node_factorization
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    (2 : ℤ) ^ Xdim n (RTree.node a cs) =
      (2 : ℤ) ^ Ydim n (RTree.node a cs) hT *
        (2 : ℤ) ^ XdimChildContrib n a cs 0 := by
  rw [Xdim_node_eq_Ydim_add_childContrib n a cs hT]
  rw [pow_add]

theorem assignmentRecursion_power_skeleton
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (hcs : ∀ C ∈ cs, RTree.PositiveWeights C) :
    (2 : ℤ) ^ Xdim n (RTree.node a cs) =
      allowedSignedSum
        (independentAllowed (childSliceFactors n cs hcs)) 0 *
        childBranchScalarProduct n a cs 0 := by
  rw [two_pow_Xdim_node_factorization n a cs hT]
  rw [Ydim_eq_YdimCandidate]
  rw [finalRootAllowed_zero_sum_node n a cs hcs]
  rw [childBranchScalarProduct_eq_two_pow_contrib]

theorem assignmentRecursion_power_skeleton_of_positive
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    (2 : ℤ) ^ Xdim n (RTree.node a cs) =
      allowedSignedSum
        (independentAllowed
          (childSliceFactors n cs (child_positive_of_node hT))) 0 *
        childBranchScalarProduct n a cs 0 := by
  exact assignmentRecursion_power_skeleton n a cs hT
    (child_positive_of_node hT)

noncomputable def abstractNodeNormalSum
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) : ℤ :=
  allowedSignedSum
    (independentAllowed
      (childSliceFactors n cs (child_positive_of_node hT))) 0 *
    childBranchScalarProduct n a cs 0

theorem abstractNodeNormalSum_eq_two_pow_Xdim
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    abstractNodeNormalSum n a cs hT =
      (2 : ℤ) ^ Xdim n (RTree.node a cs) := by
  unfold abstractNodeNormalSum
  rw [← assignmentRecursion_power_skeleton_of_positive n a cs hT]

noncomputable def abstractTreeNormalSum
    (n : Nat) [NeZero n] :
    (T : RTree) → RTree.PositiveWeights T → ℤ
  | RTree.node a cs, hT => abstractNodeNormalSum n a cs hT

noncomputable def DeltaNormal
    (n : Nat) [NeZero n] (T : RTree)
    (hT : RTree.PositiveWeights T) : ℤ :=
  abstractTreeNormalSum n T hT

theorem DeltaNormal_node
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    DeltaNormal n (RTree.node a cs) hT =
      abstractNodeNormalSum n a cs hT := rfl

theorem assignment_recursion
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    DeltaNormal n (RTree.node a cs) hT =
      allowedSignedSum
        (independentAllowed
          (childSliceFactors n cs (child_positive_of_node hT))) 0 *
        childBranchScalarProduct n a cs 0 := rfl

noncomputable def abstractNodeNormalAssignments
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) : Type :=
  independentAllowed
    (childSliceFactors n cs (child_positive_of_node hT)) ×
    childBranchScalarAssignments n a cs 0

@[reducible] noncomputable instance abstractNodeNormalAssignmentsFintype
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    Fintype (abstractNodeNormalAssignments n a cs hT) := by
  unfold abstractNodeNormalAssignments
  infer_instance

noncomputable def abstractNodeNormalPhase
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    abstractNodeNormalAssignments n a cs hT → F2 :=
  fun _ => 0

noncomputable def abstractNodeSignedSum
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) : ℤ :=
  signedCharacterSum (abstractNodeNormalAssignments n a cs hT)
    (abstractNodeNormalPhase n a cs hT)

theorem abstractNodeNormalAssignments_card
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    ((Fintype.card (abstractNodeNormalAssignments n a cs hT) : Nat) : ℤ) =
      (Fintype.card
        (independentAllowed
          (childSliceFactors n cs (child_positive_of_node hT))) : ℤ) *
        childBranchScalarProduct n a cs 0 := by
  have hcardAlias :
      Fintype.card (abstractNodeNormalAssignments n a cs hT) =
        Fintype.card
          (independentAllowed
              (childSliceFactors n cs (child_positive_of_node hT)) ×
            childBranchScalarAssignments n a cs 0) := by
    exact Fintype.card_congr (Equiv.refl _)
  rw [hcardAlias]
  rw [Fintype.card_prod]
  rw [Nat.cast_mul]
  rw [childBranchScalarAssignments_card]

theorem abstractNodeNormalAssignments_card_eq_two_pow_Xdim
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    ((Fintype.card (abstractNodeNormalAssignments n a cs hT) : Nat) : ℤ) =
      (2 : ℤ) ^ Xdim n (RTree.node a cs) := by
  rw [abstractNodeNormalAssignments_card]
  rw [← allowedSignedSum_zero_card]
  rw [finalRootAllowed_zero_sum_node_Ydim n a cs hT
    (child_positive_of_node hT)]
  rw [childBranchScalarProduct_eq_two_pow_contrib]
  rw [← pow_add]
  rw [Xdim_node_eq_Ydim_add_childContrib n a cs hT]

theorem abstractNodeSignedSum_eq_DeltaNormal
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    abstractNodeSignedSum n a cs hT =
      DeltaNormal n (RTree.node a cs) hT := by
  unfold abstractNodeSignedSum abstractNodeNormalPhase
  rw [signedCharacterSum_zero]
  rw [abstractNodeNormalAssignments_card]
  rw [← allowedSignedSum_zero_card]
  rfl

noncomputable def abstractTreeNormalAssignments
    (n : Nat) [NeZero n] :
    (T : RTree) → RTree.PositiveWeights T → Type
  | RTree.node a cs, hT => abstractNodeNormalAssignments n a cs hT

@[reducible] noncomputable instance abstractTreeNormalAssignmentsFintype
    (n : Nat) [NeZero n] (T : RTree)
    (hT : RTree.PositiveWeights T) :
    Fintype (abstractTreeNormalAssignments n T hT) := by
  cases T with
  | node a cs =>
      change Fintype (abstractNodeNormalAssignments n a cs hT)
      infer_instance

noncomputable def abstractTreeNormalPhase
    (n : Nat) [NeZero n] :
    (T : RTree) → (hT : RTree.PositiveWeights T) →
      abstractTreeNormalAssignments n T hT → F2
  | RTree.node a cs, hT => abstractNodeNormalPhase n a cs hT

noncomputable def abstractTreeSignedSum
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) : ℤ :=
  signedCharacterSum (abstractTreeNormalAssignments n T hT)
    (abstractTreeNormalPhase n T hT)

theorem abstractTreeSignedSum_eq_DeltaNormal
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    abstractTreeSignedSum n T hT = DeltaNormal n T hT := by
  cases T with
  | node a cs =>
      exact abstractNodeSignedSum_eq_DeltaNormal n a cs hT

theorem abstractTreeNormalAssignments_card_eq_DeltaNormal
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ((Fintype.card (abstractTreeNormalAssignments n T hT) : Nat) : ℤ) =
      DeltaNormal n T hT := by
  cases T with
  | node a cs =>
      change
        ((Fintype.card (abstractNodeNormalAssignments n a cs hT) : Nat) : ℤ) =
          DeltaNormal n (RTree.node a cs) hT
      rw [abstractNodeNormalAssignments_card]
      rw [← allowedSignedSum_zero_card]
      rfl

theorem abstract_rooted_tree_imbalance_formula
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    abstractTreeNormalSum n T hT = (2 : ℤ) ^ Xdim n T := by
  cases T with
  | node a cs =>
      exact abstractNodeNormalSum_eq_two_pow_Xdim n a cs hT

theorem rooted_tree_imbalance_formula
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    DeltaNormal n T hT = (2 : ℤ) ^ Xdim n T := by
  unfold DeltaNormal
  exact abstract_rooted_tree_imbalance_formula n T hT

theorem abstractTreeNormalAssignments_card_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ((Fintype.card (abstractTreeNormalAssignments n T hT) : Nat) : ℤ) =
      (2 : ℤ) ^ Xdim n T := by
  rw [abstractTreeNormalAssignments_card_eq_DeltaNormal]
  exact rooted_tree_imbalance_formula n T hT

theorem rooted_tree_signed_sum_imbalance_formula
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    abstractTreeSignedSum n T hT = (2 : ℤ) ^ Xdim n T := by
  rw [abstractTreeSignedSum_eq_DeltaNormal]
  exact rooted_tree_imbalance_formula n T hT

theorem phaseBridge_rooted_tree_imbalance_formula
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T)
    (Raw : Type) [Fintype Raw]
    (B : PhaseBridge Raw (abstractTreeNormalAssignments n T hT))
    (hnormal : ∀ F,
      B.normalPhase F = abstractTreeNormalPhase n T hT F) :
    B.rawSum = (2 : ℤ) ^ Xdim n T := by
  calc
    B.rawSum = B.normalSum := B.sum_eq
    _ = abstractTreeSignedSum n T hT := by
      unfold PhaseBridge.normalSum abstractTreeSignedSum
      exact signedCharacterSum_congr B.normalPhase
        (abstractTreeNormalPhase n T hT) hnormal
    _ = (2 : ℤ) ^ Xdim n T :=
      rooted_tree_signed_sum_imbalance_formula n T hT

theorem phaseBridge_rooted_tree_imbalance_formula_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T)
    (Raw : Type) [Fintype Raw]
    (B : PhaseBridge Raw (abstractTreeNormalAssignments n T hT))
    (hnormal : ∀ F,
      B.normalPhase F = abstractTreeNormalPhase n T hT F) :
    ∃ X : Nat,
      B.rawSum = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact phaseBridge_rooted_tree_imbalance_formula n T hT Raw B hnormal
  · exact Xdim_cast_eq_allTerms n T hT

theorem phaseBridge_rooted_tree_imbalance_formula_Xpoly
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T)
    (Raw : Type) [Fintype Raw]
    (B : PhaseBridge Raw (abstractTreeNormalAssignments n T hT))
    (hnormal : ∀ F,
      B.normalPhase F = abstractTreeNormalPhase n T hT F) :
    ∃ X : Nat,
      B.rawSum = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact phaseBridge_rooted_tree_imbalance_formula n T hT Raw B hnormal
  · exact Xdim_cast_eq_Xpoly n T hT

theorem abstract_rooted_tree_imbalance_formula_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      abstractTreeNormalSum n T hT = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact abstract_rooted_tree_imbalance_formula n T hT
  · exact Xdim_cast_eq_allTerms n T hT

theorem rooted_tree_imbalance_formula_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      DeltaNormal n T hT = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact rooted_tree_imbalance_formula n T hT
  · exact Xdim_cast_eq_allTerms n T hT

theorem rooted_tree_signed_sum_imbalance_formula_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      abstractTreeSignedSum n T hT = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact rooted_tree_signed_sum_imbalance_formula n T hT
  · exact Xdim_cast_eq_allTerms n T hT

theorem rooted_tree_imbalance_formula_Xpoly
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      DeltaNormal n T hT = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact rooted_tree_imbalance_formula n T hT
  · exact Xdim_cast_eq_Xpoly n T hT

theorem rooted_tree_signed_sum_imbalance_formula_Xpoly
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      abstractTreeSignedSum n T hT = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact rooted_tree_signed_sum_imbalance_formula n T hT
  · exact Xdim_cast_eq_Xpoly n T hT

end Imbalance
end TreeGraph
