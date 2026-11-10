import TreeGraph.RawBranchConstraint

namespace TreeGraph

namespace RawPrimitive

private lemma numVertices_le_sum_of_mem {T : RTree} {ts : List RTree}
    (h : T ∈ ts) :
    RTree.numVertices T ≤ (ts.map RTree.numVertices).sum := by
  induction ts with
  | nil =>
      cases h
  | cons U us ih =>
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst h
        simp
      · have hlt := ih h
        simp
        omega

private lemma numVertices_lt_node_of_mem
    {C : RTree} {a : Nat} {cs : List RTree} (h : C ∈ cs) :
    RTree.numVertices C < RTree.numVertices (RTree.node a cs) := by
  have hle := numVertices_le_sum_of_mem h
  simp [RTree.numVertices]
  omega

noncomputable def Ydim (n : Nat) : RTree → Nat
  | RTree.node _ cs =>
      (cs.map (fun C =>
        branchConstraintExponent n (n ^ RTree.totalWeight C) (Ydim n C))).prod
termination_by T => RTree.numVertices T
decreasing_by
  exact numVertices_lt_node_of_mem (by assumption)

@[simp] theorem Ydim_leaf (n a : Nat) :
    Ydim n (RTree.node a []) = 1 := by
  simp [Ydim]

private theorem branchConstraintProduct_le_pow_sum
    (n : Nat) :
    ∀ cs : List RTree,
      (cs.map (fun C =>
        branchConstraintExponent n (n ^ RTree.totalWeight C) (Ydim n C))).prod ≤
        n ^ (cs.map RTree.totalWeight).sum
  | [] => by
      simp
  | C :: rest => by
      have hhead :
          branchConstraintExponent n (n ^ RTree.totalWeight C) (Ydim n C) ≤
            n ^ RTree.totalWeight C := by
        simp [branchConstraintExponent]
      have htail := branchConstraintProduct_le_pow_sum n rest
      have hmul := Nat.mul_le_mul hhead htail
      simpa [Nat.pow_add, Nat.mul_assoc] using hmul

theorem Ydim_le_pow_nonroot_weight (n : Nat) (T : RTree) :
    Ydim n T ≤ n ^ (RTree.totalWeight T - RTree.rootWeight T) := by
  cases T with
  | node a cs =>
      have h := branchConstraintProduct_le_pow_sum n cs
      simpa [Ydim, RTree.totalWeight, RTree.rootWeight] using h

theorem branchConstraintExponent_le_of_Ydim
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    (n - 1) * Ydim n T ≤ n ^ RTree.totalWeight T := by
  cases T with
  | node a cs =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      have hY := Ydim_le_pow_nonroot_weight n (RTree.node a cs)
      have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
      have hroot : n - 1 ≤ n ^ a := by
        have hna : n ≤ n ^ a := by
          simpa using le_self_pow hn (Nat.ne_of_gt hnode.1)
        exact le_trans (Nat.sub_le n 1) hna
      have hmul := Nat.mul_le_mul hroot hY
      simpa [RTree.totalWeight, RTree.rootWeight, Nat.pow_add]
        using hmul

private theorem branchConstraintProduct_cast_eq
    {n : Nat} [NeZero n] :
    ∀ {cs : List RTree},
      (∀ C ∈ cs,
        ((branchConstraintExponent n (n ^ RTree.totalWeight C)
          (Ydim n C) : Nat) : ℤ) =
            (nZ n) ^ RTree.totalWeight C - (tZ n) * Ypoly n C) →
      (((cs.map (fun C =>
        branchConstraintExponent n (n ^ RTree.totalWeight C)
          (Ydim n C))).prod : Nat) : ℤ) =
        (cs.map (fun C =>
          (nZ n) ^ RTree.totalWeight C - (tZ n) * Ypoly n C)).prod
  | [], _ => by
      simp
  | C :: rest, h => by
      have hC := h C (by simp)
      have hrest :
          ∀ D ∈ rest,
            ((branchConstraintExponent n (n ^ RTree.totalWeight D)
              (Ydim n D) : Nat) : ℤ) =
                (nZ n) ^ RTree.totalWeight D - (tZ n) * Ypoly n D := by
        intro D hD
        exact h D (by simp [hD])
      simpa [hC, branchConstraintProduct_cast_eq hrest]

theorem Ydim_cast_eq_Ypoly
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    ((Ydim n T : Nat) : ℤ) = Ypoly n T := by
  induction T using Ydim.induct with
  | case1 a cs ih =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      have hbranch :
          ∀ C ∈ cs,
            ((branchConstraintExponent n (n ^ RTree.totalWeight C)
              (Ydim n C) : Nat) : ℤ) =
                (nZ n) ^ RTree.totalWeight C - (tZ n) * Ypoly n C := by
        intro C hC
        have hCpos : RTree.PositiveWeights C := hnode.2 C hC
        have hle := branchConstraintExponent_le_of_Ydim (n := n) hCpos
        have hcast :=
          branchConstraintExponent_cast_pow
            (n := n) (A := RTree.totalWeight C) (Y := Ydim n C) hle
        have hY : ((Ydim n C : Nat) : ℤ) = Ypoly n C := ih C hC hCpos
        rw [hcast, hY]
      simpa [Ydim, Ypoly] using
        branchConstraintProduct_cast_eq (n := n) hbranch

theorem Ydim_cast_eq_Yassign
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    ((Ydim n T : Nat) : ℤ) = Yassign n T := by
  simpa [Yassign] using Ydim_cast_eq_Ypoly (n := n) hT

theorem branchConstraintExponent_cast_Ydim
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    ((branchConstraintExponent n (n ^ RTree.totalWeight T)
      (Ydim n T) : Nat) : ℤ) =
        (nZ n) ^ RTree.totalWeight T - (tZ n) * Yassign n T := by
  have hle := branchConstraintExponent_le_of_Ydim (n := n) hT
  have hcast :=
    branchConstraintExponent_cast_pow
      (n := n) (A := RTree.totalWeight T) (Y := Ydim n T) hle
  rw [hcast, Ydim_cast_eq_Yassign (n := n) hT]

theorem branchConstraintExponent_Ydim_toNat
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    Int.toNat
        ((nZ n) ^ RTree.totalWeight T - (tZ n) * Yassign n T) =
      branchConstraintExponent n (n ^ RTree.totalWeight T) (Ydim n T) := by
  rw [← branchConstraintExponent_cast_Ydim (n := n) hT]
  simp

end RawPrimitive

end TreeGraph
