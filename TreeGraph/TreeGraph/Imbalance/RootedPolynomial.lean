import TreeGraph.Imbalance.Rtilde

namespace TreeGraph
namespace Imbalance

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
      · have hle := ih h
        simp
        omega

private lemma numVertices_lt_node_of_mem
    {C : RTree} {a : Nat} {cs : List RTree} (h : C ∈ cs) :
    RTree.numVertices C < RTree.numVertices (RTree.node a cs) := by
  have hle := numVertices_le_sum_of_mem h
  simp [RTree.numVertices]
  omega

def branchAllowedDim (n A Y : Nat) : Nat :=
  n ^ A - (n - 1) * Y

theorem branchAllowedDim_cast_of_le
    {n A Y : Nat} [NeZero n]
    (h : (n - 1) * Y ≤ n ^ A) :
    ((branchAllowedDim n A Y : Nat) : ℤ) =
      (nZ n) ^ A - (tZ n) * (Y : ℤ) := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  unfold branchAllowedDim nZ tZ
  calc
    ((n ^ A - (n - 1) * Y : Nat) : ℤ) =
        ((n ^ A : Nat) : ℤ) - (((n - 1) * Y : Nat) : ℤ) := by
      exact Nat.cast_sub h
    _ = (n : ℤ) ^ A - (((n - 1 : Nat) : ℤ) * (Y : ℤ)) := by
      rw [Nat.cast_pow, Nat.cast_mul]
    _ = (n : ℤ) ^ A - ((n : ℤ) - 1) * (Y : ℤ) := by
      rw [Nat.cast_sub hn1]
      norm_num

noncomputable def YdimCandidate (n : Nat) : RTree → Nat
  | RTree.node _ cs =>
      (cs.map (fun C =>
        branchAllowedDim n (RTree.totalWeight C) (YdimCandidate n C))).prod
termination_by T => RTree.numVertices T
decreasing_by
  exact numVertices_lt_node_of_mem (by assumption)

@[simp] theorem YdimCandidate_leaf (n a : Nat) :
    YdimCandidate n (RTree.node a []) = 1 := by
  simp [YdimCandidate]

def childContribSumNatWith
    (X : RTree → Nat) (n a : Nat) : List RTree → Nat → Nat
  | [], _ => 0
  | C :: rest, left =>
      let right := (rest.map RTree.totalWeight).sum
      let shift := a + left + right
      n ^ shift * X C +
        childContribSumNatWith X n a rest (left + RTree.totalWeight C)

@[simp] theorem childContribSumNatWith_nil
    (X : RTree → Nat) (n a left : Nat) :
    childContribSumNatWith X n a [] left = 0 := by
  simp [childContribSumNatWith]

theorem childContribSumNatWith_cons
    (X : RTree → Nat) (n a : Nat) (C : RTree)
    (rest : List RTree) (left : Nat) :
    childContribSumNatWith X n a (C :: rest) left =
      n ^ (a + left + (rest.map RTree.totalWeight).sum) * X C +
        childContribSumNatWith X n a rest
          (left + RTree.totalWeight C) := by
  simp [childContribSumNatWith]

mutual
  noncomputable def XdimCandidate (n : Nat) : RTree → Nat
    | RTree.node a cs =>
        YdimCandidate n (RTree.node a cs) +
          XdimChildContrib n a cs 0

  noncomputable def XdimChildContrib
      (n : Nat) (a : Nat) : List RTree → Nat → Nat
    | [], _ => 0
    | C :: rest, left =>
        let right := (rest.map RTree.totalWeight).sum
        let shift := a + left + right
        n ^ shift * XdimCandidate n C +
          XdimChildContrib n a rest (left + RTree.totalWeight C)
end

@[simp] theorem XdimCandidate_leaf (n a : Nat) :
    XdimCandidate n (RTree.node a []) = 1 := by
  simp [XdimCandidate, XdimChildContrib]

theorem XdimCandidate_node (n a : Nat) (cs : List RTree) :
    XdimCandidate n (RTree.node a cs) =
      YdimCandidate n (RTree.node a cs) +
        XdimChildContrib n a cs 0 := by
  simp [XdimCandidate]

@[simp] theorem XdimChildContrib_nil (n a left : Nat) :
    XdimChildContrib n a [] left = 0 := by
  simp [XdimChildContrib]

theorem XdimChildContrib_cons
    (n a : Nat) (C : RTree) (rest : List RTree) (left : Nat) :
    XdimChildContrib n a (C :: rest) left =
      n ^ (a + left + (rest.map RTree.totalWeight).sum) *
          XdimCandidate n C +
        XdimChildContrib n a rest
          (left + RTree.totalWeight C) := by
  simp [XdimChildContrib]

theorem XdimChildContrib_eq_childContribSumNatWith
    (n a : Nat) : ∀ (cs : List RTree) (left : Nat),
    XdimChildContrib n a cs left =
      childContribSumNatWith (XdimCandidate n) n a cs left
  | [], left => by
      simp [XdimChildContrib, childContribSumNatWith]
  | C :: rest, left => by
      simp [XdimChildContrib, childContribSumNatWith,
        XdimChildContrib_eq_childContribSumNatWith n a rest]

noncomputable def YrecInt (n : Nat) (T : RTree) : ℤ :=
  Ypoly n T

noncomputable def XrecInt (n : Nat) (T : RTree) : ℤ :=
  Xpoly n T

@[simp] theorem YrecInt_leaf (n a : Nat) :
    YrecInt n (RTree.node a []) = 1 := by
  simp [YrecInt]

@[simp] theorem XrecInt_leaf (n a : Nat) :
    XrecInt n (RTree.node a []) = 1 := by
  simp [XrecInt]

theorem YrecInt_node (n a : Nat) (cs : List RTree) :
    YrecInt n (RTree.node a cs) =
      (cs.map (fun C =>
        (nZ n) ^ RTree.totalWeight C - (tZ n) * YrecInt n C)).prod := by
  simp [YrecInt, Ypoly]

theorem XrecInt_node (n a : Nat) (cs : List RTree) :
    XrecInt n (RTree.node a cs) =
      YrecInt n (RTree.node a cs) + childContribSum n a cs 0 := by
  simp [XrecInt, YrecInt, Xpoly]

-- The natural-exponent bridge is carried by RecursiveMessageSpace and
-- AssignmentRecursion, culminating in `rooted_tree_imbalance_formula`.

end Imbalance
end TreeGraph
