import TreeGraph.RecursiveCertificate

namespace TreeGraph

noncomputable def branchProductWith
    (Y : RTree → ℤ) (n : Nat) (cs : List RTree) : ℤ :=
  (cs.map (fun C =>
    (nZ n) ^ RTree.totalWeight C - (tZ n) * Y C)).prod

noncomputable def childContribSumWith
    (X : RTree → ℤ) (n a : Nat) : List RTree → Nat → ℤ
  | [], _ => 0
  | C :: rest, left =>
      let right := (rest.map RTree.totalWeight).sum
      let shift := a + left + right
      (nZ n) ^ shift * X C
        + childContribSumWith X n a rest (left + RTree.totalWeight C)

def SatisfiesAssignmentRecursion
    (n : Nat) (Y X : RTree → ℤ) : Prop :=
  ∀ (a : Nat) (cs : List RTree),
    Y (RTree.node a cs) = branchProductWith Y n cs ∧
      X (RTree.node a cs) =
        Y (RTree.node a cs) + childContribSumWith X n a cs 0

theorem branchProductWith_congr
    {Y Y' : RTree → ℤ} {n : Nat} :
    ∀ {cs : List RTree},
      (∀ C ∈ cs, Y C = Y' C) →
      branchProductWith Y n cs = branchProductWith Y' n cs
  | [], _ => by
      simp [branchProductWith]
  | C :: rest, h => by
      have hC : Y C = Y' C := h C (by simp)
      have hrest : ∀ D ∈ rest, Y D = Y' D := by
        intro D hD
        exact h D (by simp [hD])
      have htail :
          branchProductWith Y n rest = branchProductWith Y' n rest :=
        branchProductWith_congr hrest
      change
        ((nZ n) ^ RTree.totalWeight C - (tZ n) * Y C) *
            branchProductWith Y n rest =
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Y' C) *
            branchProductWith Y' n rest
      rw [hC, htail]

theorem childContribSumWith_congr
    {X X' : RTree → ℤ} {n a left : Nat} :
    ∀ {cs : List RTree},
      (∀ C ∈ cs, X C = X' C) →
      childContribSumWith X n a cs left =
        childContribSumWith X' n a cs left
  | [], _ => by
      simp [childContribSumWith]
  | C :: rest, h => by
      have hC : X C = X' C := h C (by simp)
      have hrest : ∀ D ∈ rest, X D = X' D := by
        intro D hD
        exact h D (by simp [hD])
      have htail :
          childContribSumWith X n a rest (left + RTree.totalWeight C) =
            childContribSumWith X' n a rest (left + RTree.totalWeight C) :=
        childContribSumWith_congr hrest
      change
        (nZ n) ^ (a + left + (rest.map RTree.totalWeight).sum) * X C +
            childContribSumWith X n a rest (left + RTree.totalWeight C) =
          (nZ n) ^ (a + left + (rest.map RTree.totalWeight).sum) * X' C +
            childContribSumWith X' n a rest (left + RTree.totalWeight C)
      rw [hC, htail]

theorem childContribSumWith_append
    (X : RTree → ℤ) (n a : Nat) :
    ∀ (left right : List RTree) (base : Nat),
      childContribSumWith X n a (left ++ right) base =
        childContribSumWith X n
            (a + (right.map RTree.totalWeight).sum) left base +
          childContribSumWith X n a right
            (base + (left.map RTree.totalWeight).sum)
  | [], right, base => by
      simp [childContribSumWith]
  | C :: rest, right, base => by
      have ih :=
        childContribSumWith_append X n a rest right
          (base + RTree.totalWeight C)
      simp [childContribSumWith, List.map_append, ih,
        Nat.add_comm, add_assoc]

theorem childContribSumWith_append_cons
    (X : RTree → ℤ) (n a : Nat)
    (left : List RTree) (C : RTree) (right : List RTree)
    (base : Nat) :
    childContribSumWith X n a (left ++ C :: right) base =
      childContribSumWith X n
          (a + RTree.totalWeight C + (right.map RTree.totalWeight).sum)
          left base +
        (nZ n) ^
            (a + (base + (left.map RTree.totalWeight).sum) +
              (right.map RTree.totalWeight).sum) * X C +
          childContribSumWith X n a right
            (base + (left.map RTree.totalWeight).sum +
              RTree.totalWeight C) := by
  rw [childContribSumWith_append]
  simp [childContribSumWith, Nat.add_comm, add_assoc]

theorem childContribSumWith_Xpoly
    (n a : Nat) :
    ∀ (cs : List RTree) (left : Nat),
      childContribSumWith (Xpoly n) n a cs left =
        childContribSum n a cs left
  | [], left => by
      simp [childContribSumWith, childContribSum]
  | C :: rest, left => by
      simp [childContribSumWith, childContribSum,
        childContribSumWith_Xpoly n a rest
          (left + RTree.totalWeight C)]

theorem assignmentRecursion_unique_pair
    {n : Nat} {Y X : RTree → ℤ}
    (hrec : SatisfiesAssignmentRecursion n Y X) :
    ∀ T : RTree, Y T = Ypoly n T ∧ X T = Xpoly n T := by
  intro T
  induction T using rootedTerms.induct with
  | case1 a cs ih =>
      have hYchildren : ∀ C ∈ cs, Y C = Ypoly n C := by
        intro C hC
        exact (ih C hC).1
      have hXchildren : ∀ C ∈ cs, X C = Xpoly n C := by
        intro C hC
        exact (ih C hC).2
      have hYnode :
          Y (RTree.node a cs) = Ypoly n (RTree.node a cs) := by
        calc
          Y (RTree.node a cs) = branchProductWith Y n cs :=
            (hrec a cs).1
          _ = branchProductWith (Ypoly n) n cs :=
            branchProductWith_congr hYchildren
          _ = Ypoly n (RTree.node a cs) := by
            simp [branchProductWith, Ypoly]
      have hXnode :
          X (RTree.node a cs) = Xpoly n (RTree.node a cs) := by
        calc
          X (RTree.node a cs) =
              Y (RTree.node a cs) + childContribSumWith X n a cs 0 :=
            (hrec a cs).2
          _ =
              Ypoly n (RTree.node a cs) +
                childContribSumWith (Xpoly n) n a cs 0 := by
            rw [hYnode, childContribSumWith_congr hXchildren]
          _ = Xpoly n (RTree.node a cs) := by
            rw [childContribSumWith_Xpoly n a cs 0]
            simp [Xpoly]
      exact ⟨hYnode, hXnode⟩

theorem assignmentRecursion_unique_Y
    {n : Nat} {Y X : RTree → ℤ}
    (hrec : SatisfiesAssignmentRecursion n Y X) (T : RTree) :
    Y T = Ypoly n T :=
  (assignmentRecursion_unique_pair hrec T).1

theorem assignmentRecursion_unique_X
    {n : Nat} {Y X : RTree → ℤ}
    (hrec : SatisfiesAssignmentRecursion n Y X) (T : RTree) :
    X T = Xpoly n T :=
  (assignmentRecursion_unique_pair hrec T).2

namespace RawPrimitive

def SignedSumRealizesAssignmentExponent
    (n : Nat) [NeZero n] (X : RTree → ℤ) : Prop :=
  ∀ T : RTree,
    RawNormal.signedSum n T = (2 : ℤ) ^ Int.toNat (X T)

theorem rawBitStringSignedSum_closed_Xpoly_of_assignmentRecursion
    {n : Nat} [NeZero n] {Y X : RTree → ℤ}
    (hrec : SatisfiesAssignmentRecursion n Y X)
    (hsigned : SignedSumRealizesAssignmentExponent n X)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    rawBitStringSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [rawBitStringSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := T) hT]
  rw [hsigned T]
  rw [assignmentRecursion_unique_X hrec T]

theorem rawBitStringSignedSum_closed_connected_terms_of_assignmentRecursion
    {n : Nat} [NeZero n] {Y X : RTree → ℤ}
    (hrec : SatisfiesAssignmentRecursion n Y X)
    (hsigned : SignedSumRealizesAssignmentExponent n X)
    {T : RTree} (hT : RTree.PositiveWeights T) :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [rawBitStringSignedSum_closed_Xpoly_of_assignmentRecursion
    (n := n) hrec hsigned hT]
  rw [Xpoly_eq_allTerms n T]

end RawPrimitive

end TreeGraph
