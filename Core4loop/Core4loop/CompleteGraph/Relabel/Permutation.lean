import Core4loop.CompleteGraph.Relabel.Swap12Phase

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop

noncomputable section

/-- Swap the two non-root blocks B and C in a complete-graph normal form. -/
def k4Swap23NF
    {n a b c d : Nat} (nf : NF4 n a b c d) :
    NF4 n a c b d where
  A := fun y z w => nf.A z y w
  B := fun p s z w => nf.C p z s w
  C := fun p y s w => nf.B p s y w
  W := fun p y z s => nf.W p z y s

/-- The B/C field permutation is an involutive equivalence. -/
noncomputable def k4Swap23NFEquiv
    {n a b c d : Nat} :
    NF4 n a b c d ≃ NF4 n a c b d where
  toFun := k4Swap23NF
  invFun := k4Swap23NF
  left_inv := by
    rintro ⟨A, B, C, W⟩
    rfl
  right_inv := by
    rintro ⟨A, B, C, W⟩
    rfl

-- Literal read expansion is the shortest auditably pointwise proof.
set_option linter.flexible false in
private theorem localPhase_complete_swap23
    {n a b c d : Nat} [NeZero n] (nf : NF4 n a b c d)
    (p : PVec n a) (y : YVec n c) (z : ZVec n b) (w : WVec n d) :
    localPhase .complete (k4Swap23NF nf) p y z w =
      localPhase .complete nf p z y w := by
  simp [localPhase, alphaOf, betaOf, gammaOf, deltaOf, etaOf, xiOf,
    zetaOf, k4Swap23NF, disc]
  ring

set_option linter.flexible false in
/-- Swapping the non-root B/C blocks preserves the complete-graph phase. -/
theorem phaseExponentNF_complete_swap23
    {n a b c d : Nat} [NeZero n] (nf : NF4 n a b c d) :
    phaseExponentNF .complete (k4Swap23NF nf) =
      phaseExponentNF .complete nf := by
  unfold phaseExponentNF
  simp_rw [localPhase_complete_swap23]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]

/-- Raw complete-graph invariance under the B/C block swap. -/
theorem DeltaNF_complete_swap23
    {n a b c d : Nat} [NeZero n] :
    DeltaNF .complete a c b d n =
      DeltaNF .complete a b c d n := by
  unfold DeltaNF
  rw [← (k4Swap23NFEquiv (n := n) (a := a) (b := b) (c := c)
    (d := d)).sum_comp
      (fun nf => bitSign (phaseExponentNF .complete nf))]
  apply Finset.sum_congr rfl
  intro nf hnf
  change bitSign (phaseExponentNF .complete (k4Swap23NF nf)) =
    bitSign (phaseExponentNF .complete nf)
  rw [phaseExponentNF_complete_swap23]

/-- Swap the two non-root blocks C and W in a complete-graph normal form. -/
def k4Swap34NF
    {n a b c d : Nat} (nf : NF4 n a b c d) :
    NF4 n a b d c where
  A := fun y z w => nf.A y w z
  B := fun p s z w => nf.B p s w z
  C := fun p y s w => nf.W p y w s
  W := fun p y z s => nf.C p y s z

/-- The C/W field permutation is an involutive equivalence. -/
noncomputable def k4Swap34NFEquiv
    {n a b c d : Nat} :
    NF4 n a b c d ≃ NF4 n a b d c where
  toFun := k4Swap34NF
  invFun := k4Swap34NF
  left_inv := by
    rintro ⟨A, B, C, W⟩
    rfl
  right_inv := by
    rintro ⟨A, B, C, W⟩
    rfl

-- Literal read expansion is the shortest auditably pointwise proof.
set_option linter.flexible false in
private theorem localPhase_complete_swap34
    {n a b c d : Nat} [NeZero n] (nf : NF4 n a b c d)
    (p : PVec n a) (y : YVec n b) (z : ZVec n d) (w : WVec n c) :
    localPhase .complete (k4Swap34NF nf) p y z w =
      localPhase .complete nf p y w z := by
  simp [localPhase, alphaOf, betaOf, gammaOf, deltaOf, etaOf, xiOf,
    zetaOf, k4Swap34NF, disc]
  ring

set_option linter.flexible false in
/-- Swapping the non-root C/W blocks preserves the complete-graph phase. -/
theorem phaseExponentNF_complete_swap34
    {n a b c d : Nat} [NeZero n] (nf : NF4 n a b c d) :
    phaseExponentNF .complete (k4Swap34NF nf) =
      phaseExponentNF .complete nf := by
  unfold phaseExponentNF
  simp_rw [localPhase_complete_swap34]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]

/-- Raw complete-graph invariance under the C/W block swap. -/
theorem DeltaNF_complete_swap34
    {n a b c d : Nat} [NeZero n] :
    DeltaNF .complete a b d c n =
      DeltaNF .complete a b c d n := by
  unfold DeltaNF
  rw [← (k4Swap34NFEquiv (n := n) (a := a) (b := b) (c := c)
    (d := d)).sum_comp
      (fun nf => bitSign (phaseExponentNF .complete nf))]
  apply Finset.sum_congr rfl
  intro nf hnf
  change bitSign (phaseExponentNF .complete (k4Swap34NF nf)) =
    bitSign (phaseExponentNF .complete nf)
  rw [phaseExponentNF_complete_swap34]

/-- Raw complete-graph invariance under the root A/B reference change. -/
theorem DeltaNF_complete_swap12
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) :
    DeltaNF .complete b a c d n =
      DeltaNF .complete a b c d n := by
  unfold DeltaNF
  rw [← (k4Swap12NFEquiv (n := n) (a := a) (b := b) (c := c)
    (d := d) ha hb).sum_comp
      (fun nf => bitSign (phaseExponentNF .complete nf))]
  apply Finset.sum_congr rfl
  intro nf hnf
  change bitSign (phaseExponentNF .complete (k4Swap12NF ha hb nf)) =
    bitSign (phaseExponentNF .complete nf)
  rw [phaseExponentNF_complete_swap12]

/-- Move a positive B block to the chosen root. -/
theorem DeltaNF_complete_move_B_to_root
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) :
    DeltaNF .complete b a c d n =
      DeltaNF .complete a b c d n :=
  DeltaNF_complete_swap12 ha hb

/-- Move a positive C block to the chosen root using `(23)` then `(12)`. -/
theorem DeltaNF_complete_move_C_to_root
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) :
    DeltaNF .complete c a b d n =
      DeltaNF .complete a b c d n := by
  calc
    DeltaNF .complete c a b d n =
        DeltaNF .complete a c b d n :=
      DeltaNF_complete_swap12 ha hc
    _ = DeltaNF .complete a b c d n :=
      DeltaNF_complete_swap23

/-- Move a positive D block to the chosen root using `(34),(23),(12)`. -/
theorem DeltaNF_complete_move_D_to_root
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) :
    DeltaNF .complete d a b c n =
      DeltaNF .complete a b c d n := by
  calc
    DeltaNF .complete d a b c n =
        DeltaNF .complete a d b c n :=
      DeltaNF_complete_swap12 ha hd
    _ = DeltaNF .complete a b d c n :=
      DeltaNF_complete_swap23
    _ = DeltaNF .complete a b c d n :=
      DeltaNF_complete_swap34

end

end Core4loop
