import Core4loop.Gauss.PhaseSplit

open scoped BigOperators

namespace Core4loop

theorem DeltaNF_eq_sum_components {n a b c d : ℕ} [NeZero n] (G : CoreGraph) :
    DeltaNF G a b c d n =
      ∑ A : AFun4 n b c d,
        ∑ B : BFun4 n a c d,
          ∑ C : CFun4 n a b d,
            ∑ W : WFun4 n a b c,
              bitSign (phaseExponentNF G
                ({ A := A, B := B, C := C, W := W } : NF4 n a b c d)) := by
  unfold DeltaNF
  let e := nf4EquivProd n a b c d
  calc
    (∑ nf : NF4 n a b c d, bitSign (phaseExponentNF G nf))
        = ∑ x : AFun4 n b c d × BFun4 n a c d × CFun4 n a b d × WFun4 n a b c,
            bitSign (phaseExponentNF G (e.symm x)) := by
            exact Fintype.sum_equiv e
              (fun nf : NF4 n a b c d => bitSign (phaseExponentNF G nf))
              (fun x : AFun4 n b c d × BFun4 n a c d × CFun4 n a b d × WFun4 n a b c =>
                bitSign (phaseExponentNF G (e.symm x)))
              (fun nf => by simp [e])
    _ = ∑ A : AFun4 n b c d,
        ∑ B : BFun4 n a c d,
          ∑ C : CFun4 n a b d,
            ∑ W : WFun4 n a b c,
              bitSign (phaseExponentNF G
                ({ A := A, B := B, C := C, W := W } : NF4 n a b c d)) := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro A _
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro B _
            rw [Fintype.sum_prod_type]
            rfl

theorem DeltaNF_triangleLeaf_afterA {n a b c d : ℕ} [NeZero n] :
    DeltaNF .triangleLeaf a b c d n =
      ∑ B : BFun4 n a c d,
        ∑ C : CFun4 n a b d,
          ∑ W : WFun4 n a b c,
            if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
            then (2 : ℤ) ^ (n ^ (b + c + d)) * bitSign (Q1 B C)
            else 0 := by
  rw [DeltaNF_eq_sum_components]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro B _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro C _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro W _
  exact sum_A_triangleLeaf_afterA B C W

theorem DeltaNF_square_afterA {n a b c d : ℕ} [NeZero n] :
    DeltaNF .square a b c d n =
      ∑ B : BFun4 n a c d,
        ∑ C : CFun4 n a b d,
          ∑ W : WFun4 n a b c,
            if K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0
            then (2 : ℤ) ^ (n ^ (b + c + d)) * bitSign (Q2 B C W)
            else 0 := by
  rw [DeltaNF_eq_sum_components]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro B _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro C _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro W _
  exact sum_A_square_afterA B C W

theorem DeltaNF_squareDiagonal_afterA {n a b c d : ℕ} [NeZero n] :
    DeltaNF .squareDiagonal a b c d n =
      ∑ B : BFun4 n a c d,
        ∑ C : CFun4 n a b d,
          ∑ W : WFun4 n a b c,
            if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
            then (2 : ℤ) ^ (n ^ (b + c + d)) * bitSign (Q3 B C W)
            else 0 := by
  rw [DeltaNF_eq_sum_components]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro B _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro C _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro W _
  exact sum_A_squareDiagonal_afterA B C W

theorem DeltaNF_complete_afterA {n a b c d : ℕ} [NeZero n] :
    DeltaNF .complete a b c d n =
      ∑ B : BFun4 n a c d,
        ∑ C : CFun4 n a b d,
          ∑ W : WFun4 n a b c,
            if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
            then (2 : ℤ) ^ (n ^ (b + c + d)) * bitSign (Q4 B C W)
            else 0 := by
  rw [DeltaNF_eq_sum_components]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro B _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro C _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro W _
  exact sum_A_complete_afterA B C W

end Core4loop
