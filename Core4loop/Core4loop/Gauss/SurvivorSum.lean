import Core4loop.Gauss.DeltaAfterA

open scoped BigOperators

namespace Core4loop

lemma sum_if_mul_eq_mul_subtype {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (c : ℤ) (f : α → ℤ) :
    (∑ x : α, if p x then c * f x else 0) =
      c * ∑ x : {x // p x}, f x.1 := by
  classical
  calc
    (∑ x : α, if p x then c * f x else 0)
        = ∑ x ∈ (Finset.univ : Finset α) with p x, c * f x := by
            rw [Finset.sum_filter]
    _ = ∑ x : {x // p x}, c * f x.1 := by
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset α)) (p := p)
                (f := fun x => c * f x)).symm
    _ = c * ∑ x : {x // p x}, f x.1 := by
            rw [Finset.mul_sum]

theorem DeltaNF_triangleLeaf_survivors {n a b c d : ℕ} [NeZero n] :
    DeltaNF .triangleLeaf a b c d n =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ∑ x : Surviving_yzw n a b c d, bitSign (Q1 x.1.1 x.1.2.1) := by
  rw [DeltaNF_triangleLeaf_afterA]
  let scale : ℤ := (2 : ℤ) ^ (n ^ (b + c + d))
  let f : BFun4 n a c d × CFun4 n a b d × WFun4 n a b c → ℤ :=
    fun x => bitSign (Q1 x.1 x.2.1)
  let p : BFun4 n a c d × CFun4 n a b d × WFun4 n a b c → Prop :=
    fun x => K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) x = 0
  have hprod :
      (∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d, ∑ W : WFun4 n a b c,
        if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
        then scale * bitSign (Q1 B C)
        else 0)
      =
      ∑ x : BFun4 n a c d × CFun4 n a b d × WFun4 n a b c,
        if p x then scale * f x else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro B _
    rw [Fintype.sum_prod_type]
  rw [hprod, sum_if_mul_eq_mul_subtype p scale f]

theorem DeltaNF_square_survivors {n a b c d : ℕ} [NeZero n] :
    DeltaNF .square a b c d n =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ∑ x : Surviving_yw n a b c d,
          ∑ C : CFun4 n a b d, bitSign (Q2 x.1.1 C x.1.2) := by
  rw [DeltaNF_square_afterA]
  let scale : ℤ := (2 : ℤ) ^ (n ^ (b + c + d))
  let f : BFun4 n a c d × WFun4 n a b c → ℤ :=
    fun x => ∑ C : CFun4 n a b d, bitSign (Q2 x.1 C x.2)
  let p : BFun4 n a c d × WFun4 n a b c → Prop :=
    fun x => K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x = 0
  have hreorder :
      (∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d, ∑ W : WFun4 n a b c,
        if K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0
        then scale * bitSign (Q2 B C W)
        else 0)
      =
      ∑ x : BFun4 n a c d × WFun4 n a b c,
        if p x then scale * f x else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro B _
    rw [Finset.sum_comm]
    change
      (∑ W : WFun4 n a b c, ∑ C : CFun4 n a b d,
        if K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0
        then scale * bitSign (Q2 B C W)
        else 0)
      =
      ∑ W : WFun4 n a b c,
        if p (B, W) then scale * f (B, W) else 0
    refine Finset.sum_congr rfl ?_
    intro W _
    by_cases hK : p (B, W)
    · simp [p, f, hK, Finset.mul_sum]
    · simp [p, hK]
  rw [hreorder, sum_if_mul_eq_mul_subtype p scale f]

theorem DeltaNF_squareDiagonal_survivors {n a b c d : ℕ} [NeZero n] :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ∑ x : Surviving_yzw n a b c d, bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2) := by
  rw [DeltaNF_squareDiagonal_afterA]
  let scale : ℤ := (2 : ℤ) ^ (n ^ (b + c + d))
  let f : BFun4 n a c d × CFun4 n a b d × WFun4 n a b c → ℤ :=
    fun x => bitSign (Q3 x.1 x.2.1 x.2.2)
  let p : BFun4 n a c d × CFun4 n a b d × WFun4 n a b c → Prop :=
    fun x => K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) x = 0
  have hprod :
      (∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d, ∑ W : WFun4 n a b c,
        if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
        then scale * bitSign (Q3 B C W)
        else 0)
      =
      ∑ x : BFun4 n a c d × CFun4 n a b d × WFun4 n a b c,
        if p x then scale * f x else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro B _
    rw [Fintype.sum_prod_type]
  rw [hprod, sum_if_mul_eq_mul_subtype p scale f]

theorem DeltaNF_complete_survivors {n a b c d : ℕ} [NeZero n] :
    DeltaNF .complete a b c d n =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ∑ x : Surviving_yzw n a b c d, bitSign (Q4 x.1.1 x.1.2.1 x.1.2.2) := by
  rw [DeltaNF_complete_afterA]
  let scale : ℤ := (2 : ℤ) ^ (n ^ (b + c + d))
  let f : BFun4 n a c d × CFun4 n a b d × WFun4 n a b c → ℤ :=
    fun x => bitSign (Q4 x.1 x.2.1 x.2.2)
  let p : BFun4 n a c d × CFun4 n a b d × WFun4 n a b c → Prop :=
    fun x => K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) x = 0
  have hprod :
      (∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d, ∑ W : WFun4 n a b c,
        if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
        then scale * bitSign (Q4 B C W)
        else 0)
      =
      ∑ x : BFun4 n a c d × CFun4 n a b d × WFun4 n a b c,
        if p x then scale * f x else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro B _
    rw [Fintype.sum_prod_type]
  rw [hprod, sum_if_mul_eq_mul_subtype p scale f]

end Core4loop
