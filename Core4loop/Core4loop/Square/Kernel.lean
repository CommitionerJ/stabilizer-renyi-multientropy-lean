import Core4loop.Square.Linear
import Core4loop.RootSpaces.KernelRank

open scoped BigOperators

namespace Core4loop

noncomputable def SquareCombined {n a b c d : ℕ} [NeZero n] :
    (BFun4 n a c d × WFun4 n a b c) →ₗ[F]
      (RootTarget n b c d × CFun4 n a b d) :=
  LinearMap.prod
    (K_yw (n := n) (a := a) (b := b) (c := c) (d := d))
    (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable abbrev SquareCombinedKernel (n a b c d : ℕ) [NeZero n] :=
  LinearMap.ker (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def squareSurvivorCompatEquivKernel {n a b c d : ℕ} [NeZero n] :
    { x : Surviving_yw n a b c d //
        squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1 = 0 } ≃
      SquareCombinedKernel n a b c d where
  toFun x :=
    ⟨x.1.1, by
      apply LinearMap.mem_ker.mpr
      exact Prod.ext x.1.2 x.2⟩
  invFun x :=
    ⟨⟨x.1, by
        have hx := LinearMap.mem_ker.mp x.2
        exact congrArg Prod.fst hx⟩,
      by
        have hx := LinearMap.mem_ker.mp x.2
        exact congrArg Prod.snd hx⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The kernel is a submodule of a nested product of finite function spaces.
theorem natCard_SquareCombinedKernel {n a b c d : ℕ} [NeZero n] :
    Nat.card (SquareCombinedKernel n a b c d) =
      2 ^ Module.finrank F (SquareCombinedKernel n a b c d) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

theorem finrank_range_SquareCombined_add_kernel {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) :
    Module.finrank F
        (LinearMap.range
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)))
      + Module.finrank F (SquareCombinedKernel n a b c d)
      =
      n ^ (a + c + d) + n ^ (a + b + c) := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d))
  rw [finrank_domain_K_yw (n := n) (a := a) (b := b) (c := c) (d := d) ha] at h
  exact h

theorem DeltaNF_square_kernel_count {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) :
    DeltaNF .square a b c d n =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ((2 : ℤ) ^ (n ^ (a + b + d)) *
          (Nat.card (SquareCombinedKernel n a b c d) : ℤ)) := by
  classical
  rw [DeltaNF_square_survivors]
  let scaleC : ℤ := (2 : ℤ) ^ (n ^ (a + b + d))
  have hsum :
      (∑ x : Surviving_yw n a b c d,
        ∑ C : CFun4 n a b d, bitSign (Q2 x.1.1 C x.1.2))
        =
        scaleC * (Nat.card (SquareCombinedKernel n a b c d) : ℤ) := by
    let q : Surviving_yw n a b c d → Prop :=
      fun x =>
        squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1 = 0
    calc
      (∑ x : Surviving_yw n a b c d,
        ∑ C : CFun4 n a b d, bitSign (Q2 x.1.1 C x.1.2))
          =
          ∑ x : Surviving_yw n a b c d, if q x then scaleC else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x _
            exact square_sum_over_C (n := n) (a := a) (b := b) (c := c) (d := d)
              ha x.1.1 x.1.2
      _ = scaleC * ∑ x : {x : Surviving_yw n a b c d // q x}, (1 : ℤ) := by
            simpa only [mul_one] using
              (sum_if_mul_eq_mul_subtype
                (α := Surviving_yw n a b c d) q scaleC (fun _ => (1 : ℤ)))
      _ = scaleC * (Nat.card (SquareCombinedKernel n a b c d) : ℤ) := by
            congr 1
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [← Nat.card_eq_fintype_card]
            rw [Nat.card_congr (squareSurvivorCompatEquivKernel
              (n := n) (a := a) (b := b) (c := c) (d := d))]
            simp
  rw [hsum]

end Core4loop
