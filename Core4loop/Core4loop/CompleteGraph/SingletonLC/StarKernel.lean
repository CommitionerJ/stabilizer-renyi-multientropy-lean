import Core4loop.CompleteGraph.SingletonLC.FiniteTransform
import Core4loop.Gauss.SurvivorSum

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.SingletonLC

noncomputable section

open Core4loop

noncomputable def K4StarExpNat
    (n b c d : Nat) [NeZero n] : Nat :=
  n ^ (b + c + d) +
    Module.finrank F
      (LinearMap.ker
        (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d)))

private theorem starPhaseExponentNF_components
    {n b c d : Nat} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n 1 c d)
    (C : CFun4 n 1 b d) (W : WFun4 n 1 b c) :
    starPhaseExponentNF
        ({ A := A, B := B, C := C, W := W } : NF4 n 1 b c d) =
      coeffApplyA
        (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d) (B, C, W)) A := by
  let L := fun (p : PVec n 1) (y : YVec n b)
      (z : ZVec n c) (w : WVec n d) =>
    dyB B p y z w + dzC C p y z w + dwW W p y z w
  calc
    starPhaseExponentNF
        ({ A := A, B := B, C := C, W := W } : NF4 n 1 b c d) =
      ∑ p : PVec n 1, ∑ y : YVec n b, ∑ z : ZVec n c,
        ∑ w : WVec n d, A y z w * L p y z w := by
          unfold starPhaseExponentNF
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro z _
          apply Finset.sum_congr rfl
          intro w _
          unfold starLocalPhase alphaOf betaOf gammaOf deltaOf etaOf xiOf zetaOf
          congr 1
          simp [L, dyB, dzC, dwW, betaB, gammaB, deltaC, etaC, xiW, zetaW,
            add_comm]
          ring
    _ = ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        A y z w * ∑ p : PVec n 1, L p y z w := by
          exact sum_index_A_mul A L
    _ = coeffApplyA
        (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d) (B, C, W)) A := by
          rw [coeffApplyA_eq_sum]
          rfl

private theorem sum_A_star
    {n b c d : Nat} [NeZero n]
    (B : BFun4 n 1 c d) (C : CFun4 n 1 b d) (W : WFun4 n 1 b c) :
    (∑ A : AFun4 n b c d,
      bitSign
        (starPhaseExponentNF
          ({ A := A, B := B, C := C, W := W } : NF4 n 1 b c d))) =
      if K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d) (B, C, W) = 0
      then (2 : Int) ^ (n ^ (b + c + d))
      else 0 := by
  calc
    _ = ∑ A : AFun4 n b c d,
        bitSign
          (coeffApplyA
            (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d) (B, C, W)) A) := by
          apply Finset.sum_congr rfl
          intro A _
          rw [starPhaseExponentNF_components]
    _ = _ := signedCoeffSumA_formula
      (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d) (B, C, W))

private noncomputable def starConstraintEquivKernel
    {n b c d : Nat} [NeZero n] :
    {x : BFun4 n 1 c d × CFun4 n 1 b d × WFun4 n 1 b c //
      K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d) x = 0} ≃
    LinearMap.ker
      (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d)) where
  toFun x := ⟨x.1, LinearMap.mem_ker.mpr x.2⟩
  invFun x := ⟨x.1, LinearMap.mem_ker.mp x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

private theorem StarDeltaNF_eq_kernel_card
    {n b c d : Nat} [NeZero n] :
    StarDeltaNF n b c d =
      (2 : Int) ^ (n ^ (b + c + d)) *
        (Nat.card
          (LinearMap.ker
            (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d))) : Int) := by
  classical
  let scale : Int := (2 : Int) ^ (n ^ (b + c + d))
  let p : BFun4 n 1 c d × CFun4 n 1 b d × WFun4 n 1 b c → Prop :=
    fun x =>
      K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d) x = 0
  calc
    StarDeltaNF n b c d =
      ∑ A : AFun4 n b c d, ∑ B : BFun4 n 1 c d,
        ∑ C : CFun4 n 1 b d, ∑ W : WFun4 n 1 b c,
          bitSign
            (starPhaseExponentNF
              ({ A := A, B := B, C := C, W := W } : NF4 n 1 b c d)) := by
          unfold StarDeltaNF
          let e := nf4EquivProd n 1 b c d
          rw [Fintype.sum_equiv e
            (fun nf : NF4 n 1 b c d => bitSign (starPhaseExponentNF nf))
            (fun x => bitSign (starPhaseExponentNF (e.symm x)))
            (fun nf => by simp [e])]
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro A _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro B _
          rw [Fintype.sum_prod_type]
          rfl
    _ = ∑ B : BFun4 n 1 c d, ∑ C : CFun4 n 1 b d,
        ∑ W : WFun4 n 1 b c, if p (B, C, W) then scale else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro B _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro C _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro W _
          rw [sum_A_star]
    _ = ∑ x : BFun4 n 1 c d × CFun4 n 1 b d × WFun4 n 1 b c,
        if p x then scale else 0 := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro B _
          rw [Fintype.sum_prod_type]
    _ = scale * ∑ x : {x // p x}, (1 : Int) := by
          simpa only [mul_one] using
            sum_if_mul_eq_mul_subtype p scale (fun _ => (1 : Int))
    _ = scale *
        (Nat.card
          (LinearMap.ker
            (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d))) : Int) := by
          congr 1
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [mul_one]
          rw [← Nat.card_eq_fintype_card]
          exact_mod_cast
            Nat.card_congr
              (starConstraintEquivKernel (n := n) (b := b) (c := c) (d := d))
    _ = _ := rfl

set_option maxHeartbeats 1000000 in
-- Elaborating the generic kernel cardinality instance exceeds the default budget.
set_option synthInstance.maxHeartbeats 200000 in
private theorem starKernelCardZ_eq_pow_finrank
    {n b c d : Nat} [NeZero n] :
    (Nat.card
      (LinearMap.ker
        (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d))) : Int) =
      (2 : Int) ^
        Module.finrank F
          (LinearMap.ker
            (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d))) := by
  have hnat :
      Nat.card
        (LinearMap.ker
          (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d))) =
        2 ^
          Module.finrank F
            (LinearMap.ker
              (K_yzw (n := n) (a := 1) (b := b) (c := c) (d := d))) := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    simp [F]
  exact_mod_cast hnat

theorem StarDeltaNF_eq_pow
    {n b c d : Nat} [NeZero n]
    (_hn2 : 2 <= n) (_hb : 0 < b) (_hc : 0 < c) (_hd : 0 < d) :
    StarDeltaNF n b c d =
      (2 : Int) ^ K4StarExpNat n b c d := by
  rw [StarDeltaNF_eq_kernel_card, starKernelCardZ_eq_pow_finrank]
  rw [← pow_add]
  rfl

end

end Core4loop.CompleteGraph.SingletonLC
