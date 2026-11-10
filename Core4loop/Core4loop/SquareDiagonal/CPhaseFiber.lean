import Core4loop.Square.Linear
import Core4loop.SquareDiagonal.SurvivorFiber

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

private theorem coeffApply_add_right_local {ι : Type*} [Fintype ι]
    (c f g : ι → F) :
    coeffApply c (f + g) = coeffApply c f + coeffApply c g := by
  unfold coeffApply
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Pi.add_apply]
  ring

private theorem coeffApply_smul_right_local {ι : Type*} [Fintype ι]
    (c f : ι → F) (r : F) :
    coeffApply c (r • f) = r * coeffApply c f := by
  unfold coeffApply
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

noncomputable def sqdiagCPhaseCoeff {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) : CFun4 n a b d :=
  squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)

noncomputable def sqdiagCPhaseLinear {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    CFun4 n a b d →ₗ[F] F where
  toFun C :=
    coeffApply
        (cFun4Equiv n a b d
        (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W))
      (cFun4Equiv n a b d C)
  map_add' C C' := by
    have hadd :
        cFun4Equiv n a b d (C + C')
          = cFun4Equiv n a b d C + cFun4Equiv n a b d C' := by
      funext i
      rcases i with ⟨p, y, sz, w⟩
      rfl
    rw [hadd]
    exact coeffApply_add_right_local
      (cFun4Equiv n a b d
        (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W))
      (cFun4Equiv n a b d C)
      (cFun4Equiv n a b d C')
  map_smul' r C := by
    have hsmul :
        cFun4Equiv n a b d (r • C)
          = r • cFun4Equiv n a b d C := by
      funext i
      rcases i with ⟨p, y, sz, w⟩
      rfl
    rw [hsmul]
    simpa [smul_eq_mul] using
      coeffApply_smul_right_local
        (cFun4Equiv n a b d
          (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W))
        (cFun4Equiv n a b d C) r

theorem sqdiagCPhaseLinear_apply
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W C =
      Q3 B C W := by
  unfold sqdiagCPhaseLinear sqdiagCPhaseCoeff
  exact coeffApply_squareCompat_eq_Q2
    (n := n) (a := a) (b := b) (c := c) (d := d) B C W

noncomputable instance instFintypeKerKCMap
    {n a b c d : ℕ} [NeZero n] :
    Fintype
      (LinearMap.ker
        (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) :=
  Fintype.ofInjective
    (fun x :
      LinearMap.ker
        (KCMap (n := n) (a := a) (b := b) (c := c) (d := d)) =>
        (x : CFun4 n a b d))
    (by
      intro x y hxy
      exact Subtype.ext hxy)

set_option maxHeartbeats 800000 in
-- The statement contains `linearMapFiberSignValue` over a high-dimensional
-- function-space kernel; typeclass reduction needs a larger local budget.
theorem sqdiag_inner_C_sum_eq_fiberSignValue
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    (∑ C : CFun4 n a b d,
      if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0 then
        bitSign (Q3 B C W)
      else 0) =
    linearMapFiberSignValue
      (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))
      (sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W)
      0
      (-(KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
          + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W)) := by
  classical
  let L : CFun4 n a b d →ₗ[F] RootTarget n b c d :=
    KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
  let M : CFun4 n a b d →ₗ[F] F :=
    sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W
  let target : RootTarget n b c d :=
    -(KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
      + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W)
  have hrewrite :
      (∑ C : CFun4 n a b d,
        if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0 then
          bitSign (Q3 B C W)
        else 0)
        =
      ∑ C : CFun4 n a b d,
        if L C = target then bitSign (M C + 0) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro C _
    have hcond :
        K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
          ↔ L C = target := by
      simpa [L, target] using
        K_yzw_zero_iff_KC_eq_target
          (n := n) (a := a) (b := b) (c := c) (d := d) B C W
    have hphase : Q3 B C W = M C + 0 := by
      simpa [M] using
        (sqdiagCPhaseLinear_apply
          (n := n) (a := a) (b := b) (c := c) (d := d) B C W).symm
    by_cases hK :
        K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
    · have hL : L C = target := hcond.mp hK
      simp [hK, hL, hphase]
    · have hL : L C ≠ target := by
        intro h
        exact hK (hcond.mpr h)
      simp [hK, hL]
  rw [hrewrite]
  simpa [L, M, target] using
    sum_if_linearMap_eq_const_bitSign_linearMap_add_const_eq_fiberSignValue
      (L := L) (M := M) (q := (0 : F)) (target := target)

set_option maxHeartbeats 800000 in
-- Same kernel-finiteness instance search appears in every `B,W` summand.
theorem sqdiag_survivor_sum_as_BW_fiber_sum
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    (∑ B : BFun4 n a c d,
      ∑ W : WFun4 n a b c,
        linearMapFiberSignValue
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))
          (sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W)
          0
          (-(KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
              + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W))) := by
  rw [sqdiag_survivor_sum_reordered_BWC]
  refine Finset.sum_congr rfl ?_
  intro B _
  refine Finset.sum_congr rfl ?_
  intro W _
  exact sqdiag_inner_C_sum_eq_fiberSignValue
    (n := n) (a := a) (b := b) (c := c) (d := d) B W

end SquareDiagonal
end Core4loop
