import Core4loop.TriangleLeaf.ExceptionalGoodMap
import Core4loop.LinearSignSum
import Core3loop.AeqOneClosed

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

/-- On the actual visible source, every production constant-phase summand
vanishes by the Core3 even visible-block theorem. -/
theorem exceptional_visible_phase_eq_zero
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd : 0 < d) (H : LeafVisibleKernel n b c d) :
    qLeafProfileKernelTotalCvVisibleConst
        (n := n) (b := b) (c := c) (d := d) hd H
      =
    0 := by
  classical
  unfold qLeafProfileKernelTotalCvVisibleConst
  apply Finset.sum_eq_zero
  intro ω _
  exact
    Core3loop.qScalar_eq_zero_on_visible_of_even
      (b := b) (c := c) (n := n)
      (by omega) (by omega) hn
      (leafScalarVisibleKernelEquivCore3
        ((leafVisibleKernelEquivCoord hd H) ω))

private theorem exceptionalGoodMap_apply_eq_zero_iff
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    exceptionalGoodMap hd H = 0
      ↔
    exceptionalGoodB hd H = 0 ∧ exceptionalGoodC hd H = 0 := by
  change
    (exceptionalGoodB hd H, exceptionalGoodC hd H) = (0, 0)
      ↔
    exceptionalGoodB hd H = 0 ∧ exceptionalGoodC hd H = 0
  constructor
  · intro h
    exact
      ⟨by simpa using congrArg Prod.fst h,
        by simpa using congrArg Prod.snd h⟩
  · rintro ⟨hB, hC⟩
    exact Prod.ext hB hC

private theorem exceptional_card_XB_one
    {n c d : ℕ} [NeZero n] (hd : 0 < d) :
    (Fintype.card
        (LeafBProfileKernelIndexDiffCoord n 1 c d hd) : ℤ)
      =
    (2 : ℤ) ^ (n ^ (c + 1) * (n - 1)) := by
  norm_cast
  rw [card_LeafBProfileKernelIndexDiffCoord_one
    (n := n) (c := c) (d := d) hd]
  rw [← pow_mul, ← pow_mul]
  congr 1
  rw [pow_succ]
  ring

/-- For a fixed visible source, the surviving `XB` character is either the
whole `XB` cardinality or zero, with the branch decided by the actual paired
exceptional GoodMap. -/
theorem exceptional_sum_XB_character
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (∑ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
      if TotalBCoeffCondition
          (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB then
        bitSign
          (qLeafProfileKernelTotalCvConst
            (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB)
      else 0)
      =
    if exceptionalGoodMap hd H = 0 then
      (2 : ℤ) ^ (n ^ (c + 1) * (n - 1))
    else 0 := by
  classical
  let L :=
    qLeafProfileKernelTotalCvConstLinearMap
      (n := n) (a := 1) (b := b) (c := c) (d := d) hd H
  have hmapiff :
      exceptionalGoodMap hd H = 0
        ↔
      exceptionalGoodB hd H = 0 ∧ exceptionalGoodC hd H = 0 :=
    exceptionalGoodMap_apply_eq_zero_iff hd H
  have hcard :
      (Fintype.card
          (LeafBProfileKernelIndexDiffCoord n 1 c d hd) : ℤ)
        =
      (2 : ℤ) ^ (n ^ (c + 1) * (n - 1)) :=
    exceptional_card_XB_one hd
  by_cases hB : exceptionalGoodB hd H = 0
  · have hcondition :
        ∀ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
          TotalBCoeffCondition
            (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB := by
      intro XB
      exact
        (exceptional_totalBCoeffCondition_iff_goodB_eq_zero
          hn hb2 hc2 hd2 hd H XB).2 hB
    calc
      (∑ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
        if TotalBCoeffCondition
            (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB then
          bitSign
            (qLeafProfileKernelTotalCvConst
              (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB)
        else 0)
          =
        ∑ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
          bitSign (L XB) := by
            refine Finset.sum_congr rfl ?_
            intro XB _
            rw [if_pos (hcondition XB)]
            rw [qLeafProfileKernelTotalCvConst_eq_linear_add_visibleConst
              (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB]
            rw [exceptional_visible_phase_eq_zero
              (n := n) (b := b) (c := c) (d := d)
              hn hb2 hc2 hd H]
            simp [L]
      _ =
        if L = 0 then
          (Fintype.card
            (LeafBProfileKernelIndexDiffCoord n 1 c d hd) : ℤ)
        else 0 := by
          exact sum_bitSign_linearMap L
      _ =
        if exceptionalGoodMap hd H = 0 then
          (2 : ℤ) ^ (n ^ (c + 1) * (n - 1))
        else 0 := by
          by_cases hC : exceptionalGoodC hd H = 0
          · have hL : L = 0 := by
              dsimp [L]
              exact
                (exceptional_phaseLinearMap_eq_zero_iff_goodC_eq_zero
                  hn hb2 hc2 hd2 hd H).2 hC
            have hMap : exceptionalGoodMap hd H = 0 :=
              hmapiff.2 ⟨hB, hC⟩
            rw [if_pos hL, if_pos hMap, hcard]
          · have hL : L ≠ 0 := by
              intro hL
              apply hC
              exact
                (exceptional_phaseLinearMap_eq_zero_iff_goodC_eq_zero
                  hn hb2 hc2 hd2 hd H).1 (by simpa [L] using hL)
            have hMap : exceptionalGoodMap hd H ≠ 0 := by
              intro hMap
              exact hC (hmapiff.1 hMap).2
            rw [if_neg hL, if_neg hMap]
  · have hcondition :
        ∀ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
          ¬ TotalBCoeffCondition
            (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB := by
      intro XB hTotal
      exact hB
        ((exceptional_totalBCoeffCondition_iff_goodB_eq_zero
          hn hb2 hc2 hd2 hd H XB).1 hTotal)
    have hMap : exceptionalGoodMap hd H ≠ 0 := by
      intro hMap
      exact hB (hmapiff.1 hMap).1
    rw [if_neg hMap]
    apply Finset.sum_eq_zero
    intro XB _
    rw [if_neg (hcondition XB)]

private theorem exceptional_kCdCvElimExpNat_one
    (n b d : ℕ) :
    kCdCvElimExpNat n 1 b d = n ^ (b + 1) * (n - 1) := by
  simp [kCdCvElimExpNat, Nat.add_comm]

private theorem exceptional_sum_if_goodMap_eq_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) (A : ℤ) :
    (∑ H : LeafVisibleKernel n b c d,
      if exceptionalGoodMap hd H = 0 then A else 0)
      =
    (Fintype.card
      (LinearMap.ker
        (exceptionalGoodMap
          (n := n) (b := b) (c := c) (d := d) hd)) : ℤ) * A := by
  classical
  let p : LeafVisibleKernel n b c d → Prop :=
    fun H => exceptionalGoodMap hd H = 0
  have hcardNat :
      ((Finset.univ : Finset (LeafVisibleKernel n b c d)).filter p).card
        =
      Fintype.card
        (LinearMap.ker
          (exceptionalGoodMap
            (n := n) (b := b) (c := c) (d := d) hd)) := by
    simpa [p, LinearMap.mem_ker] using (Fintype.card_subtype p).symm
  have hcard :
      (((Finset.univ :
          Finset (LeafVisibleKernel n b c d)).filter p).card : ℤ)
        =
      (Fintype.card
        (LinearMap.ker
          (exceptionalGoodMap
            (n := n) (b := b) (c := c) (d := d) hd)) : ℤ) := by
    exact_mod_cast hcardNat
  calc
    (∑ H : LeafVisibleKernel n b c d,
      if exceptionalGoodMap hd H = 0 then A else 0)
        =
      ∑ H ∈
        ((Finset.univ : Finset (LeafVisibleKernel n b c d)).filter p),
        A := by
          rw [Finset.sum_filter]
    _ =
      (((Finset.univ :
        Finset (LeafVisibleKernel n b c d)).filter p).card : ℤ) * A := by
          simp
    _ =
      (Fintype.card
        (LinearMap.ker
          (exceptionalGoodMap
            (n := n) (b := b) (c := c) (d := d) hd)) : ℤ) * A := by
          rw [hcard]

private theorem exceptional_residual_exponent_regression_two :
    (2 ^ 2 - (2 - 1)) *
          (2 ^ 2 + 2 ^ 2 + (2 - 1) ^ 2)
        +
        (2 - 1) * (2 ^ (2 + 1) + 2 ^ (2 + 1))
        -
        2 * (2 - 1) ^ 2
      =
    41 := by
  norm_num

private theorem exceptional_residual_exponent_regression_four :
    (4 ^ 2 - (4 - 1)) *
          (4 ^ 2 + 4 ^ 2 + (4 - 1) ^ 2)
        +
        (4 - 1) * (4 ^ (2 + 1) + 4 ^ (2 + 1))
        -
        2 * (4 - 1) ^ 2
      =
    899 := by
  norm_num

/-- The exceptional TriangleLeaf residual, evaluated from the real
production reduction through the fixed-`H` character and the actual
GoodMap kernel. -/
theorem leafCompatibleResidualSum_eq_pow_exceptional_residual
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) :
    leafCompatibleResidualSum n 1 b c d
      =
    (2 : ℤ) ^
      ((n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2)
        +
        (n - 1) * (n ^ (b + 1) + n ^ (c + 1))
        -
        2 * (n - 1) ^ 2) := by
  classical
  have hd : 0 < d := by omega
  rw [leafCompatibleResidualSum_eq_after_XB_totalCoeffCondition_closedCard
    (n := n) (a := 1) (b := b) (c := c) (d := d)
    (by omega) hd]
  have hdim :=
    LinearMap.finrank_range_add_finrank_ker
      (exceptionalGoodMap (n := n) (b := b) (c := c) (d := d) hd)
  rw [exceptional_finrank_goodMap_range
      (n := n) (b := b) (c := c) (d := d)
      hn hb2 hc2 hd2 hd,
    exceptional_finrank_visibleSource
      (n := n) (b := b) (c := c) (d := d)
      hb2 hc2 hd] at hdim
  have hle :
      2 * (n - 1) ^ 2
        ≤
      (n ^ d - (n - 1)) *
        (n ^ b + n ^ c + (n - 1) ^ 2) := by
    omega
  have hKX :
      n ^ (b + 1) * (n - 1) + n ^ (c + 1) * (n - 1)
        =
      (n - 1) * (n ^ (b + 1) + n ^ (c + 1)) := by
    ring
  have hexponent :
      ((n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2)
        -
        2 * (n - 1) ^ 2)
        +
      (kCdCvElimExpNat n 1 b d
        + n ^ (c + 1) * (n - 1))
        =
      (n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2)
        +
        (n - 1) * (n ^ (b + 1) + n ^ (c + 1))
        -
        2 * (n - 1) ^ 2 := by
    rw [exceptional_kCdCvElimExpNat_one n b d, hKX]
    omega
  calc
    (∑ H : LeafVisibleKernel n b c d,
      ∑ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
        if TotalBCoeffCondition
            (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB then
          (2 : ℤ) ^ kCdCvElimExpNat n 1 b d *
            bitSign
              (qLeafProfileKernelTotalCvConst
                (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB)
        else 0)
        =
      ∑ H : LeafVisibleKernel n b c d,
        (2 : ℤ) ^ kCdCvElimExpNat n 1 b d *
          (∑ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
            if TotalBCoeffCondition
                (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB then
              bitSign
                (qLeafProfileKernelTotalCvConst
                  (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB)
            else 0) := by
              refine Finset.sum_congr rfl ?_
              intro H _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro XB _
              by_cases hTotal :
                  TotalBCoeffCondition
                    (n := n) (a := 1) (b := b) (c := c) (d := d)
                    hd H XB
              · simp [hTotal]
              · simp [hTotal]
    _ =
      ∑ H : LeafVisibleKernel n b c d,
        (2 : ℤ) ^ kCdCvElimExpNat n 1 b d *
          (if exceptionalGoodMap hd H = 0 then
            (2 : ℤ) ^ (n ^ (c + 1) * (n - 1))
          else 0) := by
            refine Finset.sum_congr rfl ?_
            intro H _
            rw [exceptional_sum_XB_character
              (n := n) (b := b) (c := c) (d := d)
              hn hb2 hc2 hd2 hd H]
    _ =
      ∑ H : LeafVisibleKernel n b c d,
        if exceptionalGoodMap hd H = 0 then
          (2 : ℤ) ^
            (kCdCvElimExpNat n 1 b d
              + n ^ (c + 1) * (n - 1))
        else 0 := by
            refine Finset.sum_congr rfl ?_
            intro H _
            by_cases hGood : exceptionalGoodMap hd H = 0
            · simp [hGood, pow_add]
            · simp [hGood]
    _ =
      (Fintype.card
        (LinearMap.ker
          (exceptionalGoodMap
            (n := n) (b := b) (c := c) (d := d) hd)) : ℤ)
        *
      (2 : ℤ) ^
        (kCdCvElimExpNat n 1 b d
          + n ^ (c + 1) * (n - 1)) := by
            exact exceptional_sum_if_goodMap_eq_zero hd _
    _ =
      (2 : ℤ) ^
        (((n ^ d - (n - 1)) *
            (n ^ b + n ^ c + (n - 1) ^ 2)
          -
          2 * (n - 1) ^ 2)
          +
        (kCdCvElimExpNat n 1 b d
          + n ^ (c + 1) * (n - 1))) := by
            rw [exceptional_card_ker_goodMap
              (n := n) (b := b) (c := c) (d := d)
              hn hb2 hc2 hd2 hd]
            norm_cast
            rw [← pow_add]
    _ =
      (2 : ℤ) ^
        ((n ^ d - (n - 1)) *
            (n ^ b + n ^ c + (n - 1) ^ 2)
          +
          (n - 1) * (n ^ (b + 1) + n ^ (c + 1))
          -
          2 * (n - 1) ^ 2) := by
            rw [hexponent]

end

end TriangleLeaf
end Core4loop
