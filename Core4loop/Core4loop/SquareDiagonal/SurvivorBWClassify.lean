import Core4loop.SquareDiagonal.CPhaseFiber

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable def sqdiagCFiberTarget {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) : RootTarget n b c d :=
  -(KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
      + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W)

noncomputable def sqdiagCKernelCardZ {n a b c d : ℕ} [NeZero n] : ℤ :=
  (Fintype.card
    (LinearMap.ker
      (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ)

def sqdiagCPhaseKernelZero {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) : Prop :=
  (sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W).comp
    (LinearMap.ker
      (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))).subtype = 0

noncomputable def sqdiagCFiberPreimageBranchValue
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) (C0 : CFun4 n a b d) : ℤ := by
  classical
  exact
    if sqdiagCPhaseKernelZero (n := n) (a := a) (b := b) (c := c) (d := d) B W then
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        bitSign
          (sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W C0
            + 0)
    else 0

set_option maxHeartbeats 800000 in
-- The value packages `linearMapFiberSignValue` for the fixed `KCMap` kernel.
noncomputable def sqdiagCFiberValue {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) : ℤ :=
  linearMapFiberSignValue
    (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))
    (sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W)
    0
    (sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W)

theorem sqdiagCFiberValue_eq_of_preimage
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (C0 : CFun4 n a b d)
    (hC0 :
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C0 =
        sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W) :
    sqdiagCFiberValue (n := n) (a := a) (b := b) (c := c) (d := d) B W =
      sqdiagCFiberPreimageBranchValue
        (n := n) (a := a) (b := b) (c := c) (d := d) B W C0 := by
  classical
  unfold sqdiagCFiberValue sqdiagCFiberPreimageBranchValue
  simpa [sqdiagCKernelCardZ, sqdiagCPhaseKernelZero] using
    linearMapFiberSignValue_eq_of_preimage
    (L := KCMap (n := n) (a := a) (b := b) (c := c) (d := d))
    (M := sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W)
    (q := (0 : F))
    (target := sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W)
    C0 hC0

theorem sqdiagCFiberValue_eq_zero_of_not_exists
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (hno :
      ¬ ∃ C0 : CFun4 n a b d,
        KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C0 =
          sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W) :
    sqdiagCFiberValue (n := n) (a := a) (b := b) (c := c) (d := d) B W = 0 := by
  unfold sqdiagCFiberValue
  exact linearMapFiberSignValue_eq_zero_of_not_exists
    (L := KCMap (n := n) (a := a) (b := b) (c := c) (d := d))
    (M := sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W)
    (q := (0 : F))
    (target := sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W)
    hno

theorem sqdiagCFiberTarget_exists_preimage_iff_ZDiff
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    (∃ C0 : CFun4 n a b d,
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C0 =
        sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W) ↔
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
      + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
        ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  constructor
  · intro h
    rcases h with ⟨C0, hC0⟩
    have hmem :
        sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W
          ∈ LinearMap.range
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d)) :=
      ⟨C0, hC0⟩
    rw [range_KCMap_eq_ZDiffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)] at hmem
    have hneg := (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).neg_mem hmem
    simpa [sqdiagCFiberTarget] using hneg
  · intro hmem
    have hneg :
        sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W
          ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
      have h := (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).neg_mem hmem
      simpa [sqdiagCFiberTarget] using h
    rw [← range_KCMap_eq_ZDiffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)] at hneg
    rcases hneg with ⟨C0, hC0⟩
    exact ⟨C0, hC0⟩

theorem sqdiagCFiberValue_eq_zero_of_not_ZDiff
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (hZ :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
          ∉ ZDiffSpace (n := n) (b := b) (c := c) (d := d)) :
    sqdiagCFiberValue (n := n) (a := a) (b := b) (c := c) (d := d) B W = 0 := by
  exact sqdiagCFiberValue_eq_zero_of_not_exists
    (n := n) (a := a) (b := b) (c := c) (d := d) B W
    (by
      intro hpre
      exact hZ
        ((sqdiagCFiberTarget_exists_preimage_iff_ZDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) B W).mp hpre))

theorem sqdiagCFiberValue_eq_zero_of_not_kernelZero
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (hK :
      ¬ sqdiagCPhaseKernelZero
        (n := n) (a := a) (b := b) (c := c) (d := d) B W) :
    sqdiagCFiberValue (n := n) (a := a) (b := b) (c := c) (d := d) B W = 0 := by
  classical
  unfold sqdiagCFiberValue linearMapFiberSignValue
  by_cases hpre :
      ∃ x0 : CFun4 n a b d,
        KCMap (n := n) (a := a) (b := b) (c := c) (d := d) x0 =
          sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W
  · rw [dif_pos hpre]
    have hraw :
        (sqdiagCPhaseLinear
            (n := n) (a := a) (b := b) (c := c) (d := d) B W).comp
          (LinearMap.ker
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))).subtype ≠ 0 := by
      simpa [sqdiagCPhaseKernelZero] using hK
    rw [if_neg hraw]
  · rw [dif_neg hpre]

noncomputable def sqdiagCFiberClassifiedValue
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) : ℤ := by
  classical
  exact
    if hZ :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
          + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
            ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) then
      if sqdiagCPhaseKernelZero
          (n := n) (a := a) (b := b) (c := c) (d := d) B W then
        sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
          bitSign
            (sqdiagCPhaseLinear
                (n := n) (a := a) (b := b) (c := c) (d := d) B W
              (Classical.choose
                ((sqdiagCFiberTarget_exists_preimage_iff_ZDiff
                  (n := n) (a := a) (b := b) (c := c) (d := d) B W).mpr hZ))
              + 0)
      else 0
    else 0

theorem sqdiagCFiberValue_eq_classifiedValue
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    sqdiagCFiberValue (n := n) (a := a) (b := b) (c := c) (d := d) B W =
      sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) B W := by
  classical
  by_cases hZ :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
          ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d)
  · let C0 : CFun4 n a b d :=
      Classical.choose
        ((sqdiagCFiberTarget_exists_preimage_iff_ZDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) B W).mpr hZ)
    have hC0 :
        KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C0 =
          sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W := by
      dsimp [C0]
      exact
        Classical.choose_spec
          ((sqdiagCFiberTarget_exists_preimage_iff_ZDiff
            (n := n) (a := a) (b := b) (c := c) (d := d) B W).mpr hZ)
    rw [sqdiagCFiberValue_eq_of_preimage
      (n := n) (a := a) (b := b) (c := c) (d := d) B W C0 hC0]
    unfold sqdiagCFiberPreimageBranchValue sqdiagCFiberClassifiedValue
    rw [dif_pos hZ]
  · rw [sqdiagCFiberValue_eq_zero_of_not_ZDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) B W hZ]
    unfold sqdiagCFiberClassifiedValue
    rw [dif_neg hZ]

theorem sqdiag_survivor_sum_as_BW_classified_value
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    (∑ B : BFun4 n a c d,
      ∑ W : WFun4 n a b c,
        sqdiagCFiberValue (n := n) (a := a) (b := b) (c := c) (d := d) B W) := by
  rw [sqdiag_survivor_sum_as_BW_fiber_sum]
  refine Finset.sum_congr rfl ?_
  intro B _
  refine Finset.sum_congr rfl ?_
  intro W _
  rfl

theorem sqdiag_survivor_sum_as_BW_ZDiff_kernel_classified_value
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    (∑ B : BFun4 n a c d,
      ∑ W : WFun4 n a b c,
        sqdiagCFiberClassifiedValue
          (n := n) (a := a) (b := b) (c := c) (d := d) B W) := by
  rw [sqdiag_survivor_sum_as_BW_classified_value]
  refine Finset.sum_congr rfl ?_
  intro B _
  refine Finset.sum_congr rfl ?_
  intro W _
  exact sqdiagCFiberValue_eq_classifiedValue
    (n := n) (a := a) (b := b) (c := c) (d := d) B W

end SquareDiagonal
end Core4loop
