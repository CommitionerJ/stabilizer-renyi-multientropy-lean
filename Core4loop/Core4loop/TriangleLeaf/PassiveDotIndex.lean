import Core4loop.TriangleLeaf.CanonicalBaseQ
import Core4loop.TriangleLeaf.PassiveDotFiber

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem passiveDot_comm {n d : ℕ} [NeZero n]
    (f g : PassiveRaw n d) :
    passiveDot (n := n) (d := d) f g =
      passiveDot (n := n) (d := d) g f := by
  unfold passiveDot
  refine Finset.sum_congr rfl ?_
  intro w _
  rw [mul_comm]

theorem passiveDot_visibleSpace_diffEmbed_eq_index_sum
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (f : PassiveVisibleSpace n d hd) (R : ZeroSumProfile n) :
    passiveDot (n := n) (d := d) f.1
        (PassiveDiffEmbed (n := n) (d := d) R)
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        passiveVisibleSpaceEquivIndex (n := n) (d := d) hd f ω *
          R.1 (vecSum ω.1) := by
  classical
  let s : Finset (WVec n d) :=
    (Finset.univ : Finset (WVec n d)).filter
      (fun w => ¬ passiveExcludedPred (n := n) (d := d) hd w)
  have hfilter :
      (∑ w : WVec n d,
          f.1 w * (PassiveDiffEmbed (n := n) (d := d) R) w)
        =
      s.sum
        (fun w => f.1 w * (PassiveDiffEmbed (n := n) (d := d) R) w) := by
    subst s
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro w _
    by_cases hw : passiveExcludedPred (n := n) (d := d) hd w
    · rcases hw with ⟨u, hu, rfl⟩
      simp [passiveExcludedPred, f.2 u hu]
    · simp [hw]
  unfold passiveDot
  rw [hfilter]
  calc
    s.sum (fun w =>
        f.1 w * (PassiveDiffEmbed (n := n) (d := d) R) w)
      =
      ∑ w : {w : WVec n d //
          ¬ passiveExcludedPred (n := n) (d := d) hd w},
        f.1 w.1 * (PassiveDiffEmbed (n := n) (d := d) R) w.1 := by
        subst s
        simpa using
          (Finset.sum_subtype_eq_sum_filter
            (s := (Finset.univ : Finset (WVec n d)))
            (p := fun w => ¬ passiveExcludedPred (n := n) (d := d) hd w)
            (f := fun w =>
              f.1 w * (PassiveDiffEmbed (n := n) (d := d) R) w)).symm
    _ =
      ∑ ω : PassiveVisibleIndex n d hd,
        f.1 ω.1 * (PassiveDiffEmbed (n := n) (d := d) R) ω.1 := by
        let e := passiveVisibleIndexEquivComplement (n := n) (d := d) hd
        simpa [e] using
          (Equiv.sum_comp e
            (fun w : {w : WVec n d //
                ¬ passiveExcludedPred (n := n) (d := d) hd w} =>
              f.1 w.1 * (PassiveDiffEmbed (n := n) (d := d) R) w.1)).symm
    _ =
      ∑ ω : PassiveVisibleIndex n d hd,
        passiveVisibleSpaceEquivIndex (n := n) (d := d) hd f ω *
          R.1 (vecSum ω.1) := by
        rfl

theorem passiveDot_diffEmbed_visibleSpace_eq_index_sum
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (R : ZeroSumProfile n) (f : PassiveVisibleSpace n d hd) :
    passiveDot (n := n) (d := d)
        (PassiveDiffEmbed (n := n) (d := d) R) f.1
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        R.1 (vecSum ω.1) *
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd f ω := by
  rw [passiveDot_comm]
  rw [passiveDot_visibleSpace_diffEmbed_eq_index_sum
    (n := n) (d := d) hd f R]
  refine Finset.sum_congr rfl ?_
  intro ω _
  rw [mul_comm]

theorem passiveDot_visibleDiff_symm_visibleSpace_eq_index_sum
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (X : PassiveVisibleSpace n d hd × ZeroSumProfile n)
    (f : PassiveVisibleSpace n d hd) :
    passiveDot (n := n) (d := d)
        ((passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm X) f.1
      =
      (∑ ω : PassiveVisibleIndex n d hd,
        passiveVisibleSpaceEquivIndex (n := n) (d := d) hd X.1 ω *
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd f ω)
        +
      (∑ ω : PassiveVisibleIndex n d hd,
        X.2.1 (vecSum ω.1) *
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd f ω) := by
  rw [passiveRawEquivVisibleDiff_symm_apply (n := n) (d := d) hd X]
  rw [passiveDot_add_left]
  rw [passiveDot_visibleSpace_eq_index_sum (n := n) (d := d) hd X.1 f]
  rw [passiveDot_diffEmbed_visibleSpace_eq_index_sum (n := n) (d := d) hd X.2 f]

theorem passiveDot_visibleSpace_visibleDiff_symm_eq_index_sum
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (f : PassiveVisibleSpace n d hd)
    (X : PassiveVisibleSpace n d hd × ZeroSumProfile n) :
    passiveDot (n := n) (d := d) f.1
        ((passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm X)
      =
      (∑ ω : PassiveVisibleIndex n d hd,
        passiveVisibleSpaceEquivIndex (n := n) (d := d) hd f ω *
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd X.1 ω)
        +
      (∑ ω : PassiveVisibleIndex n d hd,
        passiveVisibleSpaceEquivIndex (n := n) (d := d) hd f ω *
          X.2.1 (vecSum ω.1)) := by
  rw [passiveRawEquivVisibleDiff_symm_apply (n := n) (d := d) hd X]
  rw [passiveDot_add_right]
  rw [passiveDot_visibleSpace_eq_index_sum (n := n) (d := d) hd f X.1]
  rw [passiveDot_visibleSpace_diffEmbed_eq_index_sum (n := n) (d := d) hd f X.2]

theorem passiveDot_visibleDiff_symm_apply_index
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : PassiveVisibleSpace n d hd × ZeroSumProfile n) :
    passiveDot (n := n) (d := d)
        ((passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm X)
        ((passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm Y)
      =
      (∑ ω : PassiveVisibleIndex n d hd,
        passiveVisibleSpaceEquivIndex (n := n) (d := d) hd X.1 ω *
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd Y.1 ω)
        +
      (∑ ω : PassiveVisibleIndex n d hd,
        passiveVisibleSpaceEquivIndex (n := n) (d := d) hd X.1 ω *
          Y.2.1 (vecSum ω.1))
        +
      (∑ ω : PassiveVisibleIndex n d hd,
        X.2.1 (vecSum ω.1) *
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd Y.1 ω)
        +
      (Fintype.card (Vec n (d - 1)) : F) *
        ∑ s : I n, X.2.1 s * Y.2.1 s := by
  rw [passiveDot_visibleDiff_symm_apply
    (n := n) (d := d) hd X Y]
  rw [passiveDot_visibleSpace_eq_index_sum
    (n := n) (d := d) hd X.1 Y.1]
  rw [passiveDot_visibleSpace_diffEmbed_eq_index_sum
    (n := n) (d := d) hd X.1 Y.2]
  rw [passiveDot_diffEmbed_visibleSpace_eq_index_sum
    (n := n) (d := d) hd X.2 Y.1]
  rw [passiveDot_diffEmbed_diffEmbed_eq_card_tail_mul
    (n := n) (d := d) hd X.2 Y.2]

end

end TriangleLeaf
end Core4loop
