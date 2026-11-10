import Core4loop.TriangleLeaf.BReadEvenAeqOne
import Core4loop.ZeroSumSpaces.ExplicitCyclicPrefix
import Core3loop.EvenCase

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

noncomputable def exceptionalBackwardDiff
    {n : ℕ} [NeZero n] (f : I n → F) :
    Core3loop.ProfileZeroSum n :=
  ⟨fun t => f t + f (t - 1), by
    change Core3loop.sigma (fun t : I n => f t + f (t - 1)) = 0
    unfold Core3loop.sigma
    change (∑ t : I n, (f t + f (t - 1))) = 0
    rw [Finset.sum_add_distrib]
    have hshift : (∑ t : I n, f (t - 1)) = ∑ t : I n, f t := by
      simpa [sub_eq_add_neg] using
        (Equiv.sum_comp (Equiv.addRight (-1 : I n)) f)
    rw [hshift]
    exact F_add_self _⟩

/-- The visible `u` aggregate in a fixed passive-sum and `Z`-sum class. -/
noncomputable def exceptionalZAggregate
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (s t : I n) : F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    if s = vecSum ω.1 then
      ∑ z : ZVec n c,
        if t = vecSum z then
          Core3loop.visibleUData
            (leafScalarVisibleKernelEquivCore3
              ((leafVisibleKernelEquivCoord hd H) ω)) z
        else 0
    else 0

/-- The exceptional compatibility map, including the production-required
base-class term `+ U₀` before taking the backward difference. -/
noncomputable def exceptionalGoodB
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    NonzeroI n → Core3loop.ProfileZeroSum n :=
  fun s =>
    exceptionalBackwardDiff
      (fun t =>
        exceptionalZAggregate hd H s.1 t
          + exceptionalZAggregate hd H 0 t)

/-- The visible `v` aggregate in a fixed passive-sum and `Y`-sum class. -/
noncomputable def exceptionalYAggregate
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (s t : I n) : F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    if s = vecSum ω.1 then
      ∑ y : YVec n b,
        if t = vecSum y then
          Core3loop.visibleVData
            (leafScalarVisibleKernelEquivCore3
              ((leafVisibleKernelEquivCoord hd H) ω)) y
        else 0
    else 0

/-- The exceptional phase-compatibility map.  As for `exceptionalGoodB`,
the base passive-sum class is added before taking the backward difference. -/
noncomputable def exceptionalGoodC
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    NonzeroI n → Core3loop.ProfileZeroSum n :=
  fun s =>
    exceptionalBackwardDiff
      (fun t =>
        exceptionalYAggregate hd H s.1 t
          + exceptionalYAggregate hd H 0 t)

private theorem exceptionalZAggregate_add
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H K : LeafVisibleKernel n b c d) (s t : I n) :
    exceptionalZAggregate hd (H + K) s t =
      exceptionalZAggregate hd H s t + exceptionalZAggregate hd K s t := by
  unfold exceptionalZAggregate
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro ω _
  by_cases hs : s = vecSum ω.1
  · simp only [hs, if_true]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases ht : t = vecSum z
    · simp [ht, leafVisibleKernelEquivCoord, leafVisiblePairEquivCoord,
        leafScalarVisibleKernelEquivCore3, Core3loop.visibleUData]
    · simp [ht]
  · simp [hs]

private theorem exceptionalYAggregate_add
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H K : LeafVisibleKernel n b c d) (s t : I n) :
    exceptionalYAggregate hd (H + K) s t =
      exceptionalYAggregate hd H s t + exceptionalYAggregate hd K s t := by
  unfold exceptionalYAggregate
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro ω _
  by_cases hs : s = vecSum ω.1
  · simp only [hs, if_true]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases ht : t = vecSum y
    · simp [ht, leafVisibleKernelEquivCoord, leafVisiblePairEquivCoord,
        leafScalarVisibleKernelEquivCore3, Core3loop.visibleVData]
    · simp [ht]
  · simp [hs]

private theorem exceptionalZAggregate_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) (s t : I n) :
    exceptionalZAggregate hd (0 : LeafVisibleKernel n b c d) s t = 0 := by
  have h := exceptionalZAggregate_add hd
    (0 : LeafVisibleKernel n b c d) 0 s t
  have hself :
      exceptionalZAggregate hd (0 : LeafVisibleKernel n b c d) s t =
        exceptionalZAggregate hd (0 : LeafVisibleKernel n b c d) s t
          + exceptionalZAggregate hd (0 : LeafVisibleKernel n b c d) s t := by
    simpa using h
  rw [F_add_self] at hself
  exact hself

private theorem exceptionalYAggregate_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) (s t : I n) :
    exceptionalYAggregate hd (0 : LeafVisibleKernel n b c d) s t = 0 := by
  have h := exceptionalYAggregate_add hd
    (0 : LeafVisibleKernel n b c d) 0 s t
  have hself :
      exceptionalYAggregate hd (0 : LeafVisibleKernel n b c d) s t =
        exceptionalYAggregate hd (0 : LeafVisibleKernel n b c d) s t
          + exceptionalYAggregate hd (0 : LeafVisibleKernel n b c d) s t := by
    simpa using h
  rw [F_add_self] at hself
  exact hself

theorem exceptionalGoodB_add
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H K : LeafVisibleKernel n b c d) :
    exceptionalGoodB hd (H + K) =
      exceptionalGoodB hd H + exceptionalGoodB hd K := by
  funext s
  apply Subtype.ext
  funext t
  change
    (exceptionalZAggregate hd (H + K) s.1 t
        + exceptionalZAggregate hd (H + K) 0 t)
      +
    (exceptionalZAggregate hd (H + K) s.1 (t - 1)
        + exceptionalZAggregate hd (H + K) 0 (t - 1))
      =
    ((exceptionalZAggregate hd H s.1 t
        + exceptionalZAggregate hd H 0 t)
      +
    (exceptionalZAggregate hd H s.1 (t - 1)
        + exceptionalZAggregate hd H 0 (t - 1)))
      +
    ((exceptionalZAggregate hd K s.1 t
        + exceptionalZAggregate hd K 0 t)
      +
    (exceptionalZAggregate hd K s.1 (t - 1)
        + exceptionalZAggregate hd K 0 (t - 1)))
  simp only [exceptionalZAggregate_add]
  abel

theorem exceptionalGoodC_add
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H K : LeafVisibleKernel n b c d) :
    exceptionalGoodC hd (H + K) =
      exceptionalGoodC hd H + exceptionalGoodC hd K := by
  funext s
  apply Subtype.ext
  funext t
  change
    (exceptionalYAggregate hd (H + K) s.1 t
        + exceptionalYAggregate hd (H + K) 0 t)
      +
    (exceptionalYAggregate hd (H + K) s.1 (t - 1)
        + exceptionalYAggregate hd (H + K) 0 (t - 1))
      =
    ((exceptionalYAggregate hd H s.1 t
        + exceptionalYAggregate hd H 0 t)
      +
    (exceptionalYAggregate hd H s.1 (t - 1)
        + exceptionalYAggregate hd H 0 (t - 1)))
      +
    ((exceptionalYAggregate hd K s.1 t
        + exceptionalYAggregate hd K 0 t)
      +
    (exceptionalYAggregate hd K s.1 (t - 1)
        + exceptionalYAggregate hd K 0 (t - 1)))
  simp only [exceptionalYAggregate_add]
  abel

theorem exceptionalGoodB_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    exceptionalGoodB hd (0 : LeafVisibleKernel n b c d) = 0 := by
  funext s
  apply Subtype.ext
  funext t
  change
    (exceptionalZAggregate hd
        (0 : LeafVisibleKernel n b c d) s.1 t
      + exceptionalZAggregate hd 0 0 t)
      +
    (exceptionalZAggregate hd 0 s.1 (t - 1)
      + exceptionalZAggregate hd 0 0 (t - 1)) = 0
  rw [exceptionalZAggregate_zero, exceptionalZAggregate_zero,
    exceptionalZAggregate_zero, exceptionalZAggregate_zero]
  simp

theorem exceptionalGoodC_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    exceptionalGoodC hd (0 : LeafVisibleKernel n b c d) = 0 := by
  funext s
  apply Subtype.ext
  funext t
  change
    (exceptionalYAggregate hd
        (0 : LeafVisibleKernel n b c d) s.1 t
      + exceptionalYAggregate hd 0 0 t)
      +
    (exceptionalYAggregate hd 0 s.1 (t - 1)
      + exceptionalYAggregate hd 0 0 (t - 1)) = 0
  rw [exceptionalYAggregate_zero, exceptionalYAggregate_zero,
    exceptionalYAggregate_zero, exceptionalYAggregate_zero]
  simp

end

end TriangleLeaf
end Core4loop
