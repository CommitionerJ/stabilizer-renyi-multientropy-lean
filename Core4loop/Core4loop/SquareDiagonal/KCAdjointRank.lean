import Core4loop.SquareDiagonal.CPhaseAdjoint

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

private theorem add_self_eq_zero_of_F_module {M : Type*}
    [AddCommGroup M] [Module F M] (x : M) :
    x + x = 0 := by
  have htwo : (1 : F) + (1 : F) = 0 := by decide
  calc
    x + x = (1 : F) • x + (1 : F) • x := by simp
    _ = ((1 : F) + (1 : F)) • x := by rw [add_smul]
    _ = 0 := by simp [htwo]

abbrev SqdiagKCAdjointRangeModel
    (n b d : ℕ) [NeZero n] :=
  YVec n b → WVec n d → ZeroSumProfile n

noncomputable def sqdiagKCAdjointRangeEmbed
    {n a b d : ℕ} [NeZero n] :
    SqdiagKCAdjointRangeModel n b d →ₗ[F] CFun4 n a b d where
  toFun H := fun _p y sz w => (H y w).1 sz
  map_add' H H' := by
    funext p y sz w
    rfl
  map_smul' r H := by
    funext p y sz w
    rfl

theorem sqdiagKCAdjointRangeEmbed_injective
    {n a b d : ℕ} [NeZero n] :
    Function.Injective
      (sqdiagKCAdjointRangeEmbed
        (n := n) (a := a) (b := b) (d := d)) := by
  intro H H' h
  funext y w
  apply Subtype.ext
  funext sz
  exact
    congrFun
      (congrFun
        (congrFun
          (congrFun h (0 : PVec n a)) y) sz) w

theorem sqdiagKCAdjointCoeff_profile_mem_ZeroSumProfile
    {n a b c d : ℕ} [NeZero n]
    (A : RootTarget n b c d) (y : YVec n b) (w : WVec n d) :
    (fun sz : I n =>
      sqdiagKCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        A (0 : PVec n a) y sz w) ∈ ZeroSumProfile n := by
  classical
  rw [ZeroSumProfile, LinearMap.mem_ker]
  change
    (∑ sz : I n,
      sqdiagKCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        A (0 : PVec n a) y sz w) = 0
  unfold sqdiagKCAdjointCoeff
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_comm, add_self_eq_zero_of_F_module]

theorem range_sqdiagKCAdjointMap_le_rangeEmbed
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
      LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) := by
  intro C hC
  rcases hC with ⟨A, rfl⟩
  let H : SqdiagKCAdjointRangeModel n b d :=
    fun y w =>
      ⟨fun sz : I n =>
          sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d)
            A (0 : PVec n a) y sz w,
        sqdiagKCAdjointCoeff_profile_mem_ZeroSumProfile
          (n := n) (a := a) (b := b) (c := c) (d := d) A y w⟩
  refine ⟨H, ?_⟩
  funext p y sz w
  rfl

theorem sum_vecSingle_fiber_eq_shift
    {n c : ℕ} [NeZero n]
    (hc : 0 < c) (P : Profile n) (sz : I n) :
    (∑ z : ZVec n c,
      if vecSum z = sz then
        if z = vecSingle hc (vecSum z) then P (vecSum z + 1) else 0
      else 0) =
    P (sz + 1) := by
  classical
  rw [Finset.sum_eq_single (vecSingle hc sz)]
  · simp [vecSum_vecSingle]
  · intro z _ hz
    by_cases hsum : vecSum z = sz
    · have hnot :
          z ≠ vecSingle hc (vecSum z) := by
        intro hsel
        apply hz
        simpa [hsum] using hsel
      simp [hsum, hz]
    · simp [hsum]
  · intro hmem
    simp at hmem

theorem sum_vecSingle_fiber_add_one_eq
    {n c : ℕ} [NeZero n]
    (hc : 0 < c) (P : Profile n) (sz : I n) :
    (∑ z : ZVec n c,
      if vecSum z + 1 = sz then
        if z = vecSingle hc (vecSum z) then P (vecSum z + 1) else 0
      else 0) =
    P sz := by
  classical
  rw [Finset.sum_eq_single (vecSingle hc (sz - 1))]
  · have hsum :
        vecSum (vecSingle hc (sz - 1)) + 1 = sz := by
      rw [vecSum_vecSingle]
      exact sub_add_cancel sz 1
    simp [vecSum_vecSingle, sub_add_cancel]
  · intro z _ hz
    by_cases hsum : vecSum z + 1 = sz
    · have hprev : vecSum z = sz - 1 := by
        calc
          vecSum z = (vecSum z + 1) - 1 := by
            exact (add_sub_cancel_right (vecSum z) 1).symm
          _ = sz - 1 := by rw [hsum]
      have hnot :
          z ≠ vecSingle hc (vecSum z) := by
        intro hsel
        apply hz
        simpa [hprev] using hsel
      simp [hsum, hnot]
    · simp [hsum]
  · intro hmem
    simp at hmem

theorem rangeEmbed_le_range_sqdiagKCAdjointMap
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) ≤
      LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro C hC
  rcases hC with ⟨H, rfl⟩
  choose P hP using fun y w =>
    show ∃ P : Profile n, cycDiff (n := n) F P = (H y w).1 by
      have hm :
          (H y w).1 ∈ LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (H y w).2
      exact hm
  let A : RootTarget n b c d := fun y z w =>
    if z = vecSingle hc (vecSum z) then P y w (vecSum z + 1) else 0
  refine ⟨A, ?_⟩
  funext p y sz w
  change
    (∑ z : ZVec n c,
        if vecSum z = sz then A y z w else 0) +
      (∑ z : ZVec n c,
        if vecSum z + 1 = sz then A y z w else 0) =
    (H y w).1 sz
  have h1 :
      (∑ z : ZVec n c,
        if vecSum z = sz then A y z w else 0) =
      P y w (sz + 1) := by
    simpa [A] using sum_vecSingle_fiber_eq_shift (n := n) (c := c) hc (P y w) sz
  have h2 :
      (∑ z : ZVec n c,
        if vecSum z + 1 = sz then A y z w else 0) =
      P y w sz := by
    simpa [A] using sum_vecSingle_fiber_add_one_eq (n := n) (c := c) hc (P y w) sz
  rw [h1, h2]
  have hcyc := congrFun (hP y w) sz
  simpa [cycDiff, add_comm] using hcyc

theorem range_sqdiagKCAdjointMap_eq_rangeEmbed
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) := by
  exact le_antisymm
    (range_sqdiagKCAdjointMap_le_rangeEmbed
      (n := n) (a := a) (b := b) (c := c) (d := d))
    (rangeEmbed_le_range_sqdiagKCAdjointMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hc)

theorem finrank_sqdiagKCAdjointRangeModel
    {n b d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagKCAdjointRangeModel n b d) =
      (n - 1) * n ^ (b + d) := by
  change Module.finrank F (ZCoeff n b d) = (n - 1) * n ^ (b + d)
  rw [finrank_ZCoeff]
  ring

theorem finrank_range_sqdiagKCAdjointMap
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    Module.finrank F
      (LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) =
      (n - 1) * n ^ (b + d) := by
  calc
    Module.finrank F
        (LinearMap.range
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Module.finrank F
          (LinearMap.range
            (sqdiagKCAdjointRangeEmbed
              (n := n) (a := a) (b := b) (d := d))) := by
          rw [range_sqdiagKCAdjointMap_eq_rangeEmbed
            (n := n) (a := a) (b := b) (c := c) (d := d) hc]
    _ = Module.finrank F (SqdiagKCAdjointRangeModel n b d) := by
          exact LinearMap.finrank_range_of_inj
            (sqdiagKCAdjointRangeEmbed_injective
              (n := n) (a := a) (b := b) (d := d))
    _ = (n - 1) * n ^ (b + d) := by
          exact finrank_sqdiagKCAdjointRangeModel (n := n) (b := b) (d := d)

theorem finrank_range_sqdiagKCAdjointMap_eq_ZDiffSpace
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    Module.finrank F
        (LinearMap.range
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (ZDiffSpace (n := n) (b := b) (c := c) (d := d)) := by
  rw [finrank_range_sqdiagKCAdjointMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hc,
    finrank_ZDiffSpace (n := n) (b := b) (c := c) (d := d) hc]

set_option synthInstance.maxHeartbeats 200000 in
-- The rank-nullity specialization expands several finite function-space instances in build mode.
theorem finrank_ker_KCMap_add_rank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) :
    Module.finrank F
        (LinearMap.ker
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
      (n - 1) * n ^ (b + d) =
    n ^ (a + b + d) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))
  have hrange :
      Module.finrank F
          (LinearMap.range
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        (n - 1) * n ^ (b + d) := by
    rw [range_KCMap_eq_ZDiffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)]
    exact finrank_ZDiffSpace (n := n) (b := b) (c := c) (d := d) hc
  rw [hrange, finrank_CFun4 (n := n) (a := a) (b := b) (d := d) ha] at hnull
  omega

set_option synthInstance.maxHeartbeats 200000 in
-- The adjoint rank-nullity specialization has the same finite function-space instance load.
theorem finrank_ker_sqdiagKCAdjointMap_add_rank
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    Module.finrank F
        (LinearMap.ker
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      (n - 1) * n ^ (b + d) =
    n ^ (b + c + d) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (sqdiagKCAdjointMap
        (n := n) (a := a) (b := b) (c := c) (d := d))
  have hrange :=
    finrank_range_sqdiagKCAdjointMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hc
  rw [hrange, finrank_AFun4 (n := n) (b := b) (c := c) (d := d)] at hnull
  omega

theorem finrank_ker_KCMap_add_rootTarget_eq
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) :
    Module.finrank F
        (LinearMap.ker
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
      n ^ (b + c + d) =
    Module.finrank F
        (LinearMap.ker
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      n ^ (a + b + d) := by
  have hKC :=
    finrank_ker_KCMap_add_rank
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc
  have hAdj :=
    finrank_ker_sqdiagKCAdjointMap_add_rank
      (n := n) (a := a) (b := b) (c := c) (d := d) hc
  omega

end

end SquareDiagonal
end Core4loop
