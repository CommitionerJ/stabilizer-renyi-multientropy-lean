import Core4loop.TriangleLeaf.ExceptionalCyclic

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The pair of real source conditions as one linear map on the visible
kernel. -/
noncomputable def exceptionalGoodMap
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafVisibleKernel n b c d →ₗ[F]
      ((NonzeroI n → Core3loop.ProfileZeroSum n) ×
        (NonzeroI n → Core3loop.ProfileZeroSum n)) where
  toFun H := (exceptionalGoodB hd H, exceptionalGoodC hd H)
  map_add' H K := by
    exact Prod.ext
      (exceptionalGoodB_add hd H K)
      (exceptionalGoodC_add hd H K)
  map_smul' r H := by
    by_cases hr : r = 0
    · subst r
      simp only [zero_smul, RingHom.id_apply]
      exact Prod.ext
        (exceptionalGoodB_zero hd)
        (exceptionalGoodC_zero hd)
    · have hr1 : r = 1 := Core3loop.F_ne_zero_eq_one r hr
      subst r
      simp

/-- A fixed-base primitive for the audited backward difference. -/
noncomputable def exceptionalBackwardPrefix
    (n : ℕ) [NeZero n] :
    Core3loop.ProfileZeroSum n →ₗ[F] Core3loop.Profile n :=
  (cyclicShift n).comp
    ((explicitCyclicPrefixLinear n).comp
      (Core3loop.ProfileZeroSum n).subtype)

/-- The fixed-base prefix is an explicit right inverse of
`f(t) ↦ f(t) + f(t-1)`. -/
theorem exceptionalBackwardDiff_backwardPrefix
    {n : ℕ} [NeZero n] (u : Core3loop.ProfileZeroSum n) :
    exceptionalBackwardDiff (exceptionalBackwardPrefix n u) = u := by
  let u4 : ZeroSumProfile n :=
    ⟨u.1, by
      show sigmaMap (n := n) u.1 = 0
      change (∑ s : I n, u.1 s) = 0
      exact LinearMap.mem_ker.mp u.2⟩
  have hu := cycDiff_explicitCyclicPrimitive (n := n) u4
  apply Subtype.ext
  funext t
  have hut := congrFun hu t
  change
    explicitCyclicPrefix u.1 t
      + explicitCyclicPrefix u.1 (t + 1) = u.1 t at hut
  change
    explicitCyclicPrefix u.1 (t + 1)
      + explicitCyclicPrefix u.1 ((t - 1) + 1) = u.1 t
  rw [show (t - 1 : I n) + 1 = t by abel]
  simpa [add_comm] using hut

/-- The selected passive representative is obtained from the repository's
actual `vecSumRep` by opposite toggles at two distinct coordinates. -/
noncomputable def exceptionalPassiveWitnessRaw
    {n d : ℕ} [NeZero n] (hd2 : 2 ≤ d) (hd : 0 < d)
    (s : NonzeroI n) : WVec n d :=
  shiftVec
    (shiftVec (vecSumRep (n := n) (k := d) hd s.1)
      (⟨0, by omega⟩ : Fin d) 1)
    (⟨1, by omega⟩ : Fin d) (-1)

@[simp] theorem vecSum_exceptionalPassiveWitnessRaw
    {n d : ℕ} [NeZero n] (hd2 : 2 ≤ d) (hd : 0 < d)
    (s : NonzeroI n) :
    vecSum (exceptionalPassiveWitnessRaw hd2 hd s) = s.1 := by
  unfold exceptionalPassiveWitnessRaw
  rw [vecSum_shiftVec, vecSum_shiftVec,
    vecSum_vecSumRep (n := n) (k := d) hd]
  abel

private theorem exceptionalPassiveWitnessRaw_ne_rep
    {n d : ℕ} [NeZero n] (hn : Even n)
    (hd2 : 2 ≤ d) (hd : 0 < d) (s : NonzeroI n) :
    exceptionalPassiveWitnessRaw hd2 hd s
      ≠ vecSumRep (n := n) (k := d) hd s.1 := by
  letI : Fact (1 < n) := ⟨by
    have hn0 : n ≠ 0 := NeZero.ne n
    rcases hn with ⟨k, hk⟩
    omega⟩
  intro h
  have hi := congrFun h (⟨1, by omega⟩ : Fin d)
  simp [exceptionalPassiveWitnessRaw, shiftVec] at hi

/-- A visible passive witness in each nonzero sum class. -/
noncomputable def exceptionalPassiveWitness
    {n d : ℕ} [NeZero n] (hn : Even n)
    (hd2 : 2 ≤ d) (hd : 0 < d) :
    NonzeroI n → PassiveVisibleIndex n d hd :=
  fun s =>
    ⟨exceptionalPassiveWitnessRaw hd2 hd s, by
      intro t ht heq
      have hsum := congrArg (vecSum (n := n) (k := d)) heq
      rw [vecSum_exceptionalPassiveWitnessRaw,
        vecSum_vecSumRep (n := n) (k := d) hd] at hsum
      subst t
      exact exceptionalPassiveWitnessRaw_ne_rep hn hd2 hd s heq⟩

@[simp] theorem vecSum_exceptionalPassiveWitness
    {n d : ℕ} [NeZero n] (hn : Even n)
    (hd2 : 2 ≤ d) (hd : 0 < d) (s : NonzeroI n) :
    vecSum (exceptionalPassiveWitness hn hd2 hd s).1 = s.1 :=
  vecSum_exceptionalPassiveWitnessRaw hd2 hd s

theorem exceptionalPassiveWitness_injective
    {n d : ℕ} [NeZero n] (hn : Even n)
    (hd2 : 2 ≤ d) (hd : 0 < d) :
    Function.Injective (exceptionalPassiveWitness hn hd2 hd) := by
  intro s t hst
  apply Subtype.ext
  have hval := congrArg Subtype.val hst
  change
    exceptionalPassiveWitnessRaw hd2 hd s
      = exceptionalPassiveWitnessRaw hd2 hd t at hval
  have hsum := congrArg (vecSum (n := n) (k := d)) hval
  rw [vecSum_exceptionalPassiveWitnessRaw,
    vecSum_exceptionalPassiveWitnessRaw] at hsum
  exact hsum

/-- The explicit `zOfSum`-fiber lift used by the right inverse. -/
noncomputable def exceptionalRightInverseU
    {n c d : ℕ} [NeZero n]
    (hn : Even n) (hc : 0 < c) (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) : ZVec n c → F :=
  ∑ s : NonzeroI n,
    if ω = exceptionalPassiveWitness hn hd2 hd s then
      Core3loop.liftProfileZ (n := n) hc
        (exceptionalBackwardPrefix n (X.1 s))
    else 0

/-- The explicit `yOfSum`-fiber lift used by the right inverse. -/
noncomputable def exceptionalRightInverseV
    {n b d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) : YVec n b → F :=
  ∑ s : NonzeroI n,
    if ω = exceptionalPassiveWitness hn hd2 hd s then
      Core3loop.liftProfileY (n := n) hb
        (exceptionalBackwardPrefix n (X.2 s))
    else 0

/-- A real visible scalar block built from zero `h` data and the two
explicit sum-fiber lifts. -/
noncomputable def exceptionalRightInverseBlock
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) :
    LeafScalarVisibleKernel n b c :=
  (leafScalarVisibleKernelEquivCore3
      (n := n) (b := b) (c := c)).symm
    (Core3loop.dataToScalarVisible (b := b) (c := c) (n := n) hb hc
      (0, exceptionalRightInverseU hn hc hd2 hd X ω,
        exceptionalRightInverseV hn hb hd2 hd X ω))

private theorem exceptionalRightInverseU_add
    {n c d : ℕ} [NeZero n]
    (hn : Even n) (hc : 0 < c) (hd2 : 2 ≤ d) (hd : 0 < d)
    (X Y : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) :
    exceptionalRightInverseU hn hc hd2 hd (X + Y) ω =
      exceptionalRightInverseU hn hc hd2 hd X ω
        + exceptionalRightInverseU hn hc hd2 hd Y ω := by
  funext z
  unfold exceptionalRightInverseU
  simp only [Finset.sum_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro s _
  by_cases hω : ω = exceptionalPassiveWitness hn hd2 hd s
  · rw [if_pos hω, if_pos hω, if_pos hω]
    unfold Core3loop.liftProfileZ
    by_cases hz :
        z = Core3loop.zOfSum (n := n) hc (Core3loop.sumZ z)
    · rw [if_pos hz, if_pos hz, if_pos hz]
      simp only [Prod.fst_add, Pi.add_apply, map_add]
    · rw [if_neg hz, if_neg hz, if_neg hz]
      simp
  · simp [hω]

private theorem exceptionalRightInverseV_add
    {n b d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hd2 : 2 ≤ d) (hd : 0 < d)
    (X Y : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) :
    exceptionalRightInverseV hn hb hd2 hd (X + Y) ω =
      exceptionalRightInverseV hn hb hd2 hd X ω
        + exceptionalRightInverseV hn hb hd2 hd Y ω := by
  funext y
  unfold exceptionalRightInverseV
  simp only [Finset.sum_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro s _
  by_cases hω : ω = exceptionalPassiveWitness hn hd2 hd s
  · rw [if_pos hω, if_pos hω, if_pos hω]
    unfold Core3loop.liftProfileY
    by_cases hy :
        y = Core3loop.yOfSum (n := n) hb (Core3loop.sumY y)
    · rw [if_pos hy, if_pos hy, if_pos hy]
      simp only [Prod.snd_add, Pi.add_apply, map_add]
    · rw [if_neg hy, if_neg hy, if_neg hy]
      simp
  · simp [hω]

private theorem exceptionalRightInverseU_zero
    {n c d : ℕ} [NeZero n]
    (hn : Even n) (hc : 0 < c) (hd2 : 2 ≤ d) (hd : 0 < d)
    (ω : PassiveVisibleIndex n d hd) :
    exceptionalRightInverseU hn hc hd2 hd
        (0 : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
          (NonzeroI n → Core3loop.ProfileZeroSum n)) ω = 0 := by
  funext z
  unfold exceptionalRightInverseU
  simp only [Finset.sum_apply, Pi.zero_apply, Prod.fst_zero]
  refine Finset.sum_eq_zero ?_
  intro s _
  by_cases hω : ω = exceptionalPassiveWitness hn hd2 hd s
  · simp [hω, Core3loop.liftProfileZ]
  · simp [hω]

private theorem exceptionalRightInverseV_zero
    {n b d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hd2 : 2 ≤ d) (hd : 0 < d)
    (ω : PassiveVisibleIndex n d hd) :
    exceptionalRightInverseV hn hb hd2 hd
        (0 : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
          (NonzeroI n → Core3loop.ProfileZeroSum n)) ω = 0 := by
  funext y
  unfold exceptionalRightInverseV
  simp only [Finset.sum_apply, Pi.zero_apply, Prod.snd_zero]
  refine Finset.sum_eq_zero ?_
  intro s _
  by_cases hω : ω = exceptionalPassiveWitness hn hd2 hd s
  · simp [hω, Core3loop.liftProfileY]
  · simp [hω]

private theorem exceptionalRightInverseBlock_add
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (X Y : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) :
    exceptionalRightInverseBlock hn hb hc hd2 hd (X + Y) ω =
      exceptionalRightInverseBlock hn hb hc hd2 hd X ω
        + exceptionalRightInverseBlock hn hb hc hd2 hd Y ω := by
  apply Subtype.ext
  apply Prod.ext
  · funext t z
    change
      Core3loop.buildScalarB (0 : Core3loop.HRaw n)
          (exceptionalRightInverseU hn hc hd2 hd (X + Y) ω) t z
        =
      Core3loop.buildScalarB 0
          (exceptionalRightInverseU hn hc hd2 hd X ω) t z
        +
      Core3loop.buildScalarB 0
          (exceptionalRightInverseU hn hc hd2 hd Y ω) t z
    rw [exceptionalRightInverseU_add]
    simp [Core3loop.buildScalarB]
  · funext y r
    change
      Core3loop.buildScalarC (0 : Core3loop.HRaw n)
          (exceptionalRightInverseV hn hb hd2 hd (X + Y) ω) y r
        =
      Core3loop.buildScalarC 0
          (exceptionalRightInverseV hn hb hd2 hd X ω) y r
        +
      Core3loop.buildScalarC 0
          (exceptionalRightInverseV hn hb hd2 hd Y ω) y r
    rw [exceptionalRightInverseV_add]
    simp [Core3loop.buildScalarC]

private theorem exceptionalRightInverseBlock_zero
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (ω : PassiveVisibleIndex n d hd) :
    exceptionalRightInverseBlock hn hb hc hd2 hd
        (0 : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
          (NonzeroI n → Core3loop.ProfileZeroSum n)) ω = 0 := by
  apply Subtype.ext
  apply Prod.ext
  · funext t z
    change
      Core3loop.buildScalarB (0 : Core3loop.HRaw n)
          (exceptionalRightInverseU hn hc hd2 hd 0 ω) t z = 0
    rw [exceptionalRightInverseU_zero]
    simp [Core3loop.buildScalarB]
  · funext y r
    change
      Core3loop.buildScalarC (0 : Core3loop.HRaw n)
          (exceptionalRightInverseV hn hb hd2 hd 0 ω) y r = 0
    rw [exceptionalRightInverseV_zero]
    simp [Core3loop.buildScalarC]

private theorem exceptionalRightInverseBlock_smul
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (r : F)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) :
    exceptionalRightInverseBlock hn hb hc hd2 hd (r • X) ω =
      r • exceptionalRightInverseBlock hn hb hc hd2 hd X ω := by
  by_cases hr : r = 0
  · subst r
    rw [zero_smul, zero_smul]
    exact exceptionalRightInverseBlock_zero hn hb hc hd2 hd ω
  · have hr1 : r = 1 := Core3loop.F_ne_zero_eq_one r hr
    subst r
    simp

private theorem leafVisibleKernelEquivCoord_add
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H K : LeafVisibleKernel n b c d) :
    leafVisibleKernelEquivCoord hd (H + K) =
      leafVisibleKernelEquivCoord hd H
        + leafVisibleKernelEquivCoord hd K := by
  funext ω
  apply Subtype.ext
  exact congrFun
    ((leafVisiblePairEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd).map_add H.1 K.1) ω

private theorem leafVisibleKernelEquivCoord_smul
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (r : F) (H : LeafVisibleKernel n b c d) :
    leafVisibleKernelEquivCoord hd (r • H) =
      r • leafVisibleKernelEquivCoord hd H := by
  funext ω
  apply Subtype.ext
  exact congrFun
    ((leafVisiblePairEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd).map_smul r H.1) ω

/-- The explicit linear right inverse, built pointwise from real Core3
visible-data constructors and the repository equivalences. -/
noncomputable def exceptionalGoodMapRightInverse
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d) :
    ((NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n)) →ₗ[F]
      LeafVisibleKernel n b c d where
  toFun X :=
    (leafVisibleKernelEquivCoord hd).symm
      (fun ω =>
        exceptionalRightInverseBlock hn (by omega) (by omega) hd2 hd X ω)
  map_add' X Y := by
    apply (leafVisibleKernelEquivCoord hd).injective
    rw [leafVisibleKernelEquivCoord_add]
    simp only [Equiv.apply_symm_apply]
    funext ω
    exact exceptionalRightInverseBlock_add
      hn (by omega) (by omega) hd2 hd X Y ω
  map_smul' r X := by
    apply (leafVisibleKernelEquivCoord hd).injective
    rw [leafVisibleKernelEquivCoord_smul]
    simp only [Equiv.apply_symm_apply]
    funext ω
    exact exceptionalRightInverseBlock_smul
      hn (by omega) (by omega) hd2 hd r X ω

private theorem exceptionalRightInverseBlock_visibleUData
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) :
    Core3loop.visibleUData
        (leafScalarVisibleKernelEquivCore3
          (exceptionalRightInverseBlock hn hb hc hd2 hd X ω))
      =
    exceptionalRightInverseU hn hc hd2 hd X ω := by
  unfold exceptionalRightInverseBlock
  rw [Equiv.apply_symm_apply]
  exact Core3loop.visibleUData_build_eq
    (b := b) (c := c) (n := n) hb hc
    (0 : Core3loop.HAdmissible n)
    (exceptionalRightInverseU hn hc hd2 hd X ω)
    (exceptionalRightInverseV hn hb hd2 hd X ω)

private theorem exceptionalRightInverseBlock_visibleVData
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) :
    Core3loop.visibleVData
        (leafScalarVisibleKernelEquivCore3
          (exceptionalRightInverseBlock hn hb hc hd2 hd X ω))
      =
    exceptionalRightInverseV hn hb hd2 hd X ω := by
  unfold exceptionalRightInverseBlock
  rw [Equiv.apply_symm_apply]
  exact Core3loop.visibleVData_build_eq
    (b := b) (c := c) (n := n) hb hc
    (0 : Core3loop.HAdmissible n)
    (exceptionalRightInverseU hn hc hd2 hd X ω)
    (exceptionalRightInverseV hn hb hd2 hd X ω)

private theorem exceptional_liftProfileZ_fiber
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (μ : Core3loop.Profile n) (t : I n) :
    (∑ z : ZVec n c,
      if t = vecSum z then Core3loop.liftProfileZ (n := n) hc μ z else 0)
      = μ t := by
  have h := congrFun
    (Core3loop.scalarZAgg_liftProfileZ
      (c := c) (n := n) hc μ) t
  unfold Core3loop.scalarZAgg at h
  calc
    (∑ z : ZVec n c,
      if t = vecSum z then Core3loop.liftProfileZ (n := n) hc μ z else 0)
        =
      ∑ z : ZVec n c,
        if Core3loop.sumZ z = t then
          Core3loop.liftProfileZ (n := n) hc μ z else 0 := by
            refine Finset.sum_congr rfl ?_
            intro z _
            change
              (if t = vecSum z then
                  Core3loop.liftProfileZ (n := n) hc μ z else 0)
                =
              if vecSum z = t then
                Core3loop.liftProfileZ (n := n) hc μ z else 0
            by_cases hz : t = vecSum z
            · rw [if_pos hz, if_pos hz.symm]
            · have hz' : vecSum z ≠ t := fun hzt => hz hzt.symm
              rw [if_neg hz, if_neg hz']
    _ = μ t := h

private theorem exceptional_liftProfileY_fiber
    {n b : ℕ} [NeZero n] (hb : 0 < b)
    (μ : Core3loop.Profile n) (t : I n) :
    (∑ y : YVec n b,
      if t = vecSum y then Core3loop.liftProfileY (n := n) hb μ y else 0)
      = μ t := by
  have h := congrFun
    (Core3loop.scalarYAgg_liftProfileY
      (b := b) (n := n) hb μ) t
  unfold Core3loop.scalarYAgg at h
  calc
    (∑ y : YVec n b,
      if t = vecSum y then Core3loop.liftProfileY (n := n) hb μ y else 0)
        =
      ∑ y : YVec n b,
        if Core3loop.sumY y = t then
          Core3loop.liftProfileY (n := n) hb μ y else 0 := by
            refine Finset.sum_congr rfl ?_
            intro y _
            change
              (if t = vecSum y then
                  Core3loop.liftProfileY (n := n) hb μ y else 0)
                =
              if vecSum y = t then
                Core3loop.liftProfileY (n := n) hb μ y else 0
            by_cases hy : t = vecSum y
            · rw [if_pos hy, if_pos hy.symm]
            · have hy' : vecSum y ≠ t := fun hyt => hy hyt.symm
              rw [if_neg hy, if_neg hy']
    _ = μ t := h

private theorem exceptionalRightInverseU_fiber
    {n c d : ℕ} [NeZero n]
    (hn : Even n) (hc : 0 < c) (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) (t : I n) :
    (∑ z : ZVec n c,
      if t = vecSum z then
        exceptionalRightInverseU hn hc hd2 hd X ω z else 0)
      =
    ∑ s : NonzeroI n,
      if ω = exceptionalPassiveWitness hn hd2 hd s then
        exceptionalBackwardPrefix n (X.1 s) t
      else 0 := by
  unfold exceptionalRightInverseU
  simp only [Finset.sum_apply]
  calc
    (∑ z : ZVec n c,
      if t = vecSum z then
        ∑ s : NonzeroI n,
          (if ω = exceptionalPassiveWitness hn hd2 hd s then
            Core3loop.liftProfileZ (n := n) hc
              (exceptionalBackwardPrefix n (X.1 s))
          else 0) z
      else 0)
        =
      ∑ z : ZVec n c, ∑ s : NonzeroI n,
        if t = vecSum z then
          (if ω = exceptionalPassiveWitness hn hd2 hd s then
            Core3loop.liftProfileZ (n := n) hc
              (exceptionalBackwardPrefix n (X.1 s))
          else 0) z
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro z _
          by_cases hz : t = vecSum z
          · simp [hz]
          · simp [hz]
    _ =
      ∑ s : NonzeroI n, ∑ z : ZVec n c,
        if t = vecSum z then
          (if ω = exceptionalPassiveWitness hn hd2 hd s then
            Core3loop.liftProfileZ (n := n) hc
              (exceptionalBackwardPrefix n (X.1 s))
          else 0) z
        else 0 := by rw [Finset.sum_comm]
    _ =
      ∑ s : NonzeroI n,
        if ω = exceptionalPassiveWitness hn hd2 hd s then
          exceptionalBackwardPrefix n (X.1 s) t
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro s _
          by_cases hω :
              ω = exceptionalPassiveWitness hn hd2 hd s
          · simp only [hω, if_true]
            exact exceptional_liftProfileZ_fiber hc
              (exceptionalBackwardPrefix n (X.1 s)) t
          · simp [hω]

private theorem exceptionalRightInverseV_fiber
    {n b d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (ω : PassiveVisibleIndex n d hd) (t : I n) :
    (∑ y : YVec n b,
      if t = vecSum y then
        exceptionalRightInverseV hn hb hd2 hd X ω y else 0)
      =
    ∑ s : NonzeroI n,
      if ω = exceptionalPassiveWitness hn hd2 hd s then
        exceptionalBackwardPrefix n (X.2 s) t
      else 0 := by
  unfold exceptionalRightInverseV
  simp only [Finset.sum_apply]
  calc
    (∑ y : YVec n b,
      if t = vecSum y then
        ∑ s : NonzeroI n,
          (if ω = exceptionalPassiveWitness hn hd2 hd s then
            Core3loop.liftProfileY (n := n) hb
              (exceptionalBackwardPrefix n (X.2 s))
          else 0) y
      else 0)
        =
      ∑ y : YVec n b, ∑ s : NonzeroI n,
        if t = vecSum y then
          (if ω = exceptionalPassiveWitness hn hd2 hd s then
            Core3loop.liftProfileY (n := n) hb
              (exceptionalBackwardPrefix n (X.2 s))
          else 0) y
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro y _
          by_cases hy : t = vecSum y
          · simp [hy]
          · simp [hy]
    _ =
      ∑ s : NonzeroI n, ∑ y : YVec n b,
        if t = vecSum y then
          (if ω = exceptionalPassiveWitness hn hd2 hd s then
            Core3loop.liftProfileY (n := n) hb
              (exceptionalBackwardPrefix n (X.2 s))
          else 0) y
        else 0 := by rw [Finset.sum_comm]
    _ =
      ∑ s : NonzeroI n,
        if ω = exceptionalPassiveWitness hn hd2 hd s then
          exceptionalBackwardPrefix n (X.2 s) t
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro s _
          by_cases hω :
              ω = exceptionalPassiveWitness hn hd2 hd s
          · simp only [hω, if_true]
            exact exceptional_liftProfileY_fiber hb
              (exceptionalBackwardPrefix n (X.2 s)) t
          · simp [hω]

private theorem exceptional_sum_passiveWitness_nonzero_class
    {n d : ℕ} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) (hd : 0 < d)
    (f : NonzeroI n → F) (s : NonzeroI n) :
    (∑ ω : PassiveVisibleIndex n d hd,
      if s.1 = vecSum ω.1 then
        ∑ r : NonzeroI n,
          if ω = exceptionalPassiveWitness hn hd2 hd r then f r else 0
      else 0)
      = f s := by
  calc
    (∑ ω : PassiveVisibleIndex n d hd,
      if s.1 = vecSum ω.1 then
        ∑ r : NonzeroI n,
          if ω = exceptionalPassiveWitness hn hd2 hd r then f r else 0
      else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd, ∑ r : NonzeroI n,
        if s.1 = vecSum ω.1 then
          (if ω = exceptionalPassiveWitness hn hd2 hd r then f r else 0)
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hsω : s.1 = vecSum ω.1
          · simp [hsω]
          · simp [hsω]
    _ =
      ∑ r : NonzeroI n, ∑ ω : PassiveVisibleIndex n d hd,
        if s.1 = vecSum ω.1 then
          (if ω = exceptionalPassiveWitness hn hd2 hd r then f r else 0)
        else 0 := by rw [Finset.sum_comm]
    _ = ∑ r : NonzeroI n, if s = r then f r else 0 := by
      refine Finset.sum_congr rfl ?_
      intro r _
      by_cases hsr : s = r
      · subst r
        rw [Finset.sum_eq_single
          (exceptionalPassiveWitness hn hd2 hd s)]
        · rw [if_pos
            (vecSum_exceptionalPassiveWitness hn hd2 hd s).symm]
          simp
        · intro ω _ hne
          simp [hne]
        · simp
      · have hval : s.1 ≠ r.1 := fun h => hsr (Subtype.ext h)
        rw [if_neg hsr]
        refine Finset.sum_eq_zero ?_
        intro ω _
        by_cases hω :
            ω = exceptionalPassiveWitness hn hd2 hd r
        · rw [hω]
          have hout :
              s.1 ≠ vecSum (exceptionalPassiveWitness hn hd2 hd r).1 := by
            rw [vecSum_exceptionalPassiveWitness]
            exact hval
          rw [if_neg hout]
        · simp [hω]
    _ = f s := by
      rw [Finset.sum_eq_single s]
      · simp
      · intro r _ hrs
        rw [if_neg (fun hsr => hrs hsr.symm)]
      · simp

private theorem exceptional_sum_passiveWitness_zero_class
    {n d : ℕ} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) (hd : 0 < d)
    (f : NonzeroI n → F) :
    (∑ ω : PassiveVisibleIndex n d hd,
      if 0 = vecSum ω.1 then
        ∑ r : NonzeroI n,
          if ω = exceptionalPassiveWitness hn hd2 hd r then f r else 0
      else 0)
      = 0 := by
  refine Finset.sum_eq_zero ?_
  intro ω _
  by_cases hzero : 0 = vecSum ω.1
  · rw [if_pos hzero]
    refine Finset.sum_eq_zero ?_
    intro r _
    by_cases hω : ω = exceptionalPassiveWitness hn hd2 hd r
    · have hsum := congrArg (vecSum (n := n) (k := d))
        (congrArg Subtype.val hω)
      rw [vecSum_exceptionalPassiveWitness] at hsum
      have hr0 : r.1 = 0 := by
        calc
          r.1 = vecSum ω.1 := hsum.symm
          _ = 0 := hzero.symm
      exact False.elim (r.2 hr0)
    · simp [hω]
  · simp [hzero]

private theorem exceptionalZAggregate_rightInverse_nonzero
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (s : NonzeroI n) (t : I n) :
    exceptionalZAggregate hd
        (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X) s.1 t
      =
    exceptionalBackwardPrefix n (X.1 s) t := by
  have hcoord :
      ∀ ω : PassiveVisibleIndex n d hd,
        leafScalarVisibleKernelEquivCore3
            ((leafVisibleKernelEquivCoord hd
              (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X)) ω)
          =
        leafScalarVisibleKernelEquivCore3
          (exceptionalRightInverseBlock hn (by omega) (by omega)
            hd2 hd X ω) := by
    intro ω
    simp [exceptionalGoodMapRightInverse]
  unfold exceptionalZAggregate
  calc
    (∑ ω : PassiveVisibleIndex n d hd,
      if s.1 = vecSum ω.1 then
        ∑ z : ZVec n c,
          if t = vecSum z then
            Core3loop.visibleUData
              (leafScalarVisibleKernelEquivCore3
                ((leafVisibleKernelEquivCoord hd
                  (exceptionalGoodMapRightInverse
                    hn hb2 hc2 hd2 hd X)) ω)) z
          else 0
      else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        if s.1 = vecSum ω.1 then
          ∑ r : NonzeroI n,
            if ω = exceptionalPassiveWitness hn hd2 hd r then
              exceptionalBackwardPrefix n (X.1 r) t
            else 0
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hsω : s.1 = vecSum ω.1
          · simp only [hsω, if_true]
            rw [hcoord ω,
              exceptionalRightInverseBlock_visibleUData
                hn (by omega) (by omega) hd2 hd X ω]
            exact exceptionalRightInverseU_fiber
              hn (by omega) hd2 hd X ω t
          · simp [hsω]
    _ = exceptionalBackwardPrefix n (X.1 s) t :=
      exceptional_sum_passiveWitness_nonzero_class
        hn hd2 hd (fun r => exceptionalBackwardPrefix n (X.1 r) t) s

private theorem exceptionalZAggregate_rightInverse_zero
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (t : I n) :
    exceptionalZAggregate hd
        (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X) 0 t = 0 := by
  have hcoord :
      ∀ ω : PassiveVisibleIndex n d hd,
        leafScalarVisibleKernelEquivCore3
            ((leafVisibleKernelEquivCoord hd
              (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X)) ω)
          =
        leafScalarVisibleKernelEquivCore3
          (exceptionalRightInverseBlock hn (by omega) (by omega)
            hd2 hd X ω) := by
    intro ω
    simp [exceptionalGoodMapRightInverse]
  unfold exceptionalZAggregate
  calc
    (∑ ω : PassiveVisibleIndex n d hd,
      if 0 = vecSum ω.1 then
        ∑ z : ZVec n c,
          if t = vecSum z then
            Core3loop.visibleUData
              (leafScalarVisibleKernelEquivCore3
                ((leafVisibleKernelEquivCoord hd
                  (exceptionalGoodMapRightInverse
                    hn hb2 hc2 hd2 hd X)) ω)) z
          else 0
      else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        if 0 = vecSum ω.1 then
          ∑ r : NonzeroI n,
            if ω = exceptionalPassiveWitness hn hd2 hd r then
              exceptionalBackwardPrefix n (X.1 r) t
            else 0
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hω0 : 0 = vecSum ω.1
          · simp only [hω0, if_true]
            rw [hcoord ω,
              exceptionalRightInverseBlock_visibleUData
                hn (by omega) (by omega) hd2 hd X ω]
            exact exceptionalRightInverseU_fiber
              hn (by omega) hd2 hd X ω t
          · simp [hω0]
    _ = 0 :=
      exceptional_sum_passiveWitness_zero_class
        hn hd2 hd (fun r => exceptionalBackwardPrefix n (X.1 r) t)

private theorem exceptionalYAggregate_rightInverse_nonzero
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (s : NonzeroI n) (t : I n) :
    exceptionalYAggregate hd
        (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X) s.1 t
      =
    exceptionalBackwardPrefix n (X.2 s) t := by
  have hcoord :
      ∀ ω : PassiveVisibleIndex n d hd,
        leafScalarVisibleKernelEquivCore3
            ((leafVisibleKernelEquivCoord hd
              (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X)) ω)
          =
        leafScalarVisibleKernelEquivCore3
          (exceptionalRightInverseBlock hn (by omega) (by omega)
            hd2 hd X ω) := by
    intro ω
    simp [exceptionalGoodMapRightInverse]
  unfold exceptionalYAggregate
  calc
    (∑ ω : PassiveVisibleIndex n d hd,
      if s.1 = vecSum ω.1 then
        ∑ y : YVec n b,
          if t = vecSum y then
            Core3loop.visibleVData
              (leafScalarVisibleKernelEquivCore3
                ((leafVisibleKernelEquivCoord hd
                  (exceptionalGoodMapRightInverse
                    hn hb2 hc2 hd2 hd X)) ω)) y
          else 0
      else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        if s.1 = vecSum ω.1 then
          ∑ r : NonzeroI n,
            if ω = exceptionalPassiveWitness hn hd2 hd r then
              exceptionalBackwardPrefix n (X.2 r) t
            else 0
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hsω : s.1 = vecSum ω.1
          · simp only [hsω, if_true]
            rw [hcoord ω,
              exceptionalRightInverseBlock_visibleVData
                hn (by omega) (by omega) hd2 hd X ω]
            exact exceptionalRightInverseV_fiber
              hn (by omega) hd2 hd X ω t
          · simp [hsω]
    _ = exceptionalBackwardPrefix n (X.2 s) t :=
      exceptional_sum_passiveWitness_nonzero_class
        hn hd2 hd (fun r => exceptionalBackwardPrefix n (X.2 r) t) s

private theorem exceptionalYAggregate_rightInverse_zero
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (X : (NonzeroI n → Core3loop.ProfileZeroSum n) ×
      (NonzeroI n → Core3loop.ProfileZeroSum n))
    (t : I n) :
    exceptionalYAggregate hd
        (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X) 0 t = 0 := by
  have hcoord :
      ∀ ω : PassiveVisibleIndex n d hd,
        leafScalarVisibleKernelEquivCore3
            ((leafVisibleKernelEquivCoord hd
              (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X)) ω)
          =
        leafScalarVisibleKernelEquivCore3
          (exceptionalRightInverseBlock hn (by omega) (by omega)
            hd2 hd X ω) := by
    intro ω
    simp [exceptionalGoodMapRightInverse]
  unfold exceptionalYAggregate
  calc
    (∑ ω : PassiveVisibleIndex n d hd,
      if 0 = vecSum ω.1 then
        ∑ y : YVec n b,
          if t = vecSum y then
            Core3loop.visibleVData
              (leafScalarVisibleKernelEquivCore3
                ((leafVisibleKernelEquivCoord hd
                  (exceptionalGoodMapRightInverse
                    hn hb2 hc2 hd2 hd X)) ω)) y
          else 0
      else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        if 0 = vecSum ω.1 then
          ∑ r : NonzeroI n,
            if ω = exceptionalPassiveWitness hn hd2 hd r then
              exceptionalBackwardPrefix n (X.2 r) t
            else 0
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hω0 : 0 = vecSum ω.1
          · simp only [hω0, if_true]
            rw [hcoord ω,
              exceptionalRightInverseBlock_visibleVData
                hn (by omega) (by omega) hd2 hd X ω]
            exact exceptionalRightInverseV_fiber
              hn (by omega) hd2 hd X ω t
          · simp [hω0]
    _ = 0 :=
      exceptional_sum_passiveWitness_zero_class
        hn hd2 hd (fun r => exceptionalBackwardPrefix n (X.2 r) t)

private theorem exceptional_sum_visibleB_fiber_eq_u
    {n b c : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc2 : 2 ≤ c)
    (bc : Core3loop.ScalarVisibleCompat b c n) (sy t : I n) :
    (∑ z : ZVec n c,
        if t = vecSum z then bc.bcoef sy z else 0)
      =
    ∑ z : ZVec n c,
      if t = vecSum z then Core3loop.visibleUData bc z else 0 := by
  have hc : 0 < c := by omega
  rw [← Core3loop.buildScalarB_visibleData_eq
    (b := b) (c := c) (n := n) hb hc bc]
  have hprefix :
      (∑ z : ZVec n c,
        if t = vecSum z then
          Core3loop.prefixT
            (Core3loop.visibleHData (b := b) (c := c) (n := n) hc bc)
            sy (vecSum z)
        else 0) = 0 := by
    rw [sum_vecSum_eq_card_tail_mul (n := n) (d := c) hc
      (fun r : I n =>
        if t = r then
          Core3loop.prefixT
            (Core3loop.visibleHData (b := b) (c := c) (n := n) hc bc)
            sy r
        else 0)]
    rw [natCast_card_vec_eq_zero_of_even_pos
      (n := n) (k := c - 1) hn (by omega)]
    simp
  calc
    (∑ z : ZVec n c,
        if t = vecSum z then
          Core3loop.buildScalarB
            (Core3loop.visibleHData (b := b) (c := c) (n := n) hc bc)
            (Core3loop.visibleUData bc) sy z
        else 0)
        =
      (∑ z : ZVec n c,
        if t = vecSum z then Core3loop.visibleUData bc z else 0)
      +
      ∑ z : ZVec n c,
        if t = vecSum z then
          Core3loop.prefixT
            (Core3loop.visibleHData (b := b) (c := c) (n := n) hc bc)
            sy (vecSum z)
        else 0 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro z _
          by_cases hz : t = vecSum z
          · simp [hz, Core3loop.buildScalarB]
            rfl
          · simp [hz]
    _ = ∑ z : ZVec n c,
          if t = vecSum z then Core3loop.visibleUData bc z else 0 := by
            rw [hprefix, add_zero]

private theorem exceptional_remainderCdCoeff_eq_zero
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n 1) (s : I n) :
    qLeafProfileKernelRemainderCdCoeff
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd XB i p s = 0 := by
  have hcard :
      (Fintype.card (Vec n (d - 1)) : F) = 0 := by
    exact natCast_card_vec_eq_zero_of_even_pos
      (n := n) (k := d - 1) hn (by omega)
  have hpow : (n : F) ^ (d - 1) = 0 := by
    simpa [card_vec] using hcard
  simp [qLeafProfileKernelRemainderCdCoeff, hpow,
    leafScalarProfileKernel_one_apply]

private theorem exceptional_totalCvCoeffCondition
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd) :
    TotalCvCoeffCondition
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB := by
  letI := PVec_one_subsingleton (n := n)
  intro i p
  rw [Subsingleton.elim p (zeroVec : PVec n 1)]

private theorem exceptional_totalCdCoeff_eq_backward_zAggregate
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (hd : 0 < d) (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n 1) (s : I n) :
    qLeafProfileKernelTotalCdCoeff
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB i p s
      =
    exceptionalZAggregate hd H s i.2
      + exceptionalZAggregate hd H s (i.2 - 1) := by
  letI := PVec_one_subsingleton (n := n)
  have hp : p = (zeroVec : PVec n 1) :=
    Subsingleton.elim p (zeroVec : PVec n 1)
  have hb : 0 < b := by omega
  have hleft :
      ∀ ω : PassiveVisibleIndex n d hd,
        (∑ z : ZVec n c,
          if i.2 = vecSum z then
            ((leafVisibleKernelEquivCoord hd H) ω).1.1 (vecSum i.1) z
          else 0)
        =
        ∑ z : ZVec n c,
          if i.2 = vecSum z then
            Core3loop.visibleUData
              (leafScalarVisibleKernelEquivCore3
                ((leafVisibleKernelEquivCoord hd H) ω)) z
          else 0 := by
    intro ω
    simpa [leafScalarVisibleKernelEquivCore3] using
      exceptional_sum_visibleB_fiber_eq_u
        hn hb hc2
        (leafScalarVisibleKernelEquivCore3
          ((leafVisibleKernelEquivCoord hd H) ω))
        (vecSum i.1) i.2
  have hright :
      ∀ ω : PassiveVisibleIndex n d hd,
        (∑ z : ZVec n c,
          if i.2 = vecSum z + 1 then
            ((leafVisibleKernelEquivCoord hd H) ω).1.1 (vecSum i.1 + 1) z
          else 0)
        =
        ∑ z : ZVec n c,
          if i.2 - 1 = vecSum z then
            Core3loop.visibleUData
              (leafScalarVisibleKernelEquivCore3
                ((leafVisibleKernelEquivCoord hd H) ω)) z
          else 0 := by
    intro ω
    calc
      (∑ z : ZVec n c,
        if i.2 = vecSum z + 1 then
          ((leafVisibleKernelEquivCoord hd H) ω).1.1 (vecSum i.1 + 1) z
        else 0)
          =
        ∑ z : ZVec n c,
          if i.2 - 1 = vecSum z then
            ((leafVisibleKernelEquivCoord hd H) ω).1.1 (vecSum i.1 + 1) z
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro z _
            apply if_congr
            · constructor
              · intro h
                rw [h]
                abel
              · intro h
                rw [← h]
                abel
            · rfl
            · rfl
      _ =
        ∑ z : ZVec n c,
          if i.2 - 1 = vecSum z then
            Core3loop.visibleUData
              (leafScalarVisibleKernelEquivCore3
                ((leafVisibleKernelEquivCoord hd H) ω)) z
          else 0 := by
            simpa [leafScalarVisibleKernelEquivCore3] using
              exceptional_sum_visibleB_fiber_eq_u
                hn hb hc2
                (leafScalarVisibleKernelEquivCore3
                  ((leafVisibleKernelEquivCoord hd H) ω))
                (vecSum i.1 + 1) (i.2 - 1)
  rw [hp]
  unfold qLeafProfileKernelTotalCdCoeff
  rw [exceptional_remainderCdCoeff_eq_zero hn hd2 hd]
  simp only [zero_add]
  unfold qLeafScalarCanonicalProfileBlockCdCoeff
  simp only [ite_true]
  calc
    (∑ ω : PassiveVisibleIndex n d hd,
      if s = vecSum ω.1 then
        (∑ z : ZVec n c,
          if i.2 = vecSum z then
            ((leafVisibleKernelEquivCoord hd H) ω).1.1 (vecSum i.1) z
          else 0)
        +
        ∑ z : ZVec n c,
          if i.2 = vecSum z + 1 then
            ((leafVisibleKernelEquivCoord hd H) ω).1.1 (vecSum i.1 + 1) z
          else 0
      else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        if s = vecSum ω.1 then
          (∑ z : ZVec n c,
            if i.2 = vecSum z then
              Core3loop.visibleUData
                (leafScalarVisibleKernelEquivCore3
                  ((leafVisibleKernelEquivCoord hd H) ω)) z
            else 0)
          +
          ∑ z : ZVec n c,
            if i.2 - 1 = vecSum z then
              Core3loop.visibleUData
                (leafScalarVisibleKernelEquivCore3
                  ((leafVisibleKernelEquivCoord hd H) ω)) z
            else 0
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hs : s = vecSum ω.1
          · simp only [hs, if_true]
            rw [hleft ω, hright ω]
          · simp [hs]
    _ =
      exceptionalZAggregate hd H s i.2
        + exceptionalZAggregate hd H s (i.2 - 1) := by
          unfold exceptionalZAggregate
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hs : s = vecSum ω.1 <;> simp [hs]

/-- First semantic acceptance gate for the exceptional branch.  This theorem
identifies the real production condition, uniformly in the surviving `XB`,
with the `+U₀` backward-difference constraint. -/
theorem exceptional_totalBCoeffCondition_iff_goodB_eq_zero
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (hd : 0 < d) (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd) :
    TotalBCoeffCondition
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB
      ↔
    exceptionalGoodB hd H = 0 := by
  constructor
  · intro hTotal
    funext s
    apply Subtype.ext
    funext t
    have hcoeff :=
      hTotal.1 ((zeroVec : YVec n b), t) (zeroVec : PVec n 1) s
    rw [exceptional_totalCdCoeff_eq_backward_zAggregate
      hn hb2 hc2 hd2 hd H XB
      ((zeroVec : YVec n b), t) (zeroVec : PVec n 1) s.1] at hcoeff
    rw [exceptional_totalCdCoeff_eq_backward_zAggregate
      hn hb2 hc2 hd2 hd H XB
      ((zeroVec : YVec n b), t) (zeroVec : PVec n 1) 0] at hcoeff
    change
      (exceptionalZAggregate hd H s.1 t
          + exceptionalZAggregate hd H 0 t)
        +
      (exceptionalZAggregate hd H s.1 (t - 1)
          + exceptionalZAggregate hd H 0 (t - 1)) = 0
    calc
      (exceptionalZAggregate hd H s.1 t
          + exceptionalZAggregate hd H 0 t)
        +
      (exceptionalZAggregate hd H s.1 (t - 1)
          + exceptionalZAggregate hd H 0 (t - 1))
          =
        (exceptionalZAggregate hd H s.1 t
          + exceptionalZAggregate hd H s.1 (t - 1))
        +
        (exceptionalZAggregate hd H 0 t
          + exceptionalZAggregate hd H 0 (t - 1)) := by
            abel
      _ =
        (exceptionalZAggregate hd H 0 t
          + exceptionalZAggregate hd H 0 (t - 1))
        +
        (exceptionalZAggregate hd H 0 t
          + exceptionalZAggregate hd H 0 (t - 1)) := by
            rw [hcoeff]
      _ = 0 := F_add_self _
  · intro hGood
    constructor
    · intro i p s
      rw [exceptional_totalCdCoeff_eq_backward_zAggregate
        hn hb2 hc2 hd2 hd H XB i p s.1]
      rw [exceptional_totalCdCoeff_eq_backward_zAggregate
        hn hb2 hc2 hd2 hd H XB i p 0]
      have hs := congrFun hGood s
      have hst := congrFun (congrArg Subtype.val hs) i.2
      change
        (exceptionalZAggregate hd H s.1 i.2
            + exceptionalZAggregate hd H 0 i.2)
          +
        (exceptionalZAggregate hd H s.1 (i.2 - 1)
            + exceptionalZAggregate hd H 0 (i.2 - 1)) = 0 at hst
      calc
        exceptionalZAggregate hd H s.1 i.2
            + exceptionalZAggregate hd H s.1 (i.2 - 1)
            =
          (exceptionalZAggregate hd H s.1 i.2
              + exceptionalZAggregate hd H s.1 (i.2 - 1))
            + 0 := by simp
        _ =
          (exceptionalZAggregate hd H s.1 i.2
              + exceptionalZAggregate hd H s.1 (i.2 - 1))
            +
          ((exceptionalZAggregate hd H s.1 i.2
              + exceptionalZAggregate hd H 0 i.2)
            +
          (exceptionalZAggregate hd H s.1 (i.2 - 1)
              + exceptionalZAggregate hd H 0 (i.2 - 1))) := by
                rw [hst]
        _ =
          exceptionalZAggregate hd H 0 i.2
            + exceptionalZAggregate hd H 0 (i.2 - 1) := by
              calc
                (exceptionalZAggregate hd H s.1 i.2
                    + exceptionalZAggregate hd H s.1 (i.2 - 1))
                  +
                ((exceptionalZAggregate hd H s.1 i.2
                    + exceptionalZAggregate hd H 0 i.2)
                  +
                (exceptionalZAggregate hd H s.1 (i.2 - 1)
                    + exceptionalZAggregate hd H 0 (i.2 - 1)))
                    =
                  (exceptionalZAggregate hd H s.1 i.2
                    + exceptionalZAggregate hd H s.1 i.2)
                  +
                  (exceptionalZAggregate hd H s.1 (i.2 - 1)
                    + exceptionalZAggregate hd H s.1 (i.2 - 1))
                  +
                  (exceptionalZAggregate hd H 0 i.2
                    + exceptionalZAggregate hd H 0 (i.2 - 1)) := by
                      abel
                _ =
                  exceptionalZAggregate hd H 0 i.2
                    + exceptionalZAggregate hd H 0 (i.2 - 1) := by
                      rw [F_add_self, F_add_self, zero_add, zero_add]
    · exact exceptional_totalCvCoeffCondition hd H XB

set_option linter.unusedVariables false in
/-- Second semantic acceptance gate for the exceptional branch.  The real
production phase functional vanishes exactly when the visible `v` aggregate
satisfies the same base-class backward-difference compatibility. -/
theorem exceptional_phaseLinearMap_eq_zero_iff_goodC_eq_zero
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (hd : 0 < d) (H : LeafVisibleKernel n b c d) :
    qLeafProfileKernelTotalCvConstLinearMap
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd H = 0
      ↔
    exceptionalGoodC hd H = 0 := by
  classical
  let L :=
    qLeafProfileKernelTotalCvConstLinearMap
      (n := n) (a := 1) (b := b) (c := c) (d := d) hd H
  let Ldiff :
      ((I n × ZVec n c) → LeafDiffProfileCoord n 1) →ₗ[F] F :=
    { toFun := fun X => L (0, fun sy z => X (sy, z))
      map_add' := by
        intro X Y
        rw [← L.map_add]
        congr 1
      map_smul' := by
        intro r X
        rw [← L.map_smul]
        congr 1 }
  let C : (I n × ZVec n c) → PVec n 1 → I n → F :=
    fun i p s =>
      if p = (zeroVec : PVec n 1) then
        ∑ ω : PassiveVisibleIndex n d hd,
          if s = vecSum ω.1 then
            Core3loop.TScalarFun (b := b) (c := c) (n := n)
              ((leafVisibleKernelEquivCoord hd H) ω).1.2 i.1 i.2
          else 0
      else 0
  have hphase :
      ∀ X : (I n × ZVec n c) → LeafDiffProfileCoord n 1,
        Ldiff X =
          leafDiffFamilyCoeffApply
            (ι := I n × ZVec n c) (n := n) (a := 1) C X := by
    intro X
    change
      qLeafProfileKernelTotalCvConstLinearMap
          (n := n) (a := 1) (b := b) (c := c) (d := d) hd H
          (0, fun sy z => X (sy, z))
        =
      leafDiffFamilyCoeffApply
        (ι := I n × ZVec n c) (n := n) (a := 1) C X
    rw [qLeafProfileKernelTotalCvConstLinearMap_eq_scalarBTrace_visibleC]
    let TS :=
      fun (ω : PassiveVisibleIndex n d hd) (i : I n × ZVec n c) =>
        Core3loop.TScalarFun (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord hd H) ω).1.2 i.1 i.2
    calc
      (∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          (leafBReadKernelScalarBTrace hd
            (0, fun sy z => X (sy, z)) ω)
          ((leafVisibleKernelEquivCoord hd H) ω).1.2)
          =
        ∑ ω : PassiveVisibleIndex n d hd,
          ∑ i : I n × ZVec n c,
            (X i (zeroVec : PVec n 1)).1 (vecSum ω.1) * TS ω i := by
            refine Finset.sum_congr rfl ?_
            intro ω _
            rw [Core3loop.qScalar_eq_bPair_TScalarFun]
            unfold Core3loop.bPairScalar
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro sy _
            refine Finset.sum_congr rfl ?_
            intro z _
            rw [leafBReadKernelScalarBTrace_one_apply]
      _ =
        ∑ i : I n × ZVec n c,
          ∑ ω : PassiveVisibleIndex n d hd,
            TS ω i * (X i (zeroVec : PVec n 1)).1 (vecSum ω.1) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro ω _
              ring
      _ =
        ∑ i : I n × ZVec n c,
          ∑ s : I n,
            (X i (zeroVec : PVec n 1)).1 s *
              ∑ ω : PassiveVisibleIndex n d hd,
                if s = vecSum ω.1 then TS ω i else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [sum_mul_sum_ite_eq
                (K := fun s : I n =>
                  (X i (zeroVec : PVec n 1)).1 s)
                (A := fun ω : PassiveVisibleIndex n d hd => TS ω i)
                (target := fun ω : PassiveVisibleIndex n d hd =>
                  vecSum ω.1)]
      _ =
        leafDiffFamilyCoeffApply
          (ι := I n × ZVec n c) (n := n) (a := 1) C X := by
              symm
              unfold leafDiffFamilyCoeffApply leafDiffCoeffApply C
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
              · simp [TS]
              · intro p _ hp
                simp [hp]
              · simp
  have hC :
      ∀ (i : I n × ZVec n c) (p : PVec n 1) (s : I n),
        C i p s =
          if p = (zeroVec : PVec n 1) then
            exceptionalYAggregate hd H s i.1
              + exceptionalYAggregate hd H s (i.1 - 1)
          else 0 := by
    intro i p s
    by_cases hp : p = (zeroVec : PVec n 1)
    · simp only [C, hp, if_true]
      unfold exceptionalYAggregate
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro ω _
      by_cases hs : s = vecSum ω.1
      · simp only [hs, if_true]
        have hc : 0 < c := by omega
        let bc :=
          leafScalarVisibleKernelEquivCore3
            ((leafVisibleKernelEquivCoord hd H) ω)
        change
          Core3loop.TScalarFun (b := b) (c := c) (n := n)
              bc.ccoef i.1 i.2
            =
          (∑ y : YVec n b,
              if i.1 = vecSum y then Core3loop.visibleVData bc y else 0)
            +
          ∑ y : YVec n b,
            if i.1 - 1 = vecSum y then Core3loop.visibleVData bc y else 0
        rw [← Core3loop.buildScalarC_visibleData_eq
          (b := b) (c := c) (n := n) hc bc]
        rw [Core3loop.TScalar_buildScalarC_even
          (b := b) (c := c) (n := n) hn hb2
          (Core3loop.visibleHData (b := b) (c := c) (n := n) hc bc)
          (Core3loop.visibleVData bc) i.1 i.2]
        unfold Core3loop.scalarYAgg
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro y _
          change
            (if vecSum y = i.1 then Core3loop.visibleVData bc y else 0)
              =
            if i.1 = vecSum y then Core3loop.visibleVData bc y else 0
          by_cases hy : i.1 = vecSum y
          · rw [if_pos hy.symm, if_pos hy]
          · have hy' : vecSum y ≠ i.1 := fun h => hy h.symm
            rw [if_neg hy', if_neg hy]
        · refine Finset.sum_congr rfl ?_
          intro y _
          change
            (if vecSum y = i.1 - 1 then
                Core3loop.visibleVData bc y else 0)
              =
            if i.1 - 1 = vecSum y then
              Core3loop.visibleVData bc y else 0
          by_cases hy : i.1 - 1 = vecSum y
          · rw [if_pos hy.symm, if_pos hy]
          · have hy' : vecSum y ≠ i.1 - 1 := fun h => hy h.symm
            rw [if_neg hy', if_neg hy]
      · simp [hs]
    · simp [C, hp]
  have hLzero : L = 0 ↔ Ldiff = 0 := by
    constructor
    · intro hzero
      apply LinearMap.ext
      intro X
      change L (0, fun sy z => X (sy, z)) = 0
      rw [hzero]
      rfl
    · intro hzero
      apply LinearMap.ext
      intro XB
      have hfst : XB.1 = 0 := by
        funext ω sy z
        exact leafScalarProfileKernel_one_eq_zero (XB.1 ω sy z)
      have hXB : XB = (0, XB.2) := by
        apply Prod.ext
        · exact hfst
        · rfl
      rw [hXB]
      have happly := LinearMap.congr_fun hzero
        (fun i : I n × ZVec n c => XB.2 i.1 i.2)
      exact happly
  have hread :
      leafDiffFamilyCoeffRead
          (n := n) (a := 1) C = 0
        ↔
      exceptionalGoodC hd H = 0 := by
    letI := PVec_one_subsingleton (n := n)
    constructor
    · intro hzero
      funext s
      apply Subtype.ext
      funext t
      have ht := congrFun hzero
        ((t, (zeroVec : ZVec n c)),
          ((zeroVec : PVec n 1), s))
      simp only [Pi.zero_apply] at ht
      unfold leafDiffFamilyCoeffRead leafDiffCoeffRead at ht
      rw [hC, hC] at ht
      simp only [ite_true] at ht
      change
        (exceptionalYAggregate hd H s.1 t
            + exceptionalYAggregate hd H 0 t)
          +
        (exceptionalYAggregate hd H s.1 (t - 1)
            + exceptionalYAggregate hd H 0 (t - 1)) = 0
      calc
        (exceptionalYAggregate hd H s.1 t
            + exceptionalYAggregate hd H 0 t)
          +
        (exceptionalYAggregate hd H s.1 (t - 1)
            + exceptionalYAggregate hd H 0 (t - 1))
            =
          (exceptionalYAggregate hd H s.1 t
              + exceptionalYAggregate hd H s.1 (t - 1))
            +
          (exceptionalYAggregate hd H 0 t
              + exceptionalYAggregate hd H 0 (t - 1)) := by
                abel
        _ = 0 := ht
    · intro hzero
      funext ips
      rcases ips with ⟨⟨t, z⟩, p, s⟩
      rw [Subsingleton.elim p (zeroVec : PVec n 1)]
      unfold leafDiffFamilyCoeffRead leafDiffCoeffRead
      rw [hC, hC]
      simp only [ite_true, Pi.zero_apply]
      have hs := congrFun hzero s
      have hst := congrFun (congrArg Subtype.val hs) t
      change
        (exceptionalYAggregate hd H s.1 t
            + exceptionalYAggregate hd H 0 t)
          +
        (exceptionalYAggregate hd H s.1 (t - 1)
            + exceptionalYAggregate hd H 0 (t - 1)) = 0 at hst
      calc
        (exceptionalYAggregate hd H s.1 t
            + exceptionalYAggregate hd H s.1 (t - 1))
          +
        (exceptionalYAggregate hd H 0 t
            + exceptionalYAggregate hd H 0 (t - 1))
            =
          (exceptionalYAggregate hd H s.1 t
              + exceptionalYAggregate hd H 0 t)
            +
          (exceptionalYAggregate hd H s.1 (t - 1)
              + exceptionalYAggregate hd H 0 (t - 1)) := by
                abel
        _ = 0 := hst
  rw [hLzero]
  rw [linearMap_eq_zero_iff_of_apply_eq_leafDiffFamilyCoeffApply
    (n := n) (a := 1) Ldiff C hphase]
  have hd_scope :
      hd = (by omega : 0 < d) :=
    Subsingleton.elim _ _
  simpa only [hd_scope] using hread

/-- The explicit construction is a genuine linear right inverse of the
combined exceptional source-condition map. -/
theorem exceptionalGoodMap_comp_rightInverse
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d) :
    (exceptionalGoodMap hd).comp
        (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd)
      =
    LinearMap.id := by
  apply LinearMap.ext
  intro X
  apply Prod.ext
  · funext s
    apply Subtype.ext
    funext t
    change
      (exceptionalZAggregate hd
          (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X) s.1 t
        +
        exceptionalZAggregate hd
          (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X) 0 t)
        +
      (exceptionalZAggregate hd
          (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X)
            s.1 (t - 1)
        +
        exceptionalZAggregate hd
          (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X)
            0 (t - 1))
        =
      (X.1 s).1 t
    rw [exceptionalZAggregate_rightInverse_nonzero
      hn hb2 hc2 hd2 hd X s t]
    rw [exceptionalZAggregate_rightInverse_zero
      hn hb2 hc2 hd2 hd X t]
    rw [exceptionalZAggregate_rightInverse_nonzero
      hn hb2 hc2 hd2 hd X s (t - 1)]
    rw [exceptionalZAggregate_rightInverse_zero
      hn hb2 hc2 hd2 hd X (t - 1)]
    simp only [add_zero]
    have hback :=
      exceptionalBackwardDiff_backwardPrefix (X.1 s)
    have ht := congrFun (congrArg Subtype.val hback) t
    exact ht
  · funext s
    apply Subtype.ext
    funext t
    change
      (exceptionalYAggregate hd
          (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X) s.1 t
        +
        exceptionalYAggregate hd
          (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X) 0 t)
        +
      (exceptionalYAggregate hd
          (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X)
            s.1 (t - 1)
        +
        exceptionalYAggregate hd
          (exceptionalGoodMapRightInverse hn hb2 hc2 hd2 hd X)
            0 (t - 1))
        =
      (X.2 s).1 t
    rw [exceptionalYAggregate_rightInverse_nonzero
      hn hb2 hc2 hd2 hd X s t]
    rw [exceptionalYAggregate_rightInverse_zero
      hn hb2 hc2 hd2 hd X t]
    rw [exceptionalYAggregate_rightInverse_nonzero
      hn hb2 hc2 hd2 hd X s (t - 1)]
    rw [exceptionalYAggregate_rightInverse_zero
      hn hb2 hc2 hd2 hd X (t - 1)]
    simp only [add_zero]
    have hback :=
      exceptionalBackwardDiff_backwardPrefix (X.2 s)
    have ht := congrFun (congrArg Subtype.val hback) t
    exact ht

/-- The exceptional map is surjective because the preceding explicit
construction is a genuine right inverse. -/
theorem exceptionalGoodMap_surjective
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d) :
    Function.Surjective
      (exceptionalGoodMap (n := n) (b := b) (c := c) (d := d) hd) := by
  intro X
  refine
    ⟨exceptionalGoodMapRightInverse
      (n := n) (b := b) (c := c) (d := d)
      hn hb2 hc2 hd2 hd X, ?_⟩
  have h :=
    LinearMap.congr_fun
      (exceptionalGoodMap_comp_rightInverse
        (n := n) (b := b) (c := c) (d := d)
        hn hb2 hc2 hd2 hd) X
  simpa using h

/-- The target has two copies of `(n-1)` zero-sum profiles, indexed by
the `n-1` nonzero replica classes. -/
theorem exceptional_finrank_goodTarget
    {n : ℕ} [NeZero n] :
    Module.finrank F
        ((NonzeroI n → Core3loop.ProfileZeroSum n) ×
          (NonzeroI n → Core3loop.ProfileZeroSum n))
      =
    2 * (n - 1) ^ 2 := by
  rw [Module.finrank_prod]
  simp [Module.finrank_pi_fintype, Core3loop.finrank_profileZeroSum]
  ring

/-- Surjectivity identifies the range with the whole audited target. -/
theorem exceptional_finrank_goodMap_range
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d) :
    Module.finrank F
      (LinearMap.range
        (exceptionalGoodMap (n := n) (b := b) (c := c) (d := d) hd))
      =
    2 * (n - 1) ^ 2 := by
  rw [LinearMap.range_eq_top.mpr
    (exceptionalGoodMap_surjective
      (n := n) (b := b) (c := c) (d := d)
      hn hb2 hc2 hd2 hd)]
  rw [finrank_top]
  exact exceptional_finrank_goodTarget (n := n)

/-- The independent visible-source cardinality fixes its finite dimension. -/
theorem exceptional_finrank_visibleSource
    {n b c d : ℕ} [NeZero n]
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd : 0 < d) :
    Module.finrank F (LeafVisibleKernel n b c d)
      =
    (n ^ d - (n - 1)) *
      (n ^ b + n ^ c + (n - 1) ^ 2) := by
  have hcard :=
    card_LeafVisibleKernel
      (n := n) (b := b) (c := c) (d := d)
      (by omega : 0 < b) (by omega : 0 < c) hd
  rw [Module.card_eq_pow_finrank
    (K := F) (V := LeafVisibleKernel n b c d)] at hcard
  simp only [F, ZMod.card] at hcard
  rw [← pow_mul] at hcard
  have hexponent :
      Module.finrank F (LeafVisibleKernel n b c d)
        =
      (n ^ b + n ^ c + (n - 1) ^ 2) *
        (n ^ d - (n - 1)) :=
    Nat.pow_right_injective (by omega : 1 < 2) hcard
  simpa [Nat.mul_comm] using hexponent

/-- Rank-nullity now gives the exceptional compatibility-kernel dimension. -/
theorem exceptional_finrank_goodMap_ker
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker
          (exceptionalGoodMap (n := n) (b := b) (c := c) (d := d) hd))
      =
    (n ^ d - (n - 1)) *
        (n ^ b + n ^ c + (n - 1) ^ 2)
      -
    2 * (n - 1) ^ 2 := by
  have hdim :=
    LinearMap.finrank_range_add_finrank_ker
      (exceptionalGoodMap (n := n) (b := b) (c := c) (d := d) hd)
  rw [exceptional_finrank_goodMap_range
      (n := n) (b := b) (c := c) (d := d)
      hn hb2 hc2 hd2 hd,
    exceptional_finrank_visibleSource
      (n := n) (b := b) (c := c) (d := d)
      hb2 hc2 hd] at hdim
  omega

/-- The compiled exceptional GoodMap kernel has the corresponding
power-of-two cardinality. -/
theorem exceptional_card_ker_goodMap
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hd2 : 2 ≤ d) (hd : 0 < d) :
    Fintype.card
        (LinearMap.ker
          (exceptionalGoodMap (n := n) (b := b) (c := c) (d := d) hd))
      =
    2 ^
      ((n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2)
        -
        2 * (n - 1) ^ 2) := by
  rw [Module.card_eq_pow_finrank
    (K := F)
    (V := LinearMap.ker
      (exceptionalGoodMap (n := n) (b := b) (c := c) (d := d) hd))]
  rw [exceptional_finrank_goodMap_ker
    (n := n) (b := b) (c := c) (d := d)
    hn hb2 hc2 hd2 hd]
  simp [F, ZMod.card]

end

end TriangleLeaf
end Core4loop
