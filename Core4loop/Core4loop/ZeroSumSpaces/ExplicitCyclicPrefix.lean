import Core4loop.ZeroSumSpaces.Profile

open scoped BigOperators

namespace Core4loop

noncomputable section

/-- Prefix sum strictly before an index of `Fin n`. -/
noncomputable def finPrefix {n : ℕ} (u : Fin n → F) (s : Fin n) : F :=
  ∑ q ∈ Finset.Iio s, u q

/-- Forward cyclic difference on `Fin n`, with the same orientation as `cycDiff`. -/
def finForwardDiff {n : ℕ} [NeZero n] (f : Fin n → F) (s : Fin n) : F :=
  f s + f (s + 1)

/-- The explicit final index, available whenever `n` is nonzero. -/
def finLastIndex (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, Nat.pred_lt (NeZero.ne n)⟩

@[simp] lemma finPrefix_zero {n : ℕ} [NeZero n] (u : Fin n → F) :
    finPrefix u 0 = 0 := by
  have hIio0 : Finset.Iio (0 : Fin n) = ∅ := by
    rw [← Fin.bot_eq_zero]
    exact Finset.Iio_bot
  rw [finPrefix, hIio0, Finset.sum_empty]

lemma finPrefix_succ_of_lt
    {n : ℕ} [NeZero n] (u : Fin n → F) (s : Fin n)
    (hs : s.val + 1 < n) :
    finPrefix u (s + 1) = finPrefix u s + u s := by
  classical
  rw [finPrefix, finPrefix, Fin.Iio_add_one_eq_Iic hs,
    Finset.Iic_eq_cons_Iio, Finset.sum_cons]
  abel

lemma fin_eq_lastIndex_of_not_succ_lt
    {n : ℕ} [NeZero n] (s : Fin n)
    (hs : ¬s.val + 1 < n) :
    s = finLastIndex n := by
  apply Fin.ext
  simp only [finLastIndex]
  have hslt : s.val < n := s.2
  omega

lemma finLastIndex_add_one
    (n : ℕ) [NeZero n] :
    finLastIndex n + 1 = (0 : Fin n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  change (Fin.last m) + 1 = (0 : Fin (m + 1))
  simp

lemma finPrefix_last_eq_value_add_total
    {n : ℕ} [NeZero n] (u : Fin n → F) :
    finPrefix u (finLastIndex n) =
      u (finLastIndex n) + ∑ q, u q := by
  classical
  have hIic : Finset.Iic (finLastIndex n) = Finset.univ := by
    ext q
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    apply Fin.le_iff_val_le_val.mpr
    simp only [finLastIndex]
    have hq : q.val < n := q.2
    omega
  have htotal :
      (∑ q, u q) = finPrefix u (finLastIndex n) + u (finLastIndex n) := by
    calc
      (∑ q, u q) = ∑ q ∈ Finset.Iic (finLastIndex n), u q := by
        rw [hIic]
      _ = finPrefix u (finLastIndex n) + u (finLastIndex n) := by
        rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons, finPrefix]
        abel
  rw [htotal]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

/-- Full prefix/difference identity, including its wrap correction. -/
theorem finForwardDiff_finPrefix
    {n : ℕ} [NeZero n] (u : Fin n → F) (s : Fin n) :
    finForwardDiff (finPrefix u) s =
      u s + if s = finLastIndex n then (∑ q, u q) else 0 := by
  classical
  by_cases hs : s.val + 1 < n
  · have hsne : s ≠ finLastIndex n := by
      intro hlast
      subst s
      simp only [finLastIndex] at hs
      omega
    rw [finForwardDiff, finPrefix_succ_of_lt u s hs, if_neg hsne,
      add_zero, ← add_assoc, F_add_self]
    simp
  · have hlast : s = finLastIndex n :=
      fin_eq_lastIndex_of_not_succ_lt s hs
    subst s
    rw [finForwardDiff, finLastIndex_add_one, finPrefix_zero,
      add_zero, if_pos rfl, finPrefix_last_eq_value_add_total]

/-- A zero-sum profile is recovered exactly by forward difference of its prefix. -/
theorem finForwardDiff_finPrefix_of_sum_zero
    {n : ℕ} [NeZero n] (u : Fin n → F)
    (hu : (∑ q, u q) = 0) :
    finForwardDiff (finPrefix u) = u := by
  funext s
  rw [finForwardDiff_finPrefix, hu]
  by_cases hs : s = finLastIndex n <;> simp [hs]

private lemma finPrefix_finForwardDiff_natCast
    {n : ℕ} [NeZero n] (f : Fin n → F)
    (k : ℕ) (hk : k < n) :
    finPrefix (finForwardDiff f) (⟨k, hk⟩ : Fin n) =
      f 0 + f ⟨k, hk⟩ := by
  induction k with
  | zero =>
      have hz : (⟨0, hk⟩ : Fin n) = 0 := by rfl
      rw [hz, finPrefix_zero, F_add_self]
  | succ k ih =>
      have hk0 : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
      let q : Fin n := ⟨k, hk0⟩
      have hq : q.val + 1 < n := by
        simpa [q] using hk
      have hsucc : q + 1 = (⟨k + 1, hk⟩ : Fin n) := by
        apply Fin.ext
        simpa [q] using Fin.val_add_one_of_lt' hq
      rw [← hsucc, finPrefix_succ_of_lt (finForwardDiff f) q hq,
        ih hk0]
      change (f 0 + f q) + (f q + f (q + 1)) =
        f 0 + f (q + 1)
      rw [add_assoc, ← add_assoc (f q) (f q) (f (q + 1)),
        F_add_self, zero_add]

/-- Prefixing a forward difference telescopes to the basepoint difference. -/
theorem finPrefix_finForwardDiff
    {n : ℕ} [NeZero n] (f : Fin n → F) (s : Fin n) :
    finPrefix (finForwardDiff f) s = f 0 + f s := by
  have hs : (⟨s.val, s.2⟩ : Fin n) = s := by
    exact Fin.ext rfl
  simpa only [hs] using
    finPrefix_finForwardDiff_natCast f s.val s.2

/-- Transport the strict `Fin n` prefix explicitly to `I n = ZMod n`. -/
noncomputable def explicitCyclicPrefix
    {n : ℕ} [NeZero n] (u : Profile n) : Profile n :=
  fun s =>
    finPrefix (fun q : Fin n => u (ZMod.finEquiv n q))
      ((ZMod.finEquiv n).symm s)

/-- The explicit cyclic prefix is linear in the profile. -/
noncomputable def explicitCyclicPrefixLinear
    (n : ℕ) [NeZero n] :
    Profile n →ₗ[F] Profile n where
  toFun := explicitCyclicPrefix
  map_add' u v := by
    funext s
    simp only [explicitCyclicPrefix, Pi.add_apply, finPrefix]
    rw [Finset.sum_add_distrib]
  map_smul' x u := by
    funext s
    simp only [explicitCyclicPrefix, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, finPrefix]
    rw [← Finset.mul_sum]

lemma zmodFinEquiv_symm_add_one
    {n : ℕ} [NeZero n] (s : I n) :
    (ZMod.finEquiv n).symm (s + 1) =
      (ZMod.finEquiv n).symm s + 1 := by
  rcases n with - | n
  · cases NeZero.ne 0 rfl
  · simp [ZMod.finEquiv, RingEquiv.map_add]

lemma sum_fin_comp_zmodFinEquiv
    {n : ℕ} [NeZero n] (u : Profile n) :
    (∑ q : Fin n, u (ZMod.finEquiv n q)) = ∑ s : I n, u s := by
  simpa using
    (Equiv.sum_comp (ZMod.finEquiv n).toEquiv u)

lemma explicitCyclicPrefix_cycDiff_apply
    {n : ℕ} [NeZero n] (f : Profile n) (s : I n) :
    explicitCyclicPrefix (cycDiff (n := n) F f) s =
      f 0 + f s := by
  let ff : Fin n → F := fun q => f (ZMod.finEquiv n q)
  let q := (ZMod.finEquiv n).symm s
  have hprefix := finPrefix_finForwardDiff ff q
  change finPrefix
      (fun i : Fin n =>
        f (ZMod.finEquiv n i) + f (ZMod.finEquiv n i + 1)) q =
    f 0 + f s
  have hterm :
      (fun i : Fin n =>
          f (ZMod.finEquiv n i) + f (ZMod.finEquiv n i + 1)) =
        finForwardDiff ff := by
    funext i
    simp only [finForwardDiff, ff]
    rw [map_add, map_one]
  rw [hterm]
  simpa [ff, q] using hprefix

/-- The explicit prefix is a concrete primitive for every zero-sum profile. -/
noncomputable def explicitCyclicPrimitive
    (n : ℕ) [NeZero n] :
    ZeroSumProfile n →ₗ[F] Profile n :=
  (explicitCyclicPrefixLinear n).comp (ZeroSumProfile n).subtype

theorem cycDiff_explicitCyclicPrimitive
    {n : ℕ} [NeZero n] (u : ZeroSumProfile n) :
    cycDiff (n := n) F (explicitCyclicPrimitive n u) = u.1 := by
  have hu : (∑ s : I n, u.1 s) = 0 := by
    exact LinearMap.mem_ker.mp u.2
  have huFin : (∑ q : Fin n, u.1 (ZMod.finEquiv n q)) = 0 := by
    rw [sum_fin_comp_zmodFinEquiv]
    exact hu
  have hfin :=
    finForwardDiff_finPrefix_of_sum_zero
      (fun q : Fin n => u.1 (ZMod.finEquiv n q)) huFin
  funext s
  have hs := congrFun hfin ((ZMod.finEquiv n).symm s)
  change explicitCyclicPrefix u.1 s +
      explicitCyclicPrefix u.1 (s + 1) = u.1 s
  simp only [explicitCyclicPrefix]
  rw [zmodFinEquiv_symm_add_one]
  simpa [finForwardDiff] using hs

/-- Prefixing a repository-oriented cyclic difference gives `f 0 + f s`. -/
theorem explicitCyclicPrefix_cycDiff
    {n : ℕ} [NeZero n] (f : Profile n) :
    explicitCyclicPrefix (cycDiff (n := n) F f) =
      fun s => f 0 + f s := by
  funext s
  exact explicitCyclicPrefix_cycDiff_apply f s

/-- Forward shift `T f(s) = f(s+1)`. -/
noncomputable def cyclicShift
    (n : ℕ) [NeZero n] :
    Profile n →ₗ[F] Profile n where
  toFun f := fun s => f (s + 1)
  map_add' f g := by
    funext s
    rfl
  map_smul' x f := by
    funext s
    rfl

/-- Inverse shift `T⁻¹ f(s) = f(s-1)`. -/
noncomputable def cyclicInvShift
    (n : ℕ) [NeZero n] :
    Profile n →ₗ[F] Profile n where
  toFun f := fun s => f (s - 1)
  map_add' f g := by
    funext s
    rfl
  map_smul' x f := by
    funext s
    rfl

@[simp] lemma cyclicShift_apply
    {n : ℕ} [NeZero n] (f : Profile n) (s : I n) :
    cyclicShift n f s = f (s + 1) := rfl

@[simp] lemma cyclicInvShift_apply
    {n : ℕ} [NeZero n] (f : Profile n) (s : I n) :
    cyclicInvShift n f s = f (s - 1) := rfl

/-- Translation preserves the sum over a cyclic index. -/
theorem sum_shift
    {n : ℕ} [NeZero n] (a : I n) (f : Profile n) :
    (∑ s : I n, f (s + a)) = ∑ s : I n, f s :=
  sum_zmod_add_right (n := n) a f

theorem sum_cyclicShift
    {n : ℕ} [NeZero n] (f : Profile n) :
    (∑ s : I n, cyclicShift n f s) = ∑ s : I n, f s := by
  simpa using sum_shift (n := n) (1 : I n) f

theorem sum_cyclicInvShift
    {n : ℕ} [NeZero n] (f : Profile n) :
    (∑ s : I n, cyclicInvShift n f s) = ∑ s : I n, f s := by
  simpa only [cyclicInvShift_apply, sub_eq_add_neg] using
    sum_shift (n := n) (-1 : I n) f

/-- Adjointness of forward and inverse cyclic shifts. -/
theorem cyclicShift_pairing
    {n : ℕ} [NeZero n] (f g : Profile n) :
    (∑ s : I n, cyclicShift n f s * g s) =
      ∑ s : I n, f s * cyclicInvShift n g s := by
  have h := sum_shift (n := n) (1 : I n)
    (fun s : I n => f s * g (s - 1))
  simpa [cyclicShift, cyclicInvShift] using h

/-- The adjoint difference `1 + T⁻¹`. -/
noncomputable def cyclicBackwardDiff
    (n : ℕ) [NeZero n] :
    Profile n →ₗ[F] Profile n where
  toFun f := fun s => f s + f (s - 1)
  map_add' f g := by
    funext s
    simp only [Pi.add_apply]
    abel
  map_smul' x f := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma cyclicBackwardDiff_apply
    {n : ℕ} [NeZero n] (f : Profile n) (s : I n) :
    cyclicBackwardDiff n f s = f s + f (s - 1) := rfl

/-- Adjointness of `1+T` and `1+T⁻¹`. -/
theorem cycDiff_pairing_adjoint
    {n : ℕ} [NeZero n] (f g : Profile n) :
    (∑ s : I n, cycDiff (n := n) F f s * g s) =
      ∑ s : I n, f s * cyclicBackwardDiff n g s := by
  simp_rw [cycDiff_apply, cyclicBackwardDiff_apply, add_mul, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h := cyclicShift_pairing f g
  simp only [cyclicShift_apply, cyclicInvShift_apply] at h
  rw [h]

theorem cycDiff_cyclicShift_commute
    {n : ℕ} [NeZero n] (f : Profile n) :
    cycDiff (n := n) F (cyclicShift n f) =
      cyclicShift n (cycDiff (n := n) F f) := by
  funext s
  simp [cyclicShift, cycDiff, add_assoc]

theorem cycDiff_cyclicInvShift_commute
    {n : ℕ} [NeZero n] (f : Profile n) :
    cycDiff (n := n) F (cyclicInvShift n f) =
      cyclicInvShift n (cycDiff (n := n) F f) := by
  funext s
  simp only [cycDiff_apply, cyclicInvShift_apply]
  congr 1
  congr 1
  abel

/-- Three cyclic coordinates, used by the K4 cycle certificate. -/
abbrev CyclicCube (n : ℕ) := I n → I n → I n → F

def cyclicDiffX
    {n : ℕ} [NeZero n] (f : CyclicCube n) : CyclicCube n :=
  fun x y z => f x y z + f (x + 1) y z

def cyclicDiffY
    {n : ℕ} [NeZero n] (f : CyclicCube n) : CyclicCube n :=
  fun x y z => f x y z + f x (y + 1) z

def cyclicDiffZ
    {n : ℕ} [NeZero n] (f : CyclicCube n) : CyclicCube n :=
  fun x y z => f x y z + f x y (z + 1)

theorem cyclicDiffX_cyclicDiffY_commute
    {n : ℕ} [NeZero n] (f : CyclicCube n) :
    cyclicDiffX (cyclicDiffY f) = cyclicDiffY (cyclicDiffX f) := by
  funext x y z
  simp only [cyclicDiffX, cyclicDiffY]
  abel

theorem cyclicDiffX_cyclicDiffZ_commute
    {n : ℕ} [NeZero n] (f : CyclicCube n) :
    cyclicDiffX (cyclicDiffZ f) = cyclicDiffZ (cyclicDiffX f) := by
  funext x y z
  simp only [cyclicDiffX, cyclicDiffZ]
  abel

theorem cyclicDiffY_cyclicDiffZ_commute
    {n : ℕ} [NeZero n] (f : CyclicCube n) :
    cyclicDiffY (cyclicDiffZ f) = cyclicDiffZ (cyclicDiffY f) := by
  funext x y z
  simp only [cyclicDiffY, cyclicDiffZ]
  abel

end

end Core4loop
