import Core3loop.Basic

open scoped BigOperators

namespace Core3loop

abbrev Profile (n : ℕ) := I n → F
abbrev HRaw (n : ℕ) := I n → I n → F

noncomputable def sigma {n : ℕ} [NeZero n] (x : Profile n) : F :=
  ∑ a : I n, x a

def basisProfile {n : ℕ} (a0 : I n) : Profile n :=
  fun a => if a = a0 then 1 else 0

noncomputable def rowSum {n : ℕ} [NeZero n] (h : HRaw n) : Profile n :=
  fun t => ∑ s : I n, h t s

noncomputable def colSum {n : ℕ} [NeZero n] (h : HRaw n) : Profile n :=
  fun s => ∑ t : I n, h t s

noncomputable def rowSumMap {n : ℕ} [NeZero n] : HRaw n →ₗ[F] Profile n where
  toFun := rowSum
  map_add' := by
    intro h k
    funext t
    simp [rowSum, Finset.sum_add_distrib]
  map_smul' := by
    intro a h
    funext t
    simp [rowSum, Pi.smul_apply, Finset.mul_sum]

noncomputable def colSumMap {n : ℕ} [NeZero n] : HRaw n →ₗ[F] Profile n where
  toFun := colSum
  map_add' := by
    intro h k
    funext s
    simp [colSum, Finset.sum_add_distrib]
  map_smul' := by
    intro a h
    funext s
    simp [colSum, Pi.smul_apply, Finset.mul_sum]

noncomputable def HAdmissible (n : ℕ) [NeZero n] : Submodule F (HRaw n) :=
  LinearMap.ker (rowSumMap (n := n)) ⊓ LinearMap.ker (colSumMap (n := n))

noncomputable def prefixT {n : ℕ} [NeZero n] (h : HRaw n) (t s : I n) : F :=
  Finset.sum (Finset.range t.val) fun i => h (i : I n) s

noncomputable def prefixR {n : ℕ} [NeZero n] (h : HRaw n) (t r : I n) : F :=
  Finset.sum (Finset.range r.val) fun j => h t (j : I n)

lemma prefixT_zero {n : ℕ} [NeZero n] (h : HRaw n) (s : I n) :
    prefixT h 0 s = 0 := by
  simp [prefixT, ZMod.val_zero]

lemma prefixR_zero {n : ℕ} [NeZero n] (h : HRaw n) (t : I n) :
    prefixR h t 0 = 0 := by
  simp [prefixR, ZMod.val_zero]

lemma prefixT_natCast_succ {n k : ℕ} [NeZero n] (h : HRaw n) (s : I n)
    (hk : k + 1 < n) :
    prefixT h ((k + 1 : ℕ) : I n) s = prefixT h (k : I n) s + h (k : I n) s := by
  have hk' : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
  rw [prefixT, prefixT, ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hk', Finset.sum_range_succ]

lemma prefixR_natCast_succ {n k : ℕ} [NeZero n] (h : HRaw n) (t : I n)
    (hk : k + 1 < n) :
    prefixR h t ((k + 1 : ℕ) : I n) = prefixR h t (k : I n) + h t (k : I n) := by
  have hk' : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
  rw [prefixR, prefixR, ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hk', Finset.sum_range_succ]

noncomputable def profileSigmaMap {n : ℕ} [NeZero n] : Profile n →ₗ[F] F where
  toFun := sigma
  map_add' := by
    intro x y
    unfold sigma
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    unfold sigma
    simp [Finset.mul_sum]

noncomputable def ProfileZeroSum (n : ℕ) [NeZero n] : Submodule F (Profile n) :=
  LinearMap.ker (profileSigmaMap (n := n))

lemma sigma_basisProfile_zero {n : ℕ} [NeZero n] :
    sigma (basisProfile (n := n) (0 : I n)) = 1 := by
  unfold sigma basisProfile
  rw [Finset.sum_eq_single 0]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

lemma range_sigmaMap_top {n : ℕ} [NeZero n] :
    LinearMap.range (profileSigmaMap (n := n)) = ⊤ := by
  ext a
  constructor
  · intro ha
    simp
  · intro ha
    refine ⟨a • basisProfile (n := n) (0 : I n), ?_⟩
    simp [profileSigmaMap, sigma_basisProfile_zero]

lemma finrank_profile {n : ℕ} [NeZero n] : Module.finrank F (Profile n) = n := by
  change Module.finrank F (I n → F) = n
  simp [I, ZMod.card]

lemma finrank_hRaw {n : ℕ} [NeZero n] : Module.finrank F (HRaw n) = n ^ 2 := by
  change Module.finrank F (I n → I n → F) = n ^ 2
  rw [Module.finrank_pi_fintype (R := F) (M := fun _ : I n => I n → F)]
  calc
    ∑ _ : I n, Module.finrank F (I n → F) = n * n := by
      simp [Module.finrank_pi, I, ZMod.card]
    _ = n ^ 2 := by ring

lemma finrank_profileZeroSum {n : ℕ} [NeZero n] :
    Module.finrank F (ProfileZeroSum n) = n - 1 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (profileSigmaMap (n := n))
  rw [range_sigmaMap_top (n := n)] at hdim
  have htopfin : Module.finrank F (⊤ : Submodule F F) = 1 := by
    simp
  rw [htopfin, finrank_profile] at hdim
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
  have hdim' := congrArg (fun m => m - 1) hdim
  simpa using hdim'

abbrev RowColBalancedBase (n : ℕ) [NeZero n] :=
  { rc : Profile n × Profile n // sigma rc.1 = sigma rc.2 }

noncomputable def rowColBalancedBaseToData {n : ℕ} [NeZero n] :
    RowColBalancedBase n → Profile n × ProfileZeroSum n
  | ⟨rc, hrc⟩ =>
      (rc.1, ⟨rc.2 + rc.1, by
        change sigma (rc.2 + rc.1) = 0
        calc
          sigma (rc.2 + rc.1) = sigma rc.2 + sigma rc.1 := by
            unfold sigma
            simp [Finset.sum_add_distrib]
          _ = 0 := by
            rw [hrc]
            simp [F_add_self]⟩)

noncomputable def dataToRowColBalancedBase {n : ℕ} [NeZero n] :
    Profile n × ProfileZeroSum n → RowColBalancedBase n
  | (r, w) =>
      ⟨(r, w.1 + r), by
        have hw : sigma w.1 = 0 := w.2
        have hcalc : sigma (w.1 + r) = sigma r := by
          calc
            sigma (w.1 + r) = sigma w.1 + sigma r := by
              unfold sigma
              simp [Finset.sum_add_distrib]
            _ = sigma r := by simp [hw]
        exact hcalc.symm⟩

lemma dataToRowColBalancedBase_left_inv {n : ℕ} [NeZero n] (x : RowColBalancedBase n) :
    dataToRowColBalancedBase (n := n) (rowColBalancedBaseToData (n := n) x) = x := by
  rcases x with ⟨x, hx⟩
  have hcancel : ∀ a b : F, b + a + a = b := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext t
    simpa [dataToRowColBalancedBase, rowColBalancedBaseToData] using hcancel (x.1 t) (x.2 t)

lemma rowColBalancedBaseToData_right_inv {n : ℕ} [NeZero n] (x : Profile n × ProfileZeroSum n) :
    rowColBalancedBaseToData (n := n) (dataToRowColBalancedBase (n := n) x) = x := by
  rcases x with ⟨r, w⟩
  have hcancel : ∀ a b : F, b + a + a = b := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext t
    simpa [dataToRowColBalancedBase, rowColBalancedBaseToData] using hcancel (r t) (w.1 t)

noncomputable def rowColBalancedBaseEquivData {n : ℕ} [NeZero n] :
    RowColBalancedBase n ≃ Profile n × ProfileZeroSum n where
  toFun := rowColBalancedBaseToData (n := n)
  invFun := dataToRowColBalancedBase (n := n)
  left_inv := dataToRowColBalancedBase_left_inv (n := n)
  right_inv := rowColBalancedBaseToData_right_inv (n := n)

lemma natCard_profileZeroSum {n : ℕ} [NeZero n] :
    Nat.card (ProfileZeroSum n) = 2 ^ (n - 1) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F, finrank_profileZeroSum]

lemma natCard_rowColBalancedBase {n : ℕ} [NeZero n] :
    Nat.card (RowColBalancedBase n) = 2 ^ (2 * n - 1) := by
  rw [Nat.card_congr (rowColBalancedBaseEquivData (n := n))]
  rw [Nat.card_prod]
  have hProf : Nat.card (Profile n) = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := F), finrank_profile]
    simp [F]
  rw [hProf, natCard_profileZeroSum]
  calc
    2 ^ n * 2 ^ (n - 1) = 2 ^ (n + (n - 1)) := by
      symm
      exact pow_add 2 n (n - 1)
    _ = 2 ^ (2 * n - 1) := by
      congr
      omega

lemma sigma_rowSum_eq_sigma_colSum {n : ℕ} [NeZero n] (h : HRaw n) :
    sigma (rowSum h) = sigma (colSum h) := by
  unfold sigma rowSum colSum
  rw [Finset.sum_comm]

lemma rowSum_add {n : ℕ} [NeZero n] (h k : HRaw n) :
    rowSum (h + k) = rowSum h + rowSum k := by
  funext t
  simp [rowSum, Finset.sum_add_distrib]

lemma colSum_add {n : ℕ} [NeZero n] (h k : HRaw n) :
    colSum (h + k) = colSum h + colSum k := by
  funext s
  simp [colSum, Finset.sum_add_distrib]

noncomputable def rowSeed {n : ℕ} [NeZero n] (r : Profile n) : Profile n :=
  fun t => r t + if t = 0 then sigma r else 0

lemma sigma_rowSeed_eq_zero {n : ℕ} [NeZero n] (r : Profile n) :
    sigma (rowSeed r) = 0 := by
  unfold sigma rowSeed
  rw [Finset.sum_add_distrib]
  have hsingle : (∑ x : I n, if x = 0 then sigma r else 0) = sigma r := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro t _ ht
      simp [ht]
    · simp
  rw [hsingle]
  exact F_add_self (sigma r)

noncomputable def rowColBalancedBaseMap {n : ℕ} [NeZero n] : HRaw n → RowColBalancedBase n
  | h => ⟨(rowSum h, colSum h), sigma_rowSum_eq_sigma_colSum (h := h)⟩

noncomputable def rowColBalancedBaseLift {n : ℕ} [NeZero n] (rc : RowColBalancedBase n) : HRaw n :=
  fun t s =>
    (if s = 0 then rowSeed rc.1.1 t else 0) + (if t = 0 then rc.1.2 s else 0)

lemma rowSum_rowColBalancedBaseLift {n : ℕ} [NeZero n] (rc : RowColBalancedBase n) :
    rowSum (rowColBalancedBaseLift (n := n) rc) = rc.1.1 := by
  rcases rc with ⟨⟨r, c⟩, hrc⟩
  funext t
  by_cases ht : t = 0
  · subst ht
    unfold rowSum rowColBalancedBaseLift
    rw [Finset.sum_add_distrib, Finset.sum_eq_single 0]
    · have hseed : (if (0 : I n) = 0 then rowSeed r 0 else 0) = r 0 + sigma r := by
        simp [rowSeed]
      have hsigma : (∑ x : I n, if (0 : I n) = 0 then c x else 0) = sigma c := by
        simp [sigma]
      rw [hseed, hsigma, hrc]
      have hs : sigma c + sigma c = 0 := by
        exact F_add_self (sigma c)
      have hs' : sigma c + (sigma c + r 0) = r 0 := by
        simpa [add_assoc] using congrArg (fun z : F => z + r 0) hs
      simpa [add_assoc, add_left_comm, add_comm] using hs'
    · intro s _ hs
      simp [hs]
    · simp
  · unfold rowSum rowColBalancedBaseLift
    rw [Finset.sum_add_distrib, Finset.sum_eq_single 0]
    · simp [rowSeed, ht]
    · intro s _ hs
      simp [hs]
    · simp

lemma colSum_rowColBalancedBaseLift {n : ℕ} [NeZero n] (rc : RowColBalancedBase n) :
    colSum (rowColBalancedBaseLift (n := n) rc) = rc.1.2 := by
  rcases rc with ⟨⟨r, c⟩, hrc⟩
  funext s
  by_cases hs : s = 0
  · subst hs
    unfold colSum rowColBalancedBaseLift
    rw [Finset.sum_add_distrib]
    have hleft : (∑ x : I n, (if (0 : I n) = 0 then rowSeed r x else 0)) = sigma (rowSeed r) := by
      simp [sigma]
    have hright : (∑ x : I n, (if x = 0 then c 0 else 0)) = c 0 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro t _ ht
        simp [ht]
      · simp
    rw [hleft, hright, sigma_rowSeed_eq_zero]
    simp
  · unfold colSum rowColBalancedBaseLift
    rw [Finset.sum_add_distrib, Finset.sum_eq_zero]
    · rw [Finset.sum_eq_single 0]
      · simp [hs]
      · intro t _ ht
        simp [ht]
      · simp
    · intro t ht
      simp [hs]

noncomputable def hResidualBase {n : ℕ} [NeZero n] (h : HRaw n) : HRaw n :=
  h + rowColBalancedBaseLift (n := n) (rowColBalancedBaseMap (n := n) h)

lemma hResidualBase_mem_HAdmissible {n : ℕ} [NeZero n] (h : HRaw n) :
    hResidualBase (n := n) h ∈ HAdmissible (n := n) := by
  constructor
  · change rowSum (hResidualBase (n := n) h) = 0
    rw [show hResidualBase (n := n) h =
        h + rowColBalancedBaseLift (n := n) (rowColBalancedBaseMap (n := n) h) by rfl]
    rw [rowSum_add, rowSum_rowColBalancedBaseLift]
    funext t
    simp [rowColBalancedBaseMap, F_add_self]
  · change colSum (hResidualBase (n := n) h) = 0
    rw [show hResidualBase (n := n) h =
        h + rowColBalancedBaseLift (n := n) (rowColBalancedBaseMap (n := n) h) by rfl]
    rw [colSum_add, colSum_rowColBalancedBaseLift]
    funext s
    simp [rowColBalancedBaseMap, F_add_self]

noncomputable def hFunToRowColHAdmissibleBase {n : ℕ} [NeZero n] :
    HRaw n → RowColBalancedBase n × HAdmissible (n := n) :=
  fun h => (rowColBalancedBaseMap (n := n) h, ⟨hResidualBase (n := n) h, hResidualBase_mem_HAdmissible (n := n) h⟩)

noncomputable def rowColHAdmissibleBaseToHFun {n : ℕ} [NeZero n] :
    RowColBalancedBase n × HAdmissible (n := n) → HRaw n
  | (rc, kh) => rowColBalancedBaseLift (n := n) rc + kh.1

lemma rowColHAdmissibleBaseToHFun_hFunToRowColHAdmissibleBase {n : ℕ} [NeZero n] (h : HRaw n) :
    rowColHAdmissibleBaseToHFun (n := n) (hFunToRowColHAdmissibleBase (n := n) h) = h := by
  funext t s
  simp [rowColHAdmissibleBaseToHFun, hFunToRowColHAdmissibleBase, hResidualBase,
    add_assoc, add_left_comm, add_comm, F_add_self]

lemma rowColBalancedBaseMap_add_hAdmissible {n : ℕ} [NeZero n] (rc : RowColBalancedBase n)
    {k : HRaw n} (hk : k ∈ HAdmissible (n := n)) :
    rowColBalancedBaseMap (n := n) (rowColBalancedBaseLift (n := n) rc + k) = rc := by
  rcases rc with ⟨⟨r, c⟩, hrc⟩
  have hkrow : rowSum k = 0 := hk.1
  have hkcol : colSum k = 0 := hk.2
  apply Subtype.ext
  apply Prod.ext
  · funext t
    have hkrowt := congrFun hkrow t
    simp [rowColBalancedBaseMap, rowSum_add, rowSum_rowColBalancedBaseLift, hkrowt]
  · funext s
    have hkcols := congrFun hkcol s
    simp [rowColBalancedBaseMap, colSum_add, colSum_rowColBalancedBaseLift, hkcols]

lemma hFunToRowColHAdmissibleBase_rowColHAdmissibleBaseToHFun {n : ℕ} [NeZero n]
    (x : RowColBalancedBase n × HAdmissible (n := n)) :
    hFunToRowColHAdmissibleBase (n := n) (rowColHAdmissibleBaseToHFun (n := n) x) = x := by
  rcases x with ⟨rc, kh⟩
  rcases kh with ⟨k, hk⟩
  have hmap :
      rowColBalancedBaseMap (n := n) (rowColHAdmissibleBaseToHFun (n := n) (rc, ⟨k, hk⟩)) = rc := by
    exact rowColBalancedBaseMap_add_hAdmissible (n := n) rc hk
  have hmap' :
      rowColBalancedBaseMap (n := n) (k + rowColBalancedBaseLift (n := n) rc) = rc := by
    simpa [add_comm] using rowColBalancedBaseMap_add_hAdmissible (n := n) rc hk
  apply Prod.ext
  · exact hmap
  · apply Subtype.ext
    funext t s
    simp [hFunToRowColHAdmissibleBase, rowColHAdmissibleBaseToHFun, hResidualBase, hmap',
      add_assoc, add_left_comm, add_comm, F_add_self]

noncomputable def hFunEquivRowColHAdmissibleBase {n : ℕ} [NeZero n] :
    HRaw n ≃ (RowColBalancedBase n × HAdmissible (n := n)) where
  toFun := hFunToRowColHAdmissibleBase (n := n)
  invFun := rowColHAdmissibleBaseToHFun (n := n)
  left_inv := rowColHAdmissibleBaseToHFun_hFunToRowColHAdmissibleBase (n := n)
  right_inv := hFunToRowColHAdmissibleBase_rowColHAdmissibleBaseToHFun (n := n)

lemma natCard_hRaw {n : ℕ} [NeZero n] :
    Nat.card (HRaw n) = 2 ^ (n ^ 2) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F, finrank_hRaw]

lemma finrank_HAdmissible {n : ℕ} [NeZero n] :
    Module.finrank F (HAdmissible (n := n)) = (n - 1) ^ 2 := by
  have hcard :
      Nat.card (HRaw n) = Nat.card (RowColBalancedBase n) * Nat.card (HAdmissible (n := n)) := by
    calc
      Nat.card (HRaw n) = Nat.card (RowColBalancedBase n × HAdmissible (n := n)) := by
        rw [Nat.card_congr (hFunEquivRowColHAdmissibleBase (n := n))]
      _ = Nat.card (RowColBalancedBase n) * Nat.card (HAdmissible (n := n)) := by
        rw [Nat.card_prod]
  rw [natCard_hRaw, natCard_rowColBalancedBase, Module.natCard_eq_pow_finrank (K := F)] at hcard
  simp [F] at hcard
  rw [← pow_add] at hcard
  have hexp : n ^ 2 = (2 * n - 1) + Module.finrank F (HAdmissible (n := n)) := by
    exact Nat.pow_right_injective (by omega : 1 < 2) hcard
  have hdim : Module.finrank F (HAdmissible (n := n)) = n ^ 2 - (2 * n - 1) := by
    omega
  have hsq : n ^ 2 - (2 * n - 1) = (n - 1) ^ 2 := by
    rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
    simp [pow_two]
    ring_nf
    omega
  rw [hdim, hsq]

lemma natCard_HAdmissible {n : ℕ} [NeZero n] :
    Nat.card (HAdmissible (n := n)) = 2 ^ ((n - 1) ^ 2) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F, finrank_HAdmissible]

structure ScalarVisibleCompat (b c n : ℕ) [NeZero n] where
  bcoef : ScalarBCoef c n
  ccoef : ScalarCCoef b n
  compat : ∀ y z,
    bcoef (sumY y) z + bcoef (sumY y + 1) z + ccoef y (sumZ z) + ccoef y (sumZ z + 1) = 0

theorem ScalarVisibleCompat.ext {b c n : ℕ} [NeZero n] {x y : ScalarVisibleCompat b c n}
    (hb : x.bcoef = y.bcoef) (hc : x.ccoef = y.ccoef) : x = y := by
  cases x
  cases y
  cases hb
  cases hc
  simp

noncomputable def buildScalarB {c n : ℕ} [NeZero n] (h : HRaw n) (u : ZCoord c n → F) :
    ScalarBCoef c n :=
  fun t z => u z + prefixT h t (sumZ z)

noncomputable def buildScalarC {b n : ℕ} [NeZero n] (h : HRaw n) (v : YCoord b n → F) :
    ScalarCCoef b n :=
  fun y r => v y + prefixR h (sumY y) r

noncomputable def visibleCore {n : ℕ} [NeZero n] (h : HRaw n) (t s : I n) : F :=
  prefixT h t s + prefixT h (t + 1) s + prefixR h t s + prefixR h t (s + 1)

lemma buildScalarB_zero {c n : ℕ} [NeZero n] (h : HRaw n) (u : ZCoord c n → F) (z : ZCoord c n) :
    buildScalarB h u 0 z = u z := by
  simp [buildScalarB, prefixT_zero]

lemma buildScalarC_zero {b n : ℕ} [NeZero n] (h : HRaw n) (v : YCoord b n → F) (y : YCoord b n) :
    buildScalarC h v y 0 = v y := by
  simp [buildScalarC, prefixR_zero]

lemma buildScalarB_natCast_succ {c n k : ℕ} [NeZero n] (h : HRaw n) (u : ZCoord c n → F)
    (z : ZCoord c n) (hk : k + 1 < n) :
    buildScalarB h u ((k + 1 : ℕ) : I n) z = buildScalarB h u (k : I n) z + h (k : I n) (sumZ z) := by
  rw [buildScalarB, buildScalarB, prefixT_natCast_succ (h := h) (s := sumZ z) hk]
  simp [add_assoc, add_left_comm, add_comm]

lemma buildScalarC_natCast_succ {b n k : ℕ} [NeZero n] (h : HRaw n) (v : YCoord b n → F)
    (y : YCoord b n) (hk : k + 1 < n) :
    buildScalarC h v y ((k + 1 : ℕ) : I n) = buildScalarC h v y (k : I n) + h (sumY y) (k : I n) := by
  rw [buildScalarC, buildScalarC, prefixR_natCast_succ (h := h) (t := sumY y) hk]
  simp [add_assoc, add_left_comm, add_comm]

noncomputable def visibleHData {b c n : ℕ} [NeZero n] (hc : 0 < c)
    (bc : ScalarVisibleCompat b c n) : HRaw n :=
  fun t s => bc.bcoef (t + 1) (zOfSum (n := n) hc s) + bc.bcoef t (zOfSum (n := n) hc s)

noncomputable def visibleUData {b c n : ℕ} [NeZero n] (bc : ScalarVisibleCompat b c n) :
    ZCoord c n → F :=
  fun z => bc.bcoef 0 z

noncomputable def visibleVData {b c n : ℕ} [NeZero n] (bc : ScalarVisibleCompat b c n) :
    YCoord b n → F :=
  fun y => bc.ccoef y 0

lemma visibleH_eq_c_increment {b c n : ℕ} [NeZero n] (hc : 0 < c)
    (bc : ScalarVisibleCompat b c n) (y : YCoord b n) (r : I n) :
    visibleHData (b := b) (c := c) (n := n) hc bc (sumY y) r =
      bc.ccoef y (r + 1) + bc.ccoef y r := by
  have hs := sumZ_zOfSum (n := n) hc r
  have hcompat := bc.compat y (zOfSum (n := n) hc r)
  have hs0 :
      bc.bcoef (sumY y) (zOfSum (n := n) hc r) + bc.bcoef (sumY y + 1) (zOfSum (n := n) hc r) +
          (bc.ccoef y r + bc.ccoef y (r + 1)) = 0 := by
    simpa [hs, add_assoc, add_left_comm, add_comm] using hcompat
  have hs' :
      bc.bcoef (sumY y) (zOfSum (n := n) hc r) + bc.bcoef (sumY y + 1) (zOfSum (n := n) hc r) =
        -(bc.ccoef y r + bc.ccoef y (r + 1)) := by
    exact eq_neg_of_add_eq_zero_left hs0
  simpa [visibleHData, add_assoc, add_left_comm, add_comm] using hs'

lemma visibleH_eq_b_increment {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c)
    (bc : ScalarVisibleCompat b c n) (t : I n) (z : ZCoord c n) :
    visibleHData (b := b) (c := c) (n := n) hc bc t (sumZ z) =
      bc.bcoef t z + bc.bcoef (t + 1) z := by
  have hsY : sumY (yOfSum (n := n) hb t) = t := sumY_yOfSum (n := n) hb t
  have hcompat := bc.compat (yOfSum (n := n) hb t) z
  have hs0 :
      bc.bcoef t z + bc.bcoef (t + 1) z +
          (bc.ccoef (yOfSum (n := n) hb t) (sumZ z) +
            bc.ccoef (yOfSum (n := n) hb t) (sumZ z + 1)) = 0 := by
    simpa [hsY, add_assoc, add_left_comm, add_comm] using hcompat
  have hc0 :
      bc.ccoef (yOfSum (n := n) hb t) (sumZ z) +
          bc.ccoef (yOfSum (n := n) hb t) (sumZ z + 1) =
        visibleHData (b := b) (c := c) (n := n) hc bc t (sumZ z) := by
    simpa [add_comm] using
      (visibleH_eq_c_increment (b := b) (c := c) (n := n) hc bc (yOfSum (n := n) hb t) (sumZ z)).symm
  have hneg :
      -(bc.ccoef (yOfSum (n := n) hb t) (sumZ z) +
          bc.ccoef (yOfSum (n := n) hb t) (sumZ z + 1)) =
        visibleHData (b := b) (c := c) (n := n) hc bc t (sumZ z) := by
    simpa [hc0]
  have hs' :
      bc.bcoef t z + bc.bcoef (t + 1) z =
        -(bc.ccoef (yOfSum (n := n) hb t) (sumZ z) +
          bc.ccoef (yOfSum (n := n) hb t) (sumZ z + 1)) := by
    exact eq_neg_of_add_eq_zero_left hs0
  calc
    visibleHData (b := b) (c := c) (n := n) hc bc t (sumZ z)
        = -(bc.ccoef (yOfSum (n := n) hb t) (sumZ z) +
            bc.ccoef (yOfSum (n := n) hb t) (sumZ z + 1)) := by
            simpa using hneg.symm
    _ = bc.bcoef t z + bc.bcoef (t + 1) z := by
          simpa [add_assoc, add_left_comm, add_comm] using hs'.symm

lemma buildScalarB_visibleData_eq {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c)
    (bc : ScalarVisibleCompat b c n) :
    buildScalarB (visibleHData (b := b) (c := c) (n := n) hc bc) (visibleUData bc) = bc.bcoef := by
  funext t z
  have hrec :
      ∀ k, k < n →
        buildScalarB (visibleHData (b := b) (c := c) (n := n) hc bc) (visibleUData bc) (k : I n) z =
          bc.bcoef (k : I n) z := by
    intro k hk
    induction' k with k ih
    · simpa [visibleUData] using buildScalarB_zero
        (h := visibleHData (b := b) (c := c) (n := n) hc bc) (u := visibleUData bc) z
    · rw [buildScalarB_natCast_succ
        (h := visibleHData (b := b) (c := c) (n := n) hc bc) (u := visibleUData bc) (z := z) hk]
      rw [ih (Nat.lt_of_succ_lt hk)]
      have hinc := visibleH_eq_b_increment (b := b) (c := c) (n := n) hb hc bc (k : I n) z
      rw [show visibleHData (b := b) (c := c) (n := n) hc bc (k : I n) (sumZ z) =
          bc.bcoef (k : I n) z + bc.bcoef ((k + 1 : ℕ) : I n) z by simpa using hinc]
      calc
        bc.bcoef (k : I n) z + (bc.bcoef (k : I n) z + bc.bcoef ((k + 1 : ℕ) : I n) z)
            = (bc.bcoef (k : I n) z + bc.bcoef (k : I n) z) + bc.bcoef ((k + 1 : ℕ) : I n) z := by
                ac_rfl
        _ = bc.bcoef ((k + 1 : ℕ) : I n) z := by
              simp [F_add_self]
  have htlt : t.val < n := by
    simpa using ZMod.val_lt t
  simpa using hrec t.val htlt

lemma buildScalarC_visibleData_eq {b c n : ℕ} [NeZero n] (hc : 0 < c)
    (bc : ScalarVisibleCompat b c n) :
    buildScalarC (visibleHData (b := b) (c := c) (n := n) hc bc) (visibleVData bc) = bc.ccoef := by
  funext y r
  have hrec :
      ∀ k, k < n →
        buildScalarC (visibleHData (b := b) (c := c) (n := n) hc bc) (visibleVData bc) y (k : I n) =
          bc.ccoef y (k : I n) := by
    intro k hk
    induction' k with k ih
    · simpa [visibleVData] using buildScalarC_zero
        (h := visibleHData (b := b) (c := c) (n := n) hc bc) (v := visibleVData bc) y
    · rw [buildScalarC_natCast_succ
        (h := visibleHData (b := b) (c := c) (n := n) hc bc) (v := visibleVData bc) (y := y) hk]
      rw [ih (Nat.lt_of_succ_lt hk)]
      have hinc := visibleH_eq_c_increment (b := b) (c := c) (n := n) hc bc y (k : I n)
      rw [show visibleHData (b := b) (c := c) (n := n) hc bc (sumY y) (k : I n) =
          bc.ccoef y ((k + 1 : ℕ) : I n) + bc.ccoef y (k : I n) by simpa using hinc]
      calc
        bc.ccoef y (k : I n) + (bc.ccoef y ((k + 1 : ℕ) : I n) + bc.ccoef y (k : I n))
            = (bc.ccoef y (k : I n) + bc.ccoef y (k : I n)) + bc.ccoef y ((k + 1 : ℕ) : I n) := by
                ac_rfl
        _ = bc.ccoef y ((k + 1 : ℕ) : I n) := by
              simp [F_add_self]
  have hrlt : r.val < n := by
    simpa using ZMod.val_lt r
  simpa using hrec r.val hrlt

lemma visibleHData_mem_HAdmissible {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c)
    (bc : ScalarVisibleCompat b c n) :
    visibleHData (b := b) (c := c) (n := n) hc bc ∈ HAdmissible (n := n) := by
  constructor
  · change rowSumMap (n := n) (visibleHData (b := b) (c := c) (n := n) hc bc) = 0
    funext t
    have hshift :
        (∑ s : I n, bc.ccoef (yOfSum (n := n) hb t) (s + 1)) =
          ∑ s : I n, bc.ccoef (yOfSum (n := n) hb t) s := by
      exact
        Fintype.sum_equiv (Equiv.addRight (1 : I n))
          (fun s : I n => bc.ccoef (yOfSum (n := n) hb t) (s + 1))
          (fun s : I n => bc.ccoef (yOfSum (n := n) hb t) s)
          (by intro s; simp)
    calc
      rowSum (visibleHData (b := b) (c := c) (n := n) hc bc) t
          = ∑ s : I n, (bc.ccoef (yOfSum (n := n) hb t) (s + 1) + bc.ccoef (yOfSum (n := n) hb t) s) := by
              refine Finset.sum_congr rfl ?_
              intro s hs
              simpa using visibleH_eq_c_increment (b := b) (c := c) (n := n) hc bc (yOfSum (n := n) hb t) s
      _ = (∑ s : I n, bc.ccoef (yOfSum (n := n) hb t) (s + 1)) +
            ∑ s : I n, bc.ccoef (yOfSum (n := n) hb t) s := by
              rw [Finset.sum_add_distrib]
      _ = 0 := by
            rw [hshift]
            exact F_add_self _
  · change colSumMap (n := n) (visibleHData (b := b) (c := c) (n := n) hc bc) = 0
    funext s
    have hshift :
        (∑ t : I n, bc.bcoef (t + 1) (zOfSum (n := n) hc s)) =
          ∑ t : I n, bc.bcoef t (zOfSum (n := n) hc s) := by
      exact
        Fintype.sum_equiv (Equiv.addRight (1 : I n))
          (fun t : I n => bc.bcoef (t + 1) (zOfSum (n := n) hc s))
          (fun t : I n => bc.bcoef t (zOfSum (n := n) hc s))
          (by intro t; simp)
    calc
      colSum (visibleHData (b := b) (c := c) (n := n) hc bc) s
          = ∑ t : I n, (bc.bcoef t (zOfSum (n := n) hc s) + bc.bcoef (t + 1) (zOfSum (n := n) hc s)) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              have hinc := visibleH_eq_b_increment (b := b) (c := c) (n := n) hb hc bc t (zOfSum (n := n) hc s)
              simpa [add_assoc, add_left_comm, add_comm] using hinc
      _ = (∑ t : I n, bc.bcoef t (zOfSum (n := n) hc s)) +
            ∑ t : I n, bc.bcoef (t + 1) (zOfSum (n := n) hc s) := by
              rw [Finset.sum_add_distrib]
      _ = 0 := by
            rw [hshift]
            exact F_add_self _

lemma visibleCore_natCast_eq_zero {n k l : ℕ} [NeZero n] (h : HRaw n)
    (hk : k + 1 < n) (hl : l + 1 < n) :
    visibleCore h (k : I n) (l : I n) = 0 := by
  rw [visibleCore]
  rw [show ((k : I n) + 1) = (((k + 1 : ℕ) : I n)) by simp]
  rw [show ((l : I n) + 1) = (((l + 1 : ℕ) : I n)) by simp]
  rw [prefixT_natCast_succ (h := h) (s := (l : I n)) hk,
    prefixR_natCast_succ (h := h) (t := (k : I n)) hl]
  simp [add_assoc, add_left_comm, add_comm, F_add_self]

lemma fin_natCast_eq_self {m : ℕ} (x : Fin (m + 1)) :
    (((x : ℕ) : I (m + 1))) = x := by
  apply Fin.ext
  change (x : ℕ) % (m + 1) = x
  exact Nat.mod_eq_of_lt x.2

lemma natCast_pred_add_one_eq_zero {n : ℕ} [NeZero n] :
    (((n - 1 : ℕ) : I n) + 1) = 0 := by
  have hn : n - 1 + 1 = n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n)))
  calc
    (((n - 1 : ℕ) : I n) + 1) = (((n - 1) + 1 : ℕ) : I n) := by simp
    _ = (n : I n) := by rw [hn]
    _ = 0 := ZMod.natCast_self n

lemma natCast_val_add_one {n : ℕ} [NeZero n] (t : I n) (ht : t.val + 1 < n) :
    ((t.val : I n) + 1) = (((t.val + 1 : ℕ) : I n)) := by
  rw [show t = ((t.val : ℕ) : I n) by exact (ZMod.natCast_zmod_val t).symm]
  simp

lemma rowSum_eq_zero_of_mem_HAdmissible {n : ℕ} [NeZero n] {h : HRaw n}
    (hh : h ∈ HAdmissible (n := n)) (t : I n) :
    rowSum h t = 0 := by
  have hker : rowSumMap (n := n) h = 0 := hh.1
  simpa [rowSumMap] using congrFun hker t

lemma colSum_eq_zero_of_mem_HAdmissible {n : ℕ} [NeZero n] {h : HRaw n}
    (hh : h ∈ HAdmissible (n := n)) (s : I n) :
    colSum h s = 0 := by
  have hker : colSumMap (n := n) h = 0 := hh.2
  simpa [colSumMap] using congrFun hker s

lemma prefixT_last_eq_of_colSum_eq_zero {n : ℕ} [NeZero n] (h : HRaw n) (s : I n)
    (hs : colSum h s = 0) :
    prefixT h ((n - 1 : ℕ) : I n) s = h ((n - 1 : ℕ) : I n) s := by
  cases n with
  | zero =>
      cases (NeZero.ne (n := 0) rfl)
  | succ m =>
      change prefixT h ((m : ℕ) : I (m + 1)) s = h ((m : ℕ) : I (m + 1)) s
      rw [prefixT, ZMod.val_natCast_of_lt (Nat.lt_succ_self m)]
      change Finset.sum (Finset.range m) (fun k => h ((k : ℕ) : I (m + 1)) s) =
        h ((m : ℕ) : I (m + 1)) s
      have hsum0 : (∑ x : Fin (m + 1), h x s) = 0 := by
        simpa [colSum, I] using hs
      have hsum0' : (∑ x : Fin (m + 1), h ((x : ℕ) : I (m + 1)) s) = 0 := by
        refine Eq.trans ?_ hsum0
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [fin_natCast_eq_self]
      rw [Fin.sum_univ_eq_sum_range (fun k => h ((k : ℕ) : I (m + 1)) s) (m + 1)] at hsum0'
      rw [Finset.sum_range_succ] at hsum0'
      have hneg :
          Finset.sum (Finset.range m) (fun k => h ((k : ℕ) : I (m + 1)) s) =
            -h ((m : ℕ) : I (m + 1)) s :=
        eq_neg_of_add_eq_zero_left hsum0'
      simpa using hneg

lemma prefixR_last_eq_of_rowSum_eq_zero {n : ℕ} [NeZero n] (h : HRaw n) (t : I n)
    (ht : rowSum h t = 0) :
    prefixR h t ((n - 1 : ℕ) : I n) = h t ((n - 1 : ℕ) : I n) := by
  cases n with
  | zero =>
      cases (NeZero.ne (n := 0) rfl)
  | succ m =>
      change prefixR h t ((m : ℕ) : I (m + 1)) = h t ((m : ℕ) : I (m + 1))
      rw [prefixR, ZMod.val_natCast_of_lt (Nat.lt_succ_self m)]
      change Finset.sum (Finset.range m) (fun k => h t ((k : ℕ) : I (m + 1))) =
        h t ((m : ℕ) : I (m + 1))
      have hsum0 : (∑ y : Fin (m + 1), h t y) = 0 := by
        simpa [rowSum, I] using ht
      have hsum0' : (∑ y : Fin (m + 1), h t ((y : ℕ) : I (m + 1))) = 0 := by
        refine Eq.trans ?_ hsum0
        refine Finset.sum_congr rfl ?_
        intro y hy
        rw [fin_natCast_eq_self]
      rw [Fin.sum_univ_eq_sum_range (fun k => h t ((k : ℕ) : I (m + 1))) (m + 1)] at hsum0'
      rw [Finset.sum_range_succ] at hsum0'
      have hneg :
          Finset.sum (Finset.range m) (fun k => h t ((k : ℕ) : I (m + 1))) =
            -h t ((m : ℕ) : I (m + 1)) :=
        eq_neg_of_add_eq_zero_left hsum0'
      simpa using hneg

lemma val_add_one_lt_or_eq_pred {n : ℕ} [NeZero n] (t : I n) :
    t.val + 1 < n ∨ t = ((n - 1 : ℕ) : I n) := by
  by_cases ht : t.val + 1 < n
  · exact Or.inl ht
  · right
    apply ZMod.val_injective
    have hlast : n - 1 < n := Nat.pred_lt (NeZero.ne n)
    have hval : t.val < n := ZMod.val_lt t
    have : t.val = n - 1 := by omega
    rw [ZMod.val_natCast_of_lt hlast, this]

lemma visibleCore_eq_zero_of_mem_HAdmissible {n : ℕ} [NeZero n] {h : HRaw n}
    (hh : h ∈ HAdmissible (n := n)) (t s : I n) :
    visibleCore h t s = 0 := by
  rcases val_add_one_lt_or_eq_pred (n := n) t with ht | rfl
  · rcases val_add_one_lt_or_eq_pred (n := n) s with hs | rfl
    · rw [← ZMod.natCast_zmod_val t, ← ZMod.natCast_zmod_val s]
      simpa using visibleCore_natCast_eq_zero (h := h) (k := t.val) (l := s.val) ht hs
    · rw [visibleCore, natCast_pred_add_one_eq_zero, prefixR_zero]
      rw [← ZMod.natCast_zmod_val t, natCast_val_add_one t ht]
      rw [prefixT_natCast_succ (h := h) (s := ((n - 1 : ℕ) : I n)) ht]
      have hrow := rowSum_eq_zero_of_mem_HAdmissible (n := n) hh t
      have hlast := prefixR_last_eq_of_rowSum_eq_zero (h := h) t hrow
      simp [hlast, add_assoc, add_left_comm, add_comm, F_add_self]
  · rcases val_add_one_lt_or_eq_pred (n := n) s with hs | rfl
    · rw [visibleCore, natCast_pred_add_one_eq_zero, prefixT_zero]
      rw [← ZMod.natCast_zmod_val s, natCast_val_add_one s hs]
      rw [prefixR_natCast_succ (h := h) (t := ((n - 1 : ℕ) : I n)) hs]
      have hcol := colSum_eq_zero_of_mem_HAdmissible (n := n) hh s
      have hlast := prefixT_last_eq_of_colSum_eq_zero (h := h) s hcol
      simp [hlast, add_assoc, add_left_comm, add_comm, F_add_self]
    · rw [visibleCore, natCast_pred_add_one_eq_zero, prefixT_zero, prefixR_zero]
      have hcol := colSum_eq_zero_of_mem_HAdmissible (n := n) hh ((n - 1 : ℕ) : I n)
      have hrow := rowSum_eq_zero_of_mem_HAdmissible (n := n) hh ((n - 1 : ℕ) : I n)
      have hlastT := prefixT_last_eq_of_colSum_eq_zero (h := h) ((n - 1 : ℕ) : I n) hcol
      have hlastR := prefixR_last_eq_of_rowSum_eq_zero (h := h) ((n - 1 : ℕ) : I n) hrow
      simp [hlastT, hlastR, add_assoc, add_left_comm, add_comm, F_add_self]

lemma prefixT_pair_eq_of_mem_HAdmissible {n : ℕ} [NeZero n] {h : HRaw n}
    (hh : h ∈ HAdmissible (n := n)) (t s : I n) :
    prefixT h t s + prefixT h (t + 1) s = h t s := by
  rcases val_add_one_lt_or_eq_pred (n := n) t with ht | rfl
  · rw [← ZMod.natCast_zmod_val t, natCast_val_add_one t ht]
    rw [prefixT_natCast_succ (h := h) (s := s) ht]
    simp [add_assoc, add_left_comm, add_comm, F_add_self]
  · rw [natCast_pred_add_one_eq_zero, prefixT_zero]
    simpa using prefixT_last_eq_of_colSum_eq_zero (h := h) s (colSum_eq_zero_of_mem_HAdmissible hh s)

noncomputable def build_mem_scalarVisibleCompat_of_mem_HAdmissible {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (u : ZCoord c n → F) (v : YCoord b n → F) :
    ScalarVisibleCompat b c n where
  bcoef := buildScalarB h.1 u
  ccoef := buildScalarC h.1 v
  compat y z := by
    have hzero := visibleCore_eq_zero_of_mem_HAdmissible (n := n) h.2 (sumY y) (sumZ z)
    calc
      buildScalarB h.1 u (sumY y) z + buildScalarB h.1 u (sumY y + 1) z +
          buildScalarC h.1 v y (sumZ z) + buildScalarC h.1 v y (sumZ z + 1)
          = (u z + u z) + (v y + v y) + visibleCore h.1 (sumY y) (sumZ z) := by
              simp [buildScalarB, buildScalarC, visibleCore, add_assoc, add_left_comm, add_comm]
      _ = visibleCore h.1 (sumY y) (sumZ z) := by
            simp [add_assoc, add_left_comm, add_comm, F_add_self]
      _ = 0 := hzero

lemma visibleHData_build_eq {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c)
    (h : HAdmissible (n := n)) (u : ZCoord c n → F) (v : YCoord b n → F) :
    visibleHData (b := b) (c := c) (n := n) hc
      (build_mem_scalarVisibleCompat_of_mem_HAdmissible (b := b) (c := c) (n := n)
        hb hc h u v) = h.1 := by
  funext t s
  calc
    visibleHData (b := b) (c := c) (n := n) hc
        (build_mem_scalarVisibleCompat_of_mem_HAdmissible (b := b) (c := c) (n := n)
          hb hc h u v) t s
        = u (zOfSum (n := n) hc s) +
            (u (zOfSum (n := n) hc s) + (prefixT h.1 t s + prefixT h.1 (t + 1) s)) := by
            simp [build_mem_scalarVisibleCompat_of_mem_HAdmissible, visibleHData, buildScalarB,
              add_assoc, add_left_comm, add_comm, sumZ_zOfSum (n := n) hc s]
    _ = prefixT h.1 t s + prefixT h.1 (t + 1) s := by
          calc
            u (zOfSum (n := n) hc s) +
                (u (zOfSum (n := n) hc s) + (prefixT h.1 t s + prefixT h.1 (t + 1) s))
                = (u (zOfSum (n := n) hc s) + u (zOfSum (n := n) hc s)) +
                    (prefixT h.1 t s + prefixT h.1 (t + 1) s) := by
                      ac_rfl
            _ = prefixT h.1 t s + prefixT h.1 (t + 1) s := by
                  simp [F_add_self]
    _ = h.1 t s := prefixT_pair_eq_of_mem_HAdmissible h.2 t s

lemma visibleUData_build_eq {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c)
    (h : HAdmissible (n := n)) (u : ZCoord c n → F) (v : YCoord b n → F) :
    visibleUData
      (build_mem_scalarVisibleCompat_of_mem_HAdmissible (b := b) (c := c) (n := n) hb hc h u v) = u := by
  funext z
  exact buildScalarB_zero h.1 u z

lemma visibleVData_build_eq {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c)
    (h : HAdmissible (n := n)) (u : ZCoord c n → F) (v : YCoord b n → F) :
    visibleVData
      (build_mem_scalarVisibleCompat_of_mem_HAdmissible (b := b) (c := c) (n := n) hb hc h u v) = v := by
  funext y
  exact buildScalarC_zero h.1 v y

noncomputable def scalarVisibleToData {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    ScalarVisibleCompat b c n → HAdmissible n × (ZCoord c n → F) × (YCoord b n → F)
  | bc =>
      (⟨visibleHData (b := b) (c := c) (n := n) hc bc,
          visibleHData_mem_HAdmissible (b := b) (c := c) (n := n) hb hc bc⟩,
        visibleUData bc, visibleVData bc)

noncomputable def dataToScalarVisible {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    HAdmissible n × (ZCoord c n → F) × (YCoord b n → F) → ScalarVisibleCompat b c n
  | ⟨h, u, v⟩ =>
      build_mem_scalarVisibleCompat_of_mem_HAdmissible (b := b) (c := c) (n := n) hb hc h u v

lemma dataToScalarVisible_left_inv {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c)
    (bc : ScalarVisibleCompat b c n) :
    dataToScalarVisible (b := b) (c := c) (n := n) hb hc
      (scalarVisibleToData (b := b) (c := c) (n := n) hb hc bc) = bc := by
  apply ScalarVisibleCompat.ext
  · exact buildScalarB_visibleData_eq (b := b) (c := c) (n := n) hb hc bc
  · exact buildScalarC_visibleData_eq (b := b) (c := c) (n := n) hc bc

lemma scalarVisibleToData_right_inv {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c)
    (x : HAdmissible n × (ZCoord c n → F) × (YCoord b n → F)) :
    scalarVisibleToData (b := b) (c := c) (n := n) hb hc
      (dataToScalarVisible (b := b) (c := c) (n := n) hb hc x) = x := by
  rcases x with ⟨h, u, v⟩
  apply Prod.ext
  · apply Subtype.ext
    exact visibleHData_build_eq (b := b) (c := c) (n := n) hb hc h u v
  · apply Prod.ext
    · exact visibleUData_build_eq (b := b) (c := c) (n := n) hb hc h u v
    · exact visibleVData_build_eq (b := b) (c := c) (n := n) hb hc h u v

noncomputable def scalarVisibleEquiv {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    ScalarVisibleCompat b c n ≃ HAdmissible n × (ZCoord c n → F) × (YCoord b n → F) where
  toFun := scalarVisibleToData (b := b) (c := c) (n := n) hb hc
  invFun := dataToScalarVisible (b := b) (c := c) (n := n) hb hc
  left_inv := dataToScalarVisible_left_inv (b := b) (c := c) (n := n) hb hc
  right_inv := scalarVisibleToData_right_inv (b := b) (c := c) (n := n) hb hc

noncomputable def scalarVisibleCompatEquivSubtype {b c n : ℕ} [NeZero n] :
    ScalarVisibleCompat b c n ≃
      { bc : ScalarBCoef c n × ScalarCCoef b n //
          ∀ y z,
            bc.1 (sumY y) z + bc.1 (sumY y + 1) z + bc.2 y (sumZ z) + bc.2 y (sumZ z + 1) = 0 } where
  toFun := fun x => ⟨(x.bcoef, x.ccoef), x.compat⟩
  invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

noncomputable instance instFintypeHAdmissible {n : ℕ} [NeZero n] : Fintype (HAdmissible n) := by
  classical
  exact Fintype.ofFinite (HAdmissible n)

noncomputable instance instFintypeScalarVisibleCompat {b c n : ℕ} [NeZero n] :
    Fintype (ScalarVisibleCompat b c n) := by
  classical
  exact Fintype.ofEquiv
    { bc : ScalarBCoef c n × ScalarCCoef b n //
        ∀ y z,
          bc.1 (sumY y) z + bc.1 (sumY y + 1) z + bc.2 y (sumZ z) + bc.2 y (sumZ z + 1) = 0 }
    (scalarVisibleCompatEquivSubtype (b := b) (c := c) (n := n)).symm

lemma card_zFunctions {c n : ℕ} [NeZero n] :
    Fintype.card (ZCoord c n → F) = 2 ^ (n ^ c) := by
  rw [Fintype.card_fun, card_ZCoord]
  simp [F, ZMod.card]

lemma card_yFunctions {b n : ℕ} [NeZero n] :
    Fintype.card (YCoord b n → F) = 2 ^ (n ^ b) := by
  rw [Fintype.card_fun, card_YCoord]
  simp [F, ZMod.card]

lemma card_HAdmissible {n : ℕ} [NeZero n] :
    Fintype.card (HAdmissible n) = 2 ^ ((n - 1) ^ 2) := by
  rw [← Nat.card_eq_fintype_card, natCard_HAdmissible]

theorem card_scalarVisibleSpace_closed {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ScalarVisibleCompat b c n) = 2 ^ (n ^ b + n ^ c + (n - 1) ^ 2) := by
  rw [Fintype.card_congr (scalarVisibleEquiv (b := b) (c := c) (n := n) hb hc)]
  rw [Fintype.card_prod, Fintype.card_prod, card_HAdmissible, card_zFunctions, card_yFunctions]
  calc
    2 ^ ((n - 1) ^ 2) * (2 ^ (n ^ c) * 2 ^ (n ^ b))
        = 2 ^ ((n - 1) ^ 2) * 2 ^ (n ^ c + n ^ b) := by
            rw [← Nat.pow_add]
    _ = 2 ^ ((n - 1) ^ 2 + (n ^ c + n ^ b)) := by
          rw [← Nat.pow_add]
    _ = 2 ^ (n ^ b + n ^ c + (n - 1) ^ 2) := by
          congr 1
          ac_rfl

end Core3loop
