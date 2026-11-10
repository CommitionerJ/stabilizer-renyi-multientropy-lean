import Core3loop.VisibleSpace

open scoped BigOperators

namespace Core3loop

abbrev MatrixFun (n : ℕ) := I n → I n → F

noncomputable def Cagg {b n : ℕ} [NeZero n] (c : ScalarCCoef b n) (t r : I n) : F :=
  ∑ y : YCoord b n, if sumY y = t then c y r else 0

noncomputable def TScalarFun {b c n : ℕ} [NeZero n] (ccoef : ScalarCCoef b n) : ScalarBCoef c n :=
  fun t z => Cagg ccoef t (sumZ z) + Cagg ccoef (t - 1) (sumZ z + 1)

noncomputable def CaggMap {b n : ℕ} [NeZero n] : ScalarCCoef b n →ₗ[F] MatrixFun n where
  toFun := Cagg
  map_add' := by
    intro c d
    funext t r
    change (∑ y : YCoord b n, if sumY y = t then c y r + d y r else 0) =
      (∑ y : YCoord b n, if sumY y = t then c y r else 0) +
        ∑ y : YCoord b n, if sumY y = t then d y r else 0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro y hy
    by_cases hyt : sumY y = t <;> simp [hyt]
  map_smul' := by
    intro a c
    funext t r
    change (∑ y : YCoord b n, if sumY y = t then a * c y r else 0) =
      a * ∑ y : YCoord b n, if sumY y = t then c y r else 0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y hy
    by_cases hyt : sumY y = t <;> simp [hyt, Pi.smul_apply]

noncomputable def TScalar {b c n : ℕ} [NeZero n] : ScalarCCoef b n →ₗ[F] ScalarBCoef c n where
  toFun := TScalarFun
  map_add' := by
    intro c₁ c₂
    have hagg : Cagg (c₁ + c₂) = Cagg c₁ + Cagg c₂ := by
      funext t r
      exact congrFun (congrFun ((CaggMap (b := b) (n := n)).map_add c₁ c₂) t) r
    funext t z
    simp [TScalarFun, hagg, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a ccoef
    have hagg : Cagg (a • ccoef) = a • Cagg ccoef := by
      funext t r
      exact congrFun (congrFun ((CaggMap (b := b) (n := n)).map_smul a ccoef) t) r
    funext t z
    simp [TScalarFun, hagg, Pi.smul_apply, mul_add]

noncomputable def Dfun {n : ℕ} (m : MatrixFun n) : MatrixFun n :=
  fun t s => m t s + m (t - 1) (s + 1)

noncomputable def diagConst {n : ℕ} (μ : Profile n) : MatrixFun n :=
  fun t s => μ (t + s)

noncomputable def diagConstMap {n : ℕ} : Profile n →ₗ[F] MatrixFun n where
  toFun := diagConst
  map_add' := by
    intro μ ν
    funext t s
    simp [diagConst]
  map_smul' := by
    intro a μ
    funext t s
    simp [diagConst, Pi.smul_apply]

noncomputable def D {n : ℕ} : MatrixFun n →ₗ[F] MatrixFun n where
  toFun := Dfun
  map_add' := by
    intro m₁ m₂
    funext t s
    simp [Dfun, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a m
    funext t s
    simp [Dfun, Pi.smul_apply, mul_add]

noncomputable def expandMatrix {c n : ℕ} [NeZero n] : MatrixFun n →ₗ[F] ScalarBCoef c n where
  toFun := fun m t z => m t (sumZ z)
  map_add' := by
    intro m₁ m₂
    funext t z
    simp
  map_smul' := by
    intro a m
    funext t z
    simp [Pi.smul_apply]

noncomputable def liftMatrix {b n : ℕ} [NeZero n] (hb : 0 < b) (m : MatrixFun n) : ScalarCCoef b n :=
  fun y s => if y = yOfSum (n := n) hb (sumY y) then m (sumY y) s else 0

lemma Cagg_liftMatrix {b n : ℕ} [NeZero n] (hb : 0 < b) (m : MatrixFun n) :
    Cagg (liftMatrix (n := n) hb m) = m := by
  funext t s
  unfold Cagg liftMatrix
  rw [Finset.sum_eq_single (yOfSum (n := n) hb t)]
  · simp
  · intro y _ hy
    by_cases hyt : sumY y = t
    · have hy' : y ≠ yOfSum (n := n) hb (sumY y) := by
        simpa [hyt] using hy
      simp [hyt, hy']
      intro hy''
      exact False.elim (hy hy'')
    · simp [hyt]
  · simp

lemma Cagg_surjective {b n : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Surjective (Cagg (b := b) (n := n)) := by
  intro m
  exact ⟨liftMatrix (n := n) hb m, Cagg_liftMatrix (n := n) hb m⟩

lemma range_CaggMap_top {b n : ℕ} [NeZero n] (hb : 0 < b) :
    LinearMap.range (CaggMap (b := b) (n := n)) = ⊤ := by
  ext m
  constructor
  · intro hm
    simp
  · intro hm
    rcases Cagg_surjective (b := b) (n := n) hb m with ⟨c, rfl⟩
    exact ⟨c, rfl⟩

lemma Dfun_diagConst_zero {n : ℕ} (μ : Profile n) :
    Dfun (diagConst μ) = 0 := by
  funext t s
  unfold Dfun diagConst
  have hts : (t - 1) + (s + 1) = t + s := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hts]
  simpa using F_add_self (μ (t + s))

lemma diagConst_mem_ker_D {n : ℕ} (μ : Profile n) :
    diagConst μ ∈ LinearMap.ker (D (n := n)) := by
  change Dfun (diagConst μ) = 0
  exact Dfun_diagConst_zero μ

lemma diagConstMap_injective {n : ℕ} : Function.Injective (diagConstMap (n := n)) := by
  intro μ ν hμν
  funext s
  have hs := congrFun (congrFun hμν 0) s
  simpa [diagConstMap, diagConst] using hs

lemma expandMatrix_injective {c n : ℕ} [NeZero n] (hc : 0 < c) :
    Function.Injective (expandMatrix (c := c) (n := n)) := by
  intro m₁ m₂ h
  funext t s
  have hs := congrFun (congrFun h t) (zOfSum (n := n) hc s)
  simpa [expandMatrix, sumZ_zOfSum (n := n) hc s] using hs

lemma Dfun_eq_zero_iff_step {n : ℕ} (m : MatrixFun n) :
    Dfun m = 0 ↔ ∀ t s, m (t - 1) (s + 1) = m t s := by
  constructor
  · intro hm t s
    have hts := congrFun (congrFun hm t) s
    simp [Dfun] at hts
    have hts0 : m (t - 1) (s + 1) + m t s = 0 := by
      simpa [add_comm] using hts
    have hts' : m (t - 1) (s + 1) = -(m t s) := eq_neg_of_add_eq_zero_left hts0
    simpa using hts'
  · intro hstep
    funext t s
    simp [Dfun, hstep t s, F_add_self]

lemma mem_ker_D_iff_exists_diagConst {n : ℕ} [NeZero n] (m : MatrixFun n) :
    m ∈ LinearMap.ker (D (n := n)) ↔ ∃ μ : Profile n, m = diagConst μ := by
  constructor
  · intro hm
    let μ : Profile n := fun r => m r 0
    refine ⟨μ, ?_⟩
    funext t s
    let r : I n := t + s
    let g : I n → F := fun u => m (r - u) u
    have hstep : ∀ u : I n, g (u + 1) = g u := by
      intro u
      have hD : Dfun m = 0 := hm
      have hstep' := (Dfun_eq_zero_iff_step m).mp hD (r - u) u
      dsimp [g]
      have hleft : (r - u) - 1 = r - (u + 1) := by
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      simpa [hleft] using hstep'
    have hg := zmod_step_const g hstep s
    have hts : r - s = t := by
      dsimp [r]
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hg' : m (r - s) s = m r 0 := by
      simpa [g] using hg
    simpa [μ, diagConst, r, hts] using hg'
  · rintro ⟨μ, rfl⟩
    exact diagConst_mem_ker_D μ

lemma ker_D_eq_range_diagConstMap {n : ℕ} [NeZero n] :
    LinearMap.ker (D (n := n)) = LinearMap.range (diagConstMap (n := n)) := by
  ext m
  constructor
  · intro hm
    rcases (mem_ker_D_iff_exists_diagConst (n := n) m).mp hm with ⟨μ, rfl⟩
    exact ⟨μ, rfl⟩
  · rintro ⟨μ, rfl⟩
    exact diagConst_mem_ker_D μ

lemma finrank_ker_D {n : ℕ} [NeZero n] :
    Module.finrank F (LinearMap.ker (D (n := n))) = n := by
  rw [ker_D_eq_range_diagConstMap]
  rw [LinearMap.finrank_range_of_inj (R := F) (f := diagConstMap (n := n))
    (diagConstMap_injective (n := n))]
  simp [Profile, I, ZMod.card]

lemma finrank_range_D {n : ℕ} [NeZero n] :
    Module.finrank F (LinearMap.range (D (n := n))) = n ^ 2 - n := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (D (n := n))
  rw [finrank_ker_D] at hdim
  have hmat : Module.finrank F (MatrixFun n) = n ^ 2 := by
    change Module.finrank F (I n → I n → F) = n ^ 2
    rw [Module.finrank_pi_fintype (R := F) (M := fun _ : I n => I n → F)]
    calc
      ∑ _ : I n, Module.finrank F (I n → F) = n * n := by
        simp [Module.finrank_pi, I, ZMod.card]
      _ = n ^ 2 := by ring
  rw [hmat] at hdim
  omega

lemma TScalar_eq_expandMatrix_comp_D_comp_CaggMap {b c n : ℕ} [NeZero n] :
    TScalar (b := b) (c := c) (n := n) =
      ((expandMatrix (c := c) (n := n)).comp (D (n := n))).comp (CaggMap (b := b) (n := n)) := by
  ext ccoef t z
  rfl

theorem rank_TScalar {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    Module.finrank F (LinearMap.range (TScalar (b := b) (c := c) (n := n))) = n * (n - 1) := by
  rw [TScalar_eq_expandMatrix_comp_D_comp_CaggMap (b := b) (c := c) (n := n)]
  rw [LinearMap.range_comp_of_range_eq_top
    (g := (expandMatrix (c := c) (n := n)).comp (D (n := n)))
    (hf := range_CaggMap_top (b := b) (n := n) hb)]
  rw [LinearMap.range_comp]
  have hdominj :
      Function.Injective
        ((expandMatrix (c := c) (n := n)).domRestrict (LinearMap.range (D (n := n)))) := by
    intro x y hxy
    apply Subtype.ext
    exact expandMatrix_injective (c := c) (n := n) hc hxy
  have hmapfin :
      Module.finrank F ((LinearMap.range (D (n := n))).map (expandMatrix (c := c) (n := n))) =
        Module.finrank F (LinearMap.range (D (n := n))) := by
    rw [← LinearMap.range_domRestrict
      (K := LinearMap.range (D (n := n))) (f := expandMatrix (c := c) (n := n))]
    exact LinearMap.finrank_range_of_inj (R := F)
      (f := (expandMatrix (c := c) (n := n)).domRestrict (LinearMap.range (D (n := n)))) hdominj
  calc
    Module.finrank F ((LinearMap.range (D (n := n))).map (expandMatrix (c := c) (n := n))) =
        Module.finrank F (LinearMap.range (D (n := n))) := hmapfin
    _ = n ^ 2 - n := finrank_range_D (n := n)
    _ = n * (n - 1) := by
          rw [pow_two, Nat.mul_sub_left_distrib, mul_one]

lemma F_ne_zero_eq_one (a : F) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (ha rfl)
  · rfl

noncomputable def bPairScalar {c n : ℕ} [NeZero n]
    (b₁ b₂ : ScalarBCoef c n) : F :=
  ∑ t : I n, ∑ z : ZCoord c n, b₁ t z * b₂ t z

noncomputable def qLeftScalar {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) : F :=
  ∑ t : I n, ∑ z : ZCoord c n, bcoef t z * Cagg ccoef t (sumZ z)

noncomputable def qRightScalar {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) : F :=
  ∑ t : I n, ∑ z : ZCoord c n, bcoef t z * Cagg ccoef (t - 1) (sumZ z + 1)

noncomputable def qScalar {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) : F :=
  qLeftScalar bcoef ccoef + qRightScalar bcoef ccoef

lemma bPairScalar_TScalarFun_eq_qLeft_add_qRight {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    bPairScalar bcoef (TScalarFun (b := b) (c := c) (n := n) ccoef) =
      qLeftScalar bcoef ccoef + qRightScalar bcoef ccoef := by
  unfold bPairScalar TScalarFun qLeftScalar qRightScalar
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]

lemma qScalar_eq_bPair_TScalarFun {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    qScalar bcoef ccoef =
      bPairScalar bcoef (TScalarFun (b := b) (c := c) (n := n) ccoef) := by
  calc
    qScalar bcoef ccoef = qLeftScalar bcoef ccoef + qRightScalar bcoef ccoef := by
      rfl
    _ = bPairScalar bcoef (TScalarFun (b := b) (c := c) (n := n) ccoef) := by
      symm
      exact bPairScalar_TScalarFun_eq_qLeft_add_qRight (b := b) (c := c) (n := n) bcoef ccoef

lemma qScalar_eq_bPair_TScalar {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    qScalar bcoef ccoef =
      bPairScalar bcoef ((TScalar (b := b) (c := c) (n := n)) ccoef) := by
  simpa [TScalar] using qScalar_eq_bPair_TScalarFun (b := b) (c := c) (n := n) bcoef ccoef

abbrev ScalarBIndex (c n : ℕ) := I n × ZCoord c n

noncomputable def toggleAtScalarBCoef {c n : ℕ} [NeZero n]
    (u0 : ScalarBIndex c n) (bcoef : ScalarBCoef c n) : ScalarBCoef c n :=
  fun t z => bcoef t z + if (t, z) = u0 then 1 else 0

noncomputable def toggleEquivScalarBCoef {c n : ℕ} [NeZero n]
    (u0 : ScalarBIndex c n) : ScalarBCoef c n ≃ ScalarBCoef c n where
  toFun := toggleAtScalarBCoef u0
  invFun := toggleAtScalarBCoef u0
  left_inv := by
    intro bcoef
    funext t z
    by_cases h : (t, z) = u0
    · subst h
      have h11 : (1 : F) + 1 = 0 := by decide
      simp [toggleAtScalarBCoef, add_assoc, h11]
    · simp [toggleAtScalarBCoef, h]
  right_inv := by
    intro bcoef
    funext t z
    by_cases h : (t, z) = u0
    · subst h
      have h11 : (1 : F) + 1 = 0 := by decide
      simp [toggleAtScalarBCoef, add_assoc, h11]
    · simp [toggleAtScalarBCoef, h]

lemma toggleAtScalarBCoef_apply {c n : ℕ} [NeZero n]
    (u0 : ScalarBIndex c n) (bcoef : ScalarBCoef c n) (t : I n) (z : ZCoord c n) :
    toggleAtScalarBCoef u0 bcoef t z = bcoef t z + if (t, z) = u0 then 1 else 0 := by
  rfl

lemma bPairScalar_toggleAtScalarBCoef {c n : ℕ} [NeZero n]
    (u0 : ScalarBIndex c n) (bcoef m : ScalarBCoef c n) (hm : m u0.1 u0.2 = 1) :
    bPairScalar (toggleAtScalarBCoef u0 bcoef) m = bPairScalar bcoef m + 1 := by
  rcases u0 with ⟨t0, z0⟩
  unfold bPairScalar
  simp_rw [toggleAtScalarBCoef_apply, add_mul, Finset.sum_add_distrib]
  have hs :
      ∑ t : I n, ∑ z : ZCoord c n, (if (t, z) = (t0, z0) then 1 else 0) * m t z = 1 := by
    rw [Finset.sum_eq_single t0]
    · rw [Finset.sum_eq_single z0]
      · simpa using hm
      · intro z _ hz
        simp [hz]
      · simp
    · intro t _ ht
      simp [ht]
    · simp
  rw [hs]

lemma sum_bitSign_bPairScalar {c n : ℕ} [NeZero n] (m : ScalarBCoef c n) :
    ∑ bcoef : ScalarBCoef c n, bitSign (bPairScalar bcoef m) =
      if m = 0 then Fintype.card (ScalarBCoef c n) else 0 := by
  classical
  by_cases hm : m = 0
  · simp [hm, bPairScalar, No13Migration.bitSign_zero]
  · have hex : ∃ u0 : ScalarBIndex c n, m u0.1 u0.2 ≠ 0 := by
      by_contra h
      apply hm
      funext t z
      by_cases htz : m t z = 0
      · exact htz
      · exact False.elim (h ⟨(t, z), htz⟩)
    rcases hex with ⟨u0, hu0⟩
    have hm1 : m u0.1 u0.2 = 1 := F_ne_zero_eq_one _ hu0
    let S : ℤ := ∑ bcoef : ScalarBCoef c n, bitSign (bPairScalar bcoef m)
    have htoggle :
        S = ∑ bcoef : ScalarBCoef c n,
          bitSign (bPairScalar (toggleAtScalarBCoef u0 bcoef) m) := by
      simpa [S] using
        (((toggleEquivScalarBCoef (c := c) (n := n) u0).symm.sum_comp
          (fun bcoef : ScalarBCoef c n => bitSign (bPairScalar bcoef m))).symm)
    have hneg :
        ∑ bcoef : ScalarBCoef c n, bitSign (bPairScalar (toggleAtScalarBCoef u0 bcoef) m)
          = -S := by
      calc
        ∑ bcoef : ScalarBCoef c n, bitSign (bPairScalar (toggleAtScalarBCoef u0 bcoef) m)
            = ∑ bcoef : ScalarBCoef c n, -bitSign (bPairScalar bcoef m) := by
                refine Finset.sum_congr rfl ?_
                intro bcoef hbcoef
                rw [bPairScalar_toggleAtScalarBCoef (c := c) (n := n) u0 bcoef m hm1]
                simpa using No13Migration.bitSign_add_one (bPairScalar bcoef m)
        _ = -S := by
              simp [S]
    have hs : S = -S := by
      calc
        S = ∑ bcoef : ScalarBCoef c n, bitSign (bPairScalar (toggleAtScalarBCoef u0 bcoef) m) := htoggle
        _ = -S := hneg
    have hzero : S = 0 := by linarith
    simp [S, hm, hzero]

lemma sum_bitSign_qScalar {b c n : ℕ} [NeZero n] (ccoef : ScalarCCoef b n) :
    ∑ bcoef : ScalarBCoef c n, bitSign (qScalar bcoef ccoef) =
      if (TScalar (b := b) (c := c) (n := n)) ccoef = 0 then Fintype.card (ScalarBCoef c n) else 0 := by
  simpa [qScalar_eq_bPair_TScalar] using
    sum_bitSign_bPairScalar (c := c) (n := n) (m := (TScalar (b := b) (c := c) (n := n)) ccoef)

lemma finrank_scalarBCoef {c n : ℕ} [NeZero n] :
    Module.finrank F (ScalarBCoef c n) = n ^ (c + 1) := by
  change Module.finrank F (I n → ZCoord c n → F) = n ^ (c + 1)
  rw [Module.finrank_pi_fintype (R := F) (M := fun _ : I n => ZCoord c n → F)]
  calc
    ∑ _ : I n, Module.finrank F (ZCoord c n → F) = n * n ^ c := by
      simp [Module.finrank_pi, card_ZCoord, I, ZMod.card]
    _ = n ^ (c + 1) := by
      symm
      simpa [Nat.mul_comm] using (Nat.pow_succ n c)

lemma finrank_scalarCCoef {b n : ℕ} [NeZero n] :
    Module.finrank F (ScalarCCoef b n) = n ^ (b + 1) := by
  change Module.finrank F (YCoord b n → I n → F) = n ^ (b + 1)
  rw [Module.finrank_pi_fintype (R := F) (M := fun _ : YCoord b n => I n → F)]
  calc
    ∑ _ : YCoord b n, Module.finrank F (I n → F) = n ^ b * n := by
      simp [Module.finrank_pi, card_YCoord, I, ZMod.card]
    _ = n ^ (b + 1) := by
      symm
      simpa [Nat.mul_comm] using (Nat.pow_succ n b)

lemma card_scalarBCoef {c n : ℕ} [NeZero n] :
    Fintype.card (ScalarBCoef c n) = 2 ^ (n ^ (c + 1)) := by
  rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F)]
  simp [F, finrank_scalarBCoef (c := c) (n := n)]

lemma mul_pred_le_pow_succ {c n : ℕ} [NeZero n] (hc : 0 < c) :
    n * (n - 1) ≤ n ^ (c + 1) := by
  have hmul : n * (n - 1) ≤ n * n := by
    exact Nat.mul_le_mul_left n (Nat.pred_le _)
  have hpow : n * n ≤ n ^ (c + 1) := by
    have h2le : 2 ≤ c + 1 := by omega
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
    simpa [pow_two] using Nat.pow_le_pow_right hn1 h2le
  exact le_trans hmul hpow

lemma finrank_ker_TScalar {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    Module.finrank F (LinearMap.ker (TScalar (b := b) (c := c) (n := n))) =
      n ^ (b + 1) - n * (n - 1) := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (TScalar (b := b) (c := c) (n := n))
  rw [rank_TScalar (b := b) (c := c) (n := n) hb hc, finrank_scalarCCoef (b := b) (n := n)] at hdim
  omega

lemma natCard_ker_TScalar {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    Nat.card (LinearMap.ker (TScalar (b := b) (c := c) (n := n))) =
      2 ^ (n ^ (b + 1) - n * (n - 1)) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simpa [F, finrank_ker_TScalar (b := b) (c := c) (n := n) hb hc]

lemma ordinary_pair_factor_closed {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    ∑ bcoef : ScalarBCoef c n, ∑ ccoef : ScalarCCoef b n, bitSign (qScalar bcoef ccoef) =
      (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1)) := by
  classical
  have hsubB : n * (n - 1) ≤ n ^ (b + 1) := mul_pred_le_pow_succ (c := b) (n := n) hb
  calc
    ∑ bcoef : ScalarBCoef c n, ∑ ccoef : ScalarCCoef b n, bitSign (qScalar bcoef ccoef)
        = ∑ ccoef : ScalarCCoef b n, ∑ bcoef : ScalarBCoef c n, bitSign (qScalar bcoef ccoef) := by
            rw [Finset.sum_comm]
    _ =
      ∑ ccoef : ScalarCCoef b n,
        (((if (TScalar (b := b) (c := c) (n := n)) ccoef = 0 then
            Fintype.card (ScalarBCoef c n) else 0 : ℕ) : ℤ)) := by
          refine Finset.sum_congr rfl ?_
          intro ccoef hccoef
          simpa using sum_bitSign_qScalar (b := b) (c := c) (n := n) ccoef
    _ =
      ∑ ccoef : ScalarCCoef b n,
        (if (TScalar (b := b) (c := c) (n := n)) ccoef = 0 then
          (Fintype.card (ScalarBCoef c n) : ℤ) else 0) := by
            simp_rw [Nat.cast_ite, Nat.cast_zero]
    _ = (Fintype.card (ScalarBCoef c n) : ℤ) *
          Fintype.card {ccoef : ScalarCCoef b n //
            (TScalar (b := b) (c := c) (n := n)) ccoef = 0} := by
          rw [← Finset.sum_filter]
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [← Fintype.card_of_subtype
            (p := fun ccoef : ScalarCCoef b n =>
              (TScalar (b := b) (c := c) (n := n)) ccoef = 0)
            (s := Finset.univ.filter fun ccoef : ScalarCCoef b n =>
              (TScalar (b := b) (c := c) (n := n)) ccoef = 0)]
          · ring
          · intro ccoef
            simp
    _ = (2 : ℤ) ^ (n ^ (c + 1)) * (2 : ℤ) ^ (n ^ (b + 1) - n * (n - 1)) := by
          have hker :
              Fintype.card {ccoef : ScalarCCoef b n //
                (TScalar (b := b) (c := c) (n := n)) ccoef = 0} =
                2 ^ (n ^ (b + 1) - n * (n - 1)) := by
            rw [← Nat.card_eq_fintype_card]
            simpa [LinearMap.mem_ker] using natCard_ker_TScalar (b := b) (c := c) (n := n) hb hc
          rw [card_scalarBCoef (c := c) (n := n), hker]
          rw [show ((2 ^ (n ^ (c + 1)) : ℕ) : ℤ) = (2 : ℤ) ^ (n ^ (c + 1)) by
            simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ (c + 1)))]
          rw [show ((2 ^ (n ^ (b + 1) - n * (n - 1)) : ℕ) : ℤ) =
              (2 : ℤ) ^ (n ^ (b + 1) - n * (n - 1)) by
            simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ (b + 1) - n * (n - 1)))]
    _ = (2 : ℤ) ^ ((n ^ (c + 1)) + (n ^ (b + 1) - n * (n - 1))) := by
          rw [← pow_add]
    _ = (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1)) := by
          congr 1
          calc
            n ^ (c + 1) + (n ^ (b + 1) - n * (n - 1))
                = n ^ (c + 1) + n ^ (b + 1) - n * (n - 1) := by
                    rw [Nat.add_sub_assoc hsubB]
            _ = n ^ (b + 1) + n ^ (c + 1) - n * (n - 1) := by
                  rw [Nat.add_comm]

theorem ordinary_pair_sum_closed {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    ∑ bcoef : ScalarBCoef c n, ∑ bcoef' : ScalarBCoef c n,
      ∑ ccoef : ScalarCCoef b n, ∑ ccoef' : ScalarCCoef b n,
        bitSign (qScalar bcoef ccoef' + qScalar bcoef' ccoef) =
      (2 : ℤ) ^ (2 * (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1))) := by
  have hfac :
      ∑ bcoef : ScalarBCoef c n, ∑ ccoef : ScalarCCoef b n, bitSign (qScalar bcoef ccoef) =
        (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1)) :=
    ordinary_pair_factor_closed (b := b) (c := c) (n := n) hb hc
  calc
    ∑ bcoef : ScalarBCoef c n, ∑ bcoef' : ScalarBCoef c n,
        ∑ ccoef : ScalarCCoef b n, ∑ ccoef' : ScalarCCoef b n,
          bitSign (qScalar bcoef ccoef' + qScalar bcoef' ccoef)
      =
        ∑ bcoef : ScalarBCoef c n, ∑ bcoef' : ScalarBCoef c n,
          ∑ ccoef' : ScalarCCoef b n, ∑ ccoef : ScalarCCoef b n,
            bitSign (qScalar bcoef ccoef') * bitSign (qScalar bcoef' ccoef) := by
              simp_rw [No13Migration.bitSign_add]
              refine Finset.sum_congr rfl ?_
              intro bcoef hbcoef
              refine Finset.sum_congr rfl ?_
              intro bcoef' hbcoef'
              rw [Finset.sum_comm]
    _ =
      ∑ bcoef : ScalarBCoef c n, ∑ ccoef' : ScalarCCoef b n,
        ∑ bcoef' : ScalarBCoef c n, ∑ ccoef : ScalarCCoef b n,
          bitSign (qScalar bcoef ccoef') * bitSign (qScalar bcoef' ccoef) := by
            refine Finset.sum_congr rfl ?_
            intro bcoef hbcoef
            rw [Finset.sum_comm]
    _ =
      ∑ bcoef : ScalarBCoef c n, ∑ ccoef : ScalarCCoef b n,
        bitSign (qScalar bcoef ccoef) *
          (∑ bcoef : ScalarBCoef c n, ∑ ccoef : ScalarCCoef b n, bitSign (qScalar bcoef ccoef)) := by
            refine Finset.sum_congr rfl ?_
            intro bcoef hbcoef
            refine Finset.sum_congr rfl ?_
            intro ccoef hccoef
            symm
            simp_rw [Finset.mul_sum]
    _ =
      (∑ bcoef : ScalarBCoef c n, ∑ ccoef : ScalarCCoef b n, bitSign (qScalar bcoef ccoef)) *
        (∑ bcoef : ScalarBCoef c n, ∑ ccoef : ScalarCCoef b n, bitSign (qScalar bcoef ccoef)) := by
          symm
          simp_rw [Finset.sum_mul]
    _ =
      ((2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1))) *
        ((2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1))) := by
          simpa using congrArg (fun z : ℤ => z * z) hfac
    _ =
      (2 : ℤ) ^
        ((n ^ (b + 1) + n ^ (c + 1) - n * (n - 1)) +
          (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1))) := by
            rw [← pow_add]
    _ = (2 : ℤ) ^ (2 * (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1))) := by
          congr 1
          ring

end Core3loop
