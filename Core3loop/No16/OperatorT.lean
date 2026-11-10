import No16.VisibleSpace

open scoped BigOperators

namespace No16

abbrev MatrixFun (n : ℕ) := I n → I n → F

noncomputable def bPair {n : ℕ} [NeZero n] (b₁ b₂ : BCoef n) : F :=
  ∑ t : I n, ∑ p : I n, ∑ q' : I n, b₁ t p q' * b₂ t p q'

noncomputable def cPair {n : ℕ} [NeZero n] (c₁ c₂ : CCoef n) : F :=
  ∑ v : I n, ∑ w : I n, ∑ r : I n, c₁ v w r * c₂ v w r

noncomputable def Cagg {n : ℕ} [NeZero n] (c : CCoef n) (t s : I n) : F :=
  ∑ v : I n, c v (t - v) s

noncomputable def Tfun {n : ℕ} [NeZero n] (c : CCoef n) : BCoef n :=
  fun t p q' => Cagg c t (p + q') + Cagg c (t - 1) (p + q' + 1)

noncomputable def Xagg {n : ℕ} [NeZero n] (b : BCoef n) (t s : I n) : F :=
  ∑ p : I n, b t p (s - p)

noncomputable def TadjFun {n : ℕ} [NeZero n] (b : BCoef n) : CCoef n :=
  fun v w r => Xagg b (v + w) r + Xagg b (v + w + 1) (r - 1)

lemma sum_reindex_addLeft {n : ℕ} [NeZero n] (a : I n) (f : I n → F) :
    ∑ x : I n, f (a + x) = ∑ t : I n, f t := by
  simpa using (Equiv.sum_comp (Equiv.addLeft a) f)

noncomputable def qLeft {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) : F :=
  ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, b (v + w) p q' * c v w (p + q')

noncomputable def qRight {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) : F :=
  ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, b (v + w + 1) p q' * c v w (p + q' + 1)

noncomputable def pairLeft {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) : F :=
  ∑ t : I n, ∑ p : I n, ∑ q' : I n, b t p q' * ∑ v : I n, c v (t - v) (p + q')

noncomputable def pairRight {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) : F :=
  ∑ t : I n, ∑ p : I n, ∑ q' : I n, b t p q' * ∑ v : I n, c v (t - 1 - v) (p + q' + 1)

noncomputable def T {n : ℕ} [NeZero n] : CCoef n →ₗ[F] BCoef n where
  toFun := Tfun
  map_add' := by
    intro c d
    funext t p q'
    simp [Tfun, Cagg, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a c
    funext t p q'
    simp [Tfun, Cagg, Finset.mul_sum, Pi.smul_apply, mul_add]

noncomputable def Tadj {n : ℕ} [NeZero n] : BCoef n →ₗ[F] CCoef n where
  toFun := TadjFun
  map_add' := by
    intro b₁ b₂
    funext v w r
    simp [TadjFun, Xagg, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a b
    funext v w r
    simp [TadjFun, Xagg, Finset.mul_sum, Pi.smul_apply, mul_add]

noncomputable def Dfun {n : ℕ} (m : MatrixFun n) : MatrixFun n :=
  fun t s => m t s + m (t - 1) (s + 1)

noncomputable def diagConst {n : ℕ} (μ : I n → F) : MatrixFun n :=
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

noncomputable def CaggMap {n : ℕ} [NeZero n] : CCoef n →ₗ[F] MatrixFun n where
  toFun := Cagg
  map_add' := by
    intro c d
    funext t s
    simp [Cagg, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    funext t s
    simp [Cagg, Finset.mul_sum, Pi.smul_apply]

noncomputable def expandMatrix {n : ℕ} : MatrixFun n →ₗ[F] BCoef n where
  toFun := fun m t p q' => m t (p + q')
  map_add' := by
    intro m₁ m₂
    funext t p q'
    simp
  map_smul' := by
    intro a m
    funext t p q'
    simp [Pi.smul_apply]

def liftMatrix {n : ℕ} (m : MatrixFun n) : CCoef n :=
  fun v w s => if v = 0 then m w s else 0

lemma Cagg_liftMatrix {n : ℕ} [NeZero n] (m : MatrixFun n) :
    Cagg (liftMatrix m) = m := by
  funext t s
  unfold Cagg liftMatrix
  rw [Finset.sum_eq_single 0]
  · simp
  · intro v _ hv
    simp [hv]
  · simp

lemma Dfun_diagConst_zero {n : ℕ} (μ : I n → F) :
    Dfun (diagConst μ) = 0 := by
  funext t s
  unfold Dfun diagConst
  have hts : (t - 1) + (s + 1) = t + s := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hts]
  simpa using F_add_self (μ (t + s))

lemma Cagg_surjective {n : ℕ} [NeZero n] : Function.Surjective (Cagg (n := n)) := by
  intro m
  refine ⟨liftMatrix m, ?_⟩
  exact Cagg_liftMatrix m

lemma range_CaggMap_top {n : ℕ} [NeZero n] :
    LinearMap.range (CaggMap (n := n)) = ⊤ := by
  ext m
  constructor
  · intro hm
    simp
  · intro hm
    refine ⟨liftMatrix m, ?_⟩
    exact Cagg_liftMatrix m

lemma diagConst_mem_ker_D {n : ℕ} (μ : I n → F) :
    diagConst μ ∈ LinearMap.ker (D (n := n)) := by
  change Dfun (diagConst μ) = 0
  exact Dfun_diagConst_zero μ

lemma expandMatrix_injective {n : ℕ} : Function.Injective (expandMatrix (n := n)) := by
  intro m₁ m₂ h
  funext t s
  have hs := congrFun (congrFun (congrFun h t) s) 0
  simpa [expandMatrix] using hs

lemma diagConstMap_injective {n : ℕ} : Function.Injective (diagConstMap (n := n)) := by
  intro μ ν hμν
  funext s
  have hs := congrFun (congrFun hμν 0) s
  simpa [diagConstMap, diagConst] using hs

lemma sum_const_I_even {n : ℕ} [NeZero n] (hn : Even n) (c : F) :
    ∑ _ : I n, c = 0 := by
  rcases hn with ⟨k, rfl⟩
  fin_cases c
  · change (∑ _ : I (k + k), (0 : F)) = 0
    simp
  · change (∑ _ : I (k + k), (1 : F)) = 0
    rw [show (∑ _ : I (k + k), (1 : F)) = (((k + k : ℕ) : F)) by
      simp [I, ZMod.card]]
    rw [Nat.cast_add]
    exact F_add_self (k : F)

lemma Xagg_buildB_even {n : ℕ} [NeZero n] (hn : Even n) (h : HFun n) (u : UVFun n)
    (t s : I n) :
    Xagg (buildB h u) t s = uvAgg u s := by
  unfold Xagg buildB uvAgg
  rw [Finset.sum_add_distrib]
  have hconst : ∑ p : I n, prefixT h t (p + (s - p)) = 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (sum_const_I_even (n := n) hn (prefixT h t s))
  rw [hconst, add_zero]

lemma Cagg_buildC_even {n : ℕ} [NeZero n] (hn : Even n) (h : HFun n) (v : UVFun n)
    (t s : I n) :
    Cagg (buildC h v) t s = uvAgg v t := by
  unfold Cagg buildC uvAgg
  rw [Finset.sum_add_distrib]
  have hconst : ∑ x : I n, prefixR h (x + (t - x)) s = 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (sum_const_I_even (n := n) hn (prefixR h t s))
  rw [hconst, add_zero]

lemma Tadj_buildB_even {n : ℕ} [NeZero n] (hn : Even n) (h : HFun n) (u : UVFun n)
    (v w r : I n) :
    TadjFun (buildB h u) v w r = uvAgg u r + uvAgg u (r - 1) := by
  simp [TadjFun, Xagg_buildB_even (n := n) hn h u]

lemma T_buildC_even {n : ℕ} [NeZero n] (hn : Even n) (h : HFun n) (v : UVFun n)
    (t p q' : I n) :
    Tfun (buildC h v) t p q' = uvAgg v t + uvAgg v (t - 1) := by
  simp [Tfun, Cagg_buildC_even (n := n) hn h v]

lemma Tadj_buildB_eq_zero_iff {n : ℕ} [NeZero n] (hn : Even n) (h : HFun n) (u : UVFun n) :
    Tadj (n := n) (buildB h u) = 0 ↔ ∃ a : F, uvAgg u = constProfile a := by
  constructor
  · intro hzero
    change TadjFun (buildB h u) = 0 at hzero
    let μ : Profile n := uvAgg u
    have hstep : ∀ s : I n, μ (s + 1) = μ s := by
      intro s
      have hs := congrFun (congrFun (congrFun hzero 0) 0) (s + 1)
      have hs0 : μ (s + 1) + μ s = 0 := by
        simpa [μ, Tadj_buildB_even (n := n) hn h u] using hs
      have hs' : μ (s + 1) = -(μ s) := eq_neg_of_add_eq_zero_left hs0
      simpa [μ] using hs'
    refine ⟨μ 0, ?_⟩
    funext s
    simpa [μ, constProfile] using zmod_step_const μ hstep s
  · rintro ⟨a, ha⟩
    change TadjFun (buildB h u) = 0
    funext v w r
    rw [Tadj_buildB_even (n := n) hn h u, ha]
    simp [constProfile, F_add_self]

lemma T_buildC_eq_zero_iff {n : ℕ} [NeZero n] (hn : Even n) (h : HFun n) (v : UVFun n) :
    T (n := n) (buildC h v) = 0 ↔ ∃ a : F, uvAgg v = constProfile a := by
  constructor
  · intro hzero
    change Tfun (buildC h v) = 0 at hzero
    let μ : Profile n := uvAgg v
    have hstep : ∀ s : I n, μ (s + 1) = μ s := by
      intro s
      have hs := congrFun (congrFun (congrFun hzero (s + 1)) 0) 0
      have hs0 : μ (s + 1) + μ s = 0 := by
        simpa [μ, T_buildC_even (n := n) hn h v] using hs
      have hs' : μ (s + 1) = -(μ s) := eq_neg_of_add_eq_zero_left hs0
      simpa [μ] using hs'
    refine ⟨μ 0, ?_⟩
    funext s
    simpa [μ, constProfile] using zmod_step_const μ hstep s
  · rintro ⟨a, ha⟩
    change Tfun (buildC h v) = 0
    funext t p q'
    rw [T_buildC_even (n := n) hn h v, ha]
    simp [constProfile, F_add_self]

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
      simpa [hleft]
        using hstep'
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
    Module.finrank F (LinearMap.range (D (n := n))) = n^2 - n := by
  have hdim :=
    LinearMap.finrank_range_add_finrank_ker (D (n := n))
  rw [finrank_ker_D] at hdim
  have hmat : Module.finrank F (MatrixFun n) = n^2 := by
    change Module.finrank F (I n → I n → F) = n^2
    rw [Module.finrank_pi_fintype (R := F) (M := fun _ : I n => I n → F)]
    calc
      ∑ _ : I n, Module.finrank F (I n → F) = n * n := by
        simp [Module.finrank_pi, I, ZMod.card]
      _ = n ^ 2 := by ring
  rw [hmat] at hdim
  omega

lemma T_eq_expandMatrix_comp_D_comp_CaggMap {n : ℕ} [NeZero n] :
    T (n := n) = ((expandMatrix (n := n)).comp (D (n := n))).comp (CaggMap (n := n)) := by
  ext c t p q'
  rfl

lemma finrank_range_T {n : ℕ} [NeZero n] :
    Module.finrank F (LinearMap.range (T (n := n))) = n * (n - 1) := by
  rw [T_eq_expandMatrix_comp_D_comp_CaggMap]
  rw [LinearMap.range_comp_of_range_eq_top (g := (expandMatrix (n := n)).comp (D (n := n)))
    (hf := range_CaggMap_top (n := n))]
  rw [LinearMap.range_comp]
  have hdominj :
      Function.Injective
        ((expandMatrix (n := n)).domRestrict (LinearMap.range (D (n := n)))) := by
    intro x y hxy
    apply Subtype.ext
    exact expandMatrix_injective (n := n) hxy
  have hmapfin :
      Module.finrank F ((LinearMap.range (D (n := n))).map (expandMatrix (n := n))) =
        Module.finrank F (LinearMap.range (D (n := n))) := by
    rw [← LinearMap.range_domRestrict
      (K := LinearMap.range (D (n := n))) (f := expandMatrix (n := n))]
    exact LinearMap.finrank_range_of_inj (R := F)
      (f := (expandMatrix (n := n)).domRestrict (LinearMap.range (D (n := n)))) hdominj
  calc
    Module.finrank F ((LinearMap.range (D (n := n))).map (expandMatrix (n := n))) =
        Module.finrank F (LinearMap.range (D (n := n))) := hmapfin
    _ = n^2 - n := finrank_range_D (n := n)
    _ = n * (n - 1) := by
      rw [pow_two, Nat.mul_sub_left_distrib, mul_one]

lemma finrank_CCoef {n : ℕ} [NeZero n] : Module.finrank F (CCoef n) = n^3 := by
  have hmat : Module.finrank F (I n → I n → F) = n^2 := by
    rw [Module.finrank_pi_fintype (R := F) (M := fun _ : I n => I n → F)]
    calc
      ∑ _ : I n, Module.finrank F (I n → F) = n * n := by
        simp [Module.finrank_pi, I, ZMod.card]
      _ = n ^ 2 := by ring
  change Module.finrank F (I n → I n → I n → F) = n^3
  rw [Module.finrank_pi_fintype (R := F) (M := fun _ : I n => I n → I n → F)]
  calc
    ∑ _ : I n, Module.finrank F (I n → I n → F) = n * n^2 := by
      simp [hmat, I, ZMod.card]
    _ = n ^ 3 := by ring

lemma finrank_ker_T {n : ℕ} [NeZero n] :
    Module.finrank F (LinearMap.ker (T (n := n))) = n^3 - n * (n - 1) := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (T (n := n))
  rw [finrank_range_T, finrank_CCoef] at hdim
  omega

lemma natCard_range_T {n : ℕ} [NeZero n] :
    Nat.card (LinearMap.range (T (n := n))) = 2 ^ (n * (n - 1)) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simpa [ZMod.card] using finrank_range_T (n := n)

lemma natCard_ker_T {n : ℕ} [NeZero n] :
    Nat.card (LinearMap.ker (T (n := n))) = 2 ^ (n^3 - n * (n - 1)) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simpa [ZMod.card] using finrank_ker_T (n := n)

lemma sum_pairLeft_inner_eq {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n)
    (v p q' : I n) :
    (∑ t : I n, b t p q' * c v (t - v) (p + q')) =
      ∑ w : I n, b (v + w) p q' * c v w (p + q') := by
  symm
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (sum_reindex_addLeft (a := v) (f := fun t : I n => b t p q' * c v (t - v) (p + q')))

lemma sum_pairRight_inner_eq {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n)
    (v p q' : I n) :
    (∑ t : I n, b t p q' * c v (t - 1 - v) (p + q' + 1)) =
      ∑ w : I n, b (v + (w + 1)) p q' * c v w (p + q' + 1) := by
  have hraw :=
    (sum_reindex_addLeft
      (a := v + 1)
      (f := fun t : I n => b t p q' * c v (t - (v + 1)) (p + q' + 1))).symm
  convert hraw using 1
  · refine Finset.sum_congr rfl ?_
    intro t ht
    have hs : t - (v + 1) = t - 1 - v := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hs]
  · refine Finset.sum_congr rfl ?_
    intro w hw
    have hb : (v + 1) + w = v + (w + 1) := by
      simp [add_assoc, add_left_comm, add_comm]
    have hc : v + (w + 1) - (v + 1) = w := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hb, hc]

lemma pairLeft_eq_qLeft {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) :
    pairLeft b c = qLeft b c := by
  have hpair :
      pairLeft b c =
        ∑ p : I n, ∑ q' : I n, ∑ v : I n, ∑ t : I n,
          b t p q' * c v (t - v) (p + q') := by
    unfold pairLeft
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro q' hq
    rw [Finset.sum_comm]
  have hqleft₁ :
      qLeft b c =
        ∑ v : I n, ∑ p : I n, ∑ q' : I n, ∑ w : I n,
          b (v + w) p q' * c v w (p + q') := by
    unfold qLeft
    refine Finset.sum_congr rfl ?_
    intro v hv
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.sum_comm]
  have hqleft₂ :
      (∑ v : I n, ∑ p : I n, ∑ q' : I n, ∑ w : I n,
          b (v + w) p q' * c v w (p + q')) =
        ∑ p : I n, ∑ q' : I n, ∑ v : I n, ∑ w : I n,
          b (v + w) p q' * c v w (p + q') := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.sum_comm]
  rw [hpair, hqleft₁, hqleft₂]
  refine Finset.sum_congr rfl ?_
  intro p hp
  refine Finset.sum_congr rfl ?_
  intro q' hq
  refine Finset.sum_congr rfl ?_
  intro v hv
  exact sum_pairLeft_inner_eq b c v p q'

lemma pairRight_eq_qRight {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) :
    pairRight b c = qRight b c := by
  have hpair :
      pairRight b c =
        ∑ p : I n, ∑ q' : I n, ∑ v : I n, ∑ t : I n,
          b t p q' * c v (t - 1 - v) (p + q' + 1) := by
    unfold pairRight
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro q' hq
    rw [Finset.sum_comm]
  have hqright₁ :
      qRight b c =
        ∑ v : I n, ∑ p : I n, ∑ q' : I n, ∑ w : I n,
          b (v + (w + 1)) p q' * c v w (p + q' + 1) := by
    unfold qRight
    refine Finset.sum_congr rfl ?_
    intro v hv
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro q' hq
    refine Finset.sum_congr rfl ?_
    intro w hw
    congr 1
    ac_rfl
  have hqright₂ :
      (∑ v : I n, ∑ p : I n, ∑ q' : I n, ∑ w : I n,
          b (v + (w + 1)) p q' * c v w (p + q' + 1)) =
        ∑ p : I n, ∑ q' : I n, ∑ v : I n, ∑ w : I n,
          b (v + (w + 1)) p q' * c v w (p + q' + 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.sum_comm]
  rw [hpair, hqright₁, hqright₂]
  refine Finset.sum_congr rfl ?_
  intro p hp
  refine Finset.sum_congr rfl ?_
  intro q' hq
  refine Finset.sum_congr rfl ?_
  intro v hv
  exact sum_pairRight_inner_eq b c v p q'

lemma q_eq_qLeft_add_qRight {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) :
    q b c = qLeft b c + qRight b c := by
  unfold q qLeft qRight
  simp_rw [Finset.sum_add_distrib]

lemma bPair_Tfun_eq_pairLeft_add_pairRight {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) :
    bPair b (Tfun c) = pairLeft b c + pairRight b c := by
  unfold bPair Tfun pairLeft pairRight Cagg
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]

lemma q_eq_bPair_Tfun {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) :
    q b c = bPair b (Tfun c) := by
  calc
    q b c = qLeft b c + qRight b c := q_eq_qLeft_add_qRight b c
    _ = pairLeft b c + pairRight b c := by
      rw [pairLeft_eq_qLeft, pairRight_eq_qRight]
    _ = bPair b (Tfun c) := by
      symm
      exact bPair_Tfun_eq_pairLeft_add_pairRight b c

lemma q_eq_bPair_T {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) :
    q b c = bPair b (T c) := by
  simpa [T] using q_eq_bPair_Tfun b c

lemma sum_cPairLeft_inner_eq {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n)
    (v w p : I n) :
    (∑ r : I n, b (v + w) p (r - p) * c v w r) =
      ∑ q' : I n, b (v + w) p q' * c v w (p + q') := by
  symm
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (sum_reindex_addLeft
      (a := p)
      (f := fun r : I n => b (v + w) p (r - p) * c v w r))

lemma sum_cPairRight_inner_eq {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n)
    (v w p : I n) :
    (∑ r : I n, b (v + w + 1) p ((r - 1) - p) * c v w r) =
      ∑ q' : I n, b (v + w + 1) p q' * c v w (p + q' + 1) := by
  have hraw :=
    (sum_reindex_addLeft
      (a := p + 1)
      (f := fun r : I n => b (v + w + 1) p (r - (p + 1)) * c v w r)).symm
  convert hraw using 1
  · refine Finset.sum_congr rfl ?_
    intro r hr
    have hs : r - (p + 1) = (r - 1) - p := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hs]
  · refine Finset.sum_congr rfl ?_
    intro q' hq'
    have hs : (p + 1) + q' = p + q' + 1 := by
      simp [add_assoc, add_left_comm, add_comm]
    have ht : p + q' + 1 - (p + 1) = q' := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hs, ht]

lemma cPair_TadjFun_eq_qLeft_add_qRight {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) :
    cPair (TadjFun b) c = qLeft b c + qRight b c := by
  unfold cPair TadjFun Xagg qLeft qRight
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]
  calc
    ∑ v : I n, ∑ w : I n, ∑ r : I n, (∑ p : I n, b (v + w) p (r - p)) * c v w r +
        ∑ v : I n, ∑ w : I n, ∑ r : I n, (∑ p : I n, b (v + w + 1) p ((r - 1) - p)) * c v w r
      = (∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ r : I n, b (v + w) p (r - p) * c v w r) +
          ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ r : I n, b (v + w + 1) p ((r - 1) - p) * c v w r := by
            rw [show (∑ v : I n, ∑ w : I n, ∑ r : I n, (∑ p : I n, b (v + w) p (r - p)) * c v w r)
              = ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ r : I n, b (v + w) p (r - p) * c v w r by
                refine Finset.sum_congr rfl ?_
                intro v hv
                refine Finset.sum_congr rfl ?_
                intro w hw
                calc
                  ∑ r : I n, (∑ p : I n, b (v + w) p (r - p)) * c v w r
                    = ∑ r : I n, ∑ p : I n, b (v + w) p (r - p) * c v w r := by
                        refine Finset.sum_congr rfl ?_
                        intro r hr
                        rw [Finset.sum_mul]
                  _ = ∑ p : I n, ∑ r : I n, b (v + w) p (r - p) * c v w r := by
                        rw [Finset.sum_comm]]
            rw [show (∑ v : I n, ∑ w : I n, ∑ r : I n, (∑ p : I n, b (v + w + 1) p ((r - 1) - p)) * c v w r)
              = ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ r : I n, b (v + w + 1) p ((r - 1) - p) * c v w r by
                refine Finset.sum_congr rfl ?_
                intro v hv
                refine Finset.sum_congr rfl ?_
                intro w hw
                calc
                  ∑ r : I n, (∑ p : I n, b (v + w + 1) p ((r - 1) - p)) * c v w r
                    = ∑ r : I n, ∑ p : I n, b (v + w + 1) p ((r - 1) - p) * c v w r := by
                        refine Finset.sum_congr rfl ?_
                        intro r hr
                        rw [Finset.sum_mul]
                  _ = ∑ p : I n, ∑ r : I n, b (v + w + 1) p ((r - 1) - p) * c v w r := by
                        rw [Finset.sum_comm]]
    _ = (∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, b (v + w) p q' * c v w (p + q')) +
          ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, b (v + w + 1) p q' * c v w (p + q' + 1) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro v hv
              refine Finset.sum_congr rfl ?_
              intro w hw
              refine Finset.sum_congr rfl ?_
              intro p hp
              exact sum_cPairLeft_inner_eq b c v w p
            · refine Finset.sum_congr rfl ?_
              intro v hv
              refine Finset.sum_congr rfl ?_
              intro w hw
              refine Finset.sum_congr rfl ?_
              intro p hp
              exact sum_cPairRight_inner_eq b c v w p

lemma q_eq_cPair_TadjFun {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) :
    q b c = cPair (TadjFun b) c := by
  calc
    q b c = qLeft b c + qRight b c := q_eq_qLeft_add_qRight b c
    _ = cPair (TadjFun b) c := by
      symm
      exact cPair_TadjFun_eq_qLeft_add_qRight b c

lemma q_eq_cPair_Tadj {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) :
    q b c = cPair (Tadj b) c := by
  simpa [Tadj] using q_eq_cPair_TadjFun b c

abbrev TripleI (n : ℕ) := I n × I n × I n

noncomputable def toggleAtBCoef {n : ℕ} [NeZero n] (u0 : TripleI n) (b : BCoef n) : BCoef n :=
  (bCoefEquivTriple n).symm fun u => (bCoefEquivTriple n b) u + if u = u0 then 1 else 0

noncomputable def toggleEquivBCoef {n : ℕ} [NeZero n] (u0 : TripleI n) : BCoef n ≃ BCoef n where
  toFun := toggleAtBCoef u0
  invFun := toggleAtBCoef u0
  left_inv b := by
    apply (bCoefEquivTriple n).injective
    funext u
    by_cases h : u = u0
    · have h11 : (1 : F) + 1 = 0 := by decide
      simpa [toggleAtBCoef, h, add_assoc] using h11
    · simp [toggleAtBCoef, h]
  right_inv b := by
    apply (bCoefEquivTriple n).injective
    funext u
    by_cases h : u = u0
    · have h11 : (1 : F) + 1 = 0 := by decide
      simpa [toggleAtBCoef, h, add_assoc] using h11
    · simp [toggleAtBCoef, h]

noncomputable def toggleAtCCoef {n : ℕ} [NeZero n] (u0 : TripleI n) (c : CCoef n) : CCoef n :=
  (cCoefEquivTriple n).symm fun u => (cCoefEquivTriple n c) u + if u = u0 then 1 else 0

noncomputable def toggleEquivCCoef {n : ℕ} [NeZero n] (u0 : TripleI n) : CCoef n ≃ CCoef n where
  toFun := toggleAtCCoef u0
  invFun := toggleAtCCoef u0
  left_inv c := by
    apply (cCoefEquivTriple n).injective
    funext u
    by_cases h : u = u0
    · have h11 : (1 : F) + 1 = 0 := by decide
      simpa [toggleAtCCoef, h, add_assoc] using h11
    · simp [toggleAtCCoef, h]
  right_inv c := by
    apply (cCoefEquivTriple n).injective
    funext u
    by_cases h : u = u0
    · have h11 : (1 : F) + 1 = 0 := by decide
      simpa [toggleAtCCoef, h, add_assoc] using h11
    · simp [toggleAtCCoef, h]

lemma toggleAtCCoef_apply {n : ℕ} [NeZero n] (u0 : TripleI n) (c : CCoef n) (v w r : I n) :
    toggleAtCCoef u0 c v w r = c v w r + if (v, w, r) = u0 then 1 else 0 := by
  rfl

lemma cPair_toggleAtCCoef {n : ℕ} [NeZero n] (u0 : TripleI n) (c m : CCoef n)
    (hm : (cCoefEquivTriple n m) u0 = 1) :
    cPair m (toggleAtCCoef u0 c) = cPair m c + 1 := by
  rcases u0 with ⟨v0, w0, r0⟩
  unfold cPair
  simp_rw [toggleAtCCoef_apply, mul_add, Finset.sum_add_distrib]
  have hs :
      ∑ v : I n, ∑ w : I n, ∑ r : I n, m v w r * (if (v, w, r) = (v0, w0, r0) then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single v0]
    · rw [Finset.sum_eq_single w0]
      · rw [Finset.sum_eq_single r0]
        · simpa using hm
        · intro r _ hr
          simp [hr]
        · simp
      · intro w _ hw
        simp [hw]
      · simp
    · intro v _ hv
      simp [hv]
    · simp
  rw [hs]

lemma sum_bitSign_cPair {n : ℕ} [NeZero n] (m : CCoef n) :
    ∑ c : CCoef n, bitSign (cPair m c) = if m = 0 then Fintype.card (CCoef n) else 0 := by
  classical
  by_cases hm : m = 0
  · simp [hm, cPair, bitSign_zero]
  · have hex : ∃ u0 : TripleI n, (cCoefEquivTriple n m) u0 ≠ 0 := by
      by_contra h
      apply hm
      apply (cCoefEquivTriple n).injective
      funext u
      by_cases hu : (cCoefEquivTriple n m) u = 0
      · exact hu
      · exact False.elim (h ⟨u, hu⟩)
    rcases hex with ⟨u0, hu0⟩
    have hm1 : (cCoefEquivTriple n m) u0 = 1 := F_ne_zero_eq_one _ hu0
    let S : ℤ := ∑ c : CCoef n, bitSign (cPair m c)
    have htoggle :
        S = ∑ c : CCoef n, bitSign (cPair m (toggleAtCCoef u0 c)) := by
      simpa [S] using
        (((toggleEquivCCoef (n := n) u0).symm.sum_comp
          (fun c : CCoef n => bitSign (cPair m c))).symm)
    have hneg :
        ∑ c : CCoef n, bitSign (cPair m (toggleAtCCoef u0 c)) = -S := by
      calc
        ∑ c : CCoef n, bitSign (cPair m (toggleAtCCoef u0 c))
            = ∑ c : CCoef n, -bitSign (cPair m c) := by
                refine Finset.sum_congr rfl ?_
                intro c hc
                rw [cPair_toggleAtCCoef (n := n) u0 c m hm1, bitSign_add_one]
        _ = -S := by simp [S]
    have hs : S = -S := by
      calc
        S = ∑ c : CCoef n, bitSign (cPair m (toggleAtCCoef u0 c)) := htoggle
        _ = -S := hneg
    have hzero : S = 0 := by linarith
    simp [S, hm, hzero]

lemma sum_bitSign_q_right {n : ℕ} [NeZero n] (b : BCoef n) :
    ∑ c : CCoef n, bitSign (q b c) = if Tadj b = 0 then Fintype.card (CCoef n) else 0 := by
  simpa [q_eq_cPair_Tadj] using sum_bitSign_cPair (n := n) (m := Tadj b)

lemma toggleAtBCoef_apply {n : ℕ} [NeZero n] (u0 : TripleI n) (b : BCoef n) (t p q' : I n) :
    toggleAtBCoef u0 b t p q' = b t p q' + if (t, p, q') = u0 then 1 else 0 := by
  rfl

lemma bPair_toggleAtBCoef {n : ℕ} [NeZero n] (u0 : TripleI n) (b m : BCoef n)
    (hm : (bCoefEquivTriple n m) u0 = 1) :
    bPair (toggleAtBCoef u0 b) m = bPair b m + 1 := by
  rcases u0 with ⟨t0, p0, q0⟩
  unfold bPair
  simp_rw [toggleAtBCoef_apply, add_mul, Finset.sum_add_distrib]
  have hs :
      ∑ t : I n, ∑ p : I n, ∑ q' : I n, (if (t, p, q') = (t0, p0, q0) then 1 else 0) * m t p q' = 1 := by
    rw [Finset.sum_eq_single t0]
    · rw [Finset.sum_eq_single p0]
      · rw [Finset.sum_eq_single q0]
        · simpa using hm
        · intro q' _ hq'
          simp [hq']
        · simp
      · intro p _ hp
        simp [hp]
      · simp
    · intro t _ ht
      simp [ht]
    · simp
  rw [hs]

lemma sum_bitSign_bPair {n : ℕ} [NeZero n] (m : BCoef n) :
    ∑ b : BCoef n, bitSign (bPair b m) = if m = 0 then Fintype.card (BCoef n) else 0 := by
  classical
  by_cases hm : m = 0
  · simp [hm, bPair, bitSign_zero]
  · have hex : ∃ u0 : TripleI n, (bCoefEquivTriple n m) u0 ≠ 0 := by
      by_contra h
      apply hm
      apply (bCoefEquivTriple n).injective
      funext u
      by_cases hu : (bCoefEquivTriple n m) u = 0
      · exact hu
      · exact False.elim (h ⟨u, hu⟩)
    rcases hex with ⟨u0, hu0⟩
    have hm1 : (bCoefEquivTriple n m) u0 = 1 := F_ne_zero_eq_one _ hu0
    let S : ℤ := ∑ b : BCoef n, bitSign (bPair b m)
    have htoggle :
        S = ∑ b : BCoef n, bitSign (bPair (toggleAtBCoef u0 b) m) := by
      simpa [S] using
        (((toggleEquivBCoef (n := n) u0).symm.sum_comp
          (fun b : BCoef n => bitSign (bPair b m))).symm)
    have hneg :
        ∑ b : BCoef n, bitSign (bPair (toggleAtBCoef u0 b) m) = -S := by
      calc
        ∑ b : BCoef n, bitSign (bPair (toggleAtBCoef u0 b) m)
            = ∑ b : BCoef n, -bitSign (bPair b m) := by
                refine Finset.sum_congr rfl ?_
                intro b hb
                rw [bPair_toggleAtBCoef (n := n) u0 b m hm1, bitSign_add_one]
        _ = -S := by simp [S]
    have hs : S = -S := by
      calc
        S = ∑ b : BCoef n, bitSign (bPair (toggleAtBCoef u0 b) m) := htoggle
        _ = -S := hneg
    have hzero : S = 0 := by linarith
    simp [S, hm, hzero]

lemma sum_bitSign_q {n : ℕ} [NeZero n] (c : CCoef n) :
    ∑ b : BCoef n, bitSign (q b c) = if T c = 0 then Fintype.card (BCoef n) else 0 := by
  simpa [q_eq_bPair_T] using sum_bitSign_bPair (n := n) (m := T c)

lemma ordinary_pair_factor {n : ℕ} [NeZero n] :
    ∑ b : BCoef n, ∑ c : CCoef n, bitSign (q b c) =
      (2 : ℤ) ^ (n ^ 3 + (n ^ 3 - n * (n - 1))) := by
  classical
  calc
    ∑ b : BCoef n, ∑ c : CCoef n, bitSign (q b c)
        = ∑ c : CCoef n, ∑ b : BCoef n, bitSign (q b c) := by
            rw [Finset.sum_comm]
    _ = ∑ c : CCoef n, (((if T c = 0 then Fintype.card (BCoef n) else 0 : ℕ) : ℤ)) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          simpa using (sum_bitSign_q (n := n) c)
    _ = ∑ c : CCoef n, (if T c = 0 then (Fintype.card (BCoef n) : ℤ) else 0) := by
          simp_rw [Nat.cast_ite, Nat.cast_zero]
    _ = (Fintype.card (BCoef n) : ℤ) * Fintype.card {c : CCoef n // T c = 0} := by
          rw [← Finset.sum_filter]
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [← Fintype.card_of_subtype
            (p := fun c : CCoef n => T c = 0)
            (s := Finset.univ.filter fun c : CCoef n => T c = 0)]
          · ring
          · intro c
            simp
    _ = (2 : ℤ) ^ (n ^ 3) * (2 : ℤ) ^ (n^3 - n * (n - 1)) := by
          have hker :
              Fintype.card {c : CCoef n // T c = 0} = 2 ^ (n ^ 3 - n * (n - 1)) := by
            rw [← Nat.card_eq_fintype_card]
            simpa [LinearMap.mem_ker] using natCard_ker_T (n := n)
          rw [card_BCoef]
          rw [hker]
          rw [show ((2 ^ (n ^ 3) : ℕ) : ℤ) = (2 : ℤ) ^ (n ^ 3) by
            simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ 3))]
          rw [show ((2 ^ (n ^ 3 - n * (n - 1)) : ℕ) : ℤ) =
              (2 : ℤ) ^ (n ^ 3 - n * (n - 1)) by
            simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ 3 - n * (n - 1)))]
    _ = (2 : ℤ) ^ (n ^ 3 + (n ^ 3 - n * (n - 1))) := by
          rw [← pow_add]

lemma ordinary_pair_sum {n : ℕ} [NeZero n] :
    ∑ b : BCoef n, ∑ b' : BCoef n, ∑ c : CCoef n, ∑ c' : CCoef n,
      bitSign (q b c' + q b' c) =
        (2 : ℤ) ^
          ((n ^ 3 + (n ^ 3 - n * (n - 1))) + (n ^ 3 + (n ^ 3 - n * (n - 1)))) := by
  have hfac :
      ∑ b : BCoef n, ∑ c : CCoef n, bitSign (q b c) =
        (2 : ℤ) ^ (n ^ 3 + (n ^ 3 - n * (n - 1))) :=
    ordinary_pair_factor (n := n)
  calc
    ∑ b : BCoef n, ∑ b' : BCoef n, ∑ c : CCoef n, ∑ c' : CCoef n,
        bitSign (q b c' + q b' c)
      = ∑ b : BCoef n, ∑ b' : BCoef n, ∑ c' : CCoef n, ∑ c : CCoef n,
          bitSign (q b c') * bitSign (q b' c) := by
            simp_rw [bitSign_add]
            refine Finset.sum_congr rfl ?_
            intro b hb
            refine Finset.sum_congr rfl ?_
            intro b' hb'
            rw [Finset.sum_comm]
    _ = ∑ b : BCoef n, ∑ c' : CCoef n, ∑ b' : BCoef n, ∑ c : CCoef n,
          bitSign (q b c') * bitSign (q b' c) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            rw [Finset.sum_comm]
    _ = ∑ b : BCoef n, ∑ c : CCoef n,
          bitSign (q b c) * (∑ b : BCoef n, ∑ c : CCoef n, bitSign (q b c)) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            refine Finset.sum_congr rfl ?_
            intro c hc
            symm
            simp_rw [Finset.mul_sum]
    _ = (∑ b : BCoef n, ∑ c : CCoef n, bitSign (q b c)) *
          (∑ b : BCoef n, ∑ c : CCoef n, bitSign (q b c)) := by
            symm
            simp_rw [Finset.sum_mul]
    _ = ((2 : ℤ) ^ (n ^ 3 + (n ^ 3 - n * (n - 1)))) *
          ((2 : ℤ) ^ (n ^ 3 + (n ^ 3 - n * (n - 1)))) := by
          simpa using congrArg (fun z : ℤ => z * z) hfac
    _ = (2 : ℤ) ^
          ((n ^ 3 + (n ^ 3 - n * (n - 1))) + (n ^ 3 + (n ^ 3 - n * (n - 1)))) := by
          rw [← pow_add]

/-!
Next: prove the two single-summand reindexing lemmas
`pairLeft = qLeft` and `pairRight = qRight`, then recover `q = bPair b (T c)`.
The direct proof is mathematically straightforward but currently hits heartbeat
limits during elaboration, so it needs a more granular decomposition.
-/

end No16
