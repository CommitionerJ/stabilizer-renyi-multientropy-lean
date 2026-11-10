import No16.PhaseReduction

open scoped BigOperators

namespace No16

noncomputable def sigma {n : ℕ} [NeZero n] (x : Profile n) : F :=
  ∑ a : I n, x a

noncomputable def dot {n : ℕ} [NeZero n] (x y : Profile n) : F :=
  ∑ a : I n, x a * y a

def basisProfile {n : ℕ} (a0 : I n) : Profile n :=
  fun a => if a = a0 then 1 else 0

lemma dot_basisProfile {n : ℕ} [NeZero n] (x : Profile n) (a0 : I n) :
    dot x (basisProfile a0) = x a0 := by
  unfold dot basisProfile
  rw [Finset.sum_eq_single a0]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

lemma dot_zero_left {n : ℕ} [NeZero n] (x : Profile n) : dot 0 x = 0 := by
  unfold dot
  simp

lemma dot_zero_right {n : ℕ} [NeZero n] (x : Profile n) : dot x 0 = 0 := by
  unfold dot
  simp

lemma dot_comm {n : ℕ} [NeZero n] (x y : Profile n) : dot x y = dot y x := by
  unfold dot
  congr with a
  ring

lemma dot_nondegenerate {n : ℕ} [NeZero n] {x : Profile n}
    (hx : ∀ y : Profile n, dot x y = 0) : x = 0 := by
  funext a
  have ha := hx (basisProfile a)
  simpa [dot_basisProfile] using ha

abbrev VisibleConstraintFun (n : ℕ) := I n → I n → I n → I n → F

def visibleConstraint {n : ℕ} (bc : BCoef n × CCoef n) : VisibleConstraintFun n :=
  fun v w p q' =>
    bc.1 (v + w) p q' + bc.1 (v + w + 1) p q' + bc.2 v w (p + q') + bc.2 v w (p + q' + 1)

noncomputable def visibleConstraintMap {n : ℕ} :
    (BCoef n × CCoef n) →ₗ[F] VisibleConstraintFun n where
  toFun := visibleConstraint
  map_add' := by
    intro x y
    funext v w p q'
    simp [visibleConstraint, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a x
    rcases x with ⟨b, c⟩
    funext v w p q'
    simp [visibleConstraint, Pi.smul_apply, mul_add, add_mul, add_assoc, add_left_comm]

noncomputable def SSpace {n : ℕ} : Submodule F (BCoef n × CCoef n) :=
  LinearMap.ker (visibleConstraintMap (n := n))

abbrev HFun (n : ℕ) := I n → I n → F

noncomputable def rowSum {n : ℕ} [NeZero n] (h : HFun n) : Profile n :=
  fun t => ∑ s : I n, h t s

noncomputable def colSum {n : ℕ} [NeZero n] (h : HFun n) : Profile n :=
  fun s => ∑ t : I n, h t s

noncomputable def rowSumMap {n : ℕ} [NeZero n] : HFun n →ₗ[F] Profile n where
  toFun := rowSum
  map_add' := by
    intro h k
    funext t
    simp [rowSum, Finset.sum_add_distrib]
  map_smul' := by
    intro a h
    funext t
    simp [rowSum, Pi.smul_apply, Finset.mul_sum]

noncomputable def colSumMap {n : ℕ} [NeZero n] : HFun n →ₗ[F] Profile n where
  toFun := colSum
  map_add' := by
    intro h k
    funext s
    simp [colSum, Finset.sum_add_distrib]
  map_smul' := by
    intro a h
    funext s
    simp [colSum, Pi.smul_apply, Finset.mul_sum]

noncomputable def HSpace {n : ℕ} [NeZero n] : Submodule F (HFun n) :=
  LinearMap.ker (rowSumMap (n := n)) ⊓ LinearMap.ker (colSumMap (n := n))

noncomputable def prefixT {n : ℕ} [NeZero n] (h : HFun n) (t s : I n) : F :=
  Finset.sum (Finset.range t.val) fun i => h (i : I n) s

noncomputable def prefixR {n : ℕ} [NeZero n] (h : HFun n) (t r : I n) : F :=
  Finset.sum (Finset.range r.val) fun j => h t (j : I n)

lemma prefixT_zero {n : ℕ} [NeZero n] (h : HFun n) (s : I n) :
    prefixT h 0 s = 0 := by
  simp [prefixT, ZMod.val_zero]

lemma prefixR_zero {n : ℕ} [NeZero n] (h : HFun n) (t : I n) :
    prefixR h t 0 = 0 := by
  simp [prefixR, ZMod.val_zero]

lemma prefixT_natCast_succ {n k : ℕ} [NeZero n] (h : HFun n) (s : I n)
    (hk : k + 1 < n) :
    prefixT h ((k + 1 : ℕ) : I n) s = prefixT h (k : I n) s + h (k : I n) s := by
  have hk' : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
  rw [prefixT, prefixT, ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hk', Finset.sum_range_succ]

lemma prefixR_natCast_succ {n k : ℕ} [NeZero n] (h : HFun n) (t : I n)
    (hk : k + 1 < n) :
    prefixR h t ((k + 1 : ℕ) : I n) = prefixR h t (k : I n) + h t (k : I n) := by
  have hk' : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
  rw [prefixR, prefixR, ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hk', Finset.sum_range_succ]

abbrev UVFun (n : ℕ) := I n → I n → F

noncomputable def constProfile {n : ℕ} (a : F) : Profile n :=
  fun _ => a

noncomputable def uvAgg {n : ℕ} [NeZero n] (u : UVFun n) : Profile n :=
  fun s => ∑ p : I n, u p (s - p)

noncomputable def uvAggMap {n : ℕ} [NeZero n] : UVFun n →ₗ[F] Profile n where
  toFun := uvAgg
  map_add' := by
    intro u v
    funext s
    simp [uvAgg, Finset.sum_add_distrib]
  map_smul' := by
    intro a u
    funext s
    simp [uvAgg, Pi.smul_apply, Finset.mul_sum]

noncomputable def uvLiftProfile {n : ℕ} [NeZero n] (μ : Profile n) : UVFun n :=
  fun p q => if p = 0 then μ q else 0

lemma uvAgg_uvLiftProfile {n : ℕ} [NeZero n] (μ : Profile n) :
    uvAgg (uvLiftProfile μ) = μ := by
  funext s
  unfold uvAgg uvLiftProfile
  rw [Finset.sum_eq_single 0]
  · simp
  · intro p hp hp0
    simp [hp0]
  · simp

lemma uvAgg_surjective {n : ℕ} [NeZero n] : Function.Surjective (uvAgg (n := n)) := by
  intro μ
  exact ⟨uvLiftProfile μ, uvAgg_uvLiftProfile (μ := μ)⟩

lemma finrank_profile_vis {n : ℕ} [NeZero n] : Module.finrank F (Profile n) = n := by
  change Module.finrank F (I n → F) = n
  simp [I, ZMod.card]

lemma finrank_uvFun {n : ℕ} [NeZero n] : Module.finrank F (UVFun n) = n ^ 2 := by
  change Module.finrank F (I n → I n → F) = n ^ 2
  rw [Module.finrank_pi_fintype (R := F) (M := fun _ : I n => I n → F)]
  calc
    ∑ _ : I n, Module.finrank F (I n → F) = n * n := by
      simp [Module.finrank_pi, I, ZMod.card]
    _ = n ^ 2 := by ring

lemma finrank_ker_uvAgg {n : ℕ} [NeZero n] :
    Module.finrank F (LinearMap.ker (uvAggMap (n := n))) = n ^ 2 - n := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (uvAggMap (n := n))
  have htop : LinearMap.range (uvAggMap (n := n)) = ⊤ := by
    ext μ
    constructor
    · intro hμ
      simp
    · intro hμ
      rcases uvAgg_surjective (n := n) μ with ⟨u, rfl⟩
      exact ⟨u, rfl⟩
  rw [htop] at hdim
  have htopfin : Module.finrank F (⊤ : Submodule F (Profile n)) = n := by
    simpa using finrank_profile_vis (n := n)
  rw [htopfin, finrank_uvFun] at hdim
  omega

noncomputable def uvConstWitness {n : ℕ} [NeZero n] (a : F) : UVFun n :=
  uvLiftProfile (constProfile a)

lemma uvAgg_uvConstWitness {n : ℕ} [NeZero n] (a : F) :
    uvAgg (uvConstWitness (n := n) a) = constProfile a := by
  exact uvAgg_uvLiftProfile (μ := constProfile a)

lemma uvAgg_add {n : ℕ} [NeZero n] (u v : UVFun n) :
    uvAgg (u + v) = uvAgg u + uvAgg v := by
  ext s
  simp [uvAgg, Finset.sum_add_distrib]

lemma uvConstWitness_add_self {n : ℕ} [NeZero n] (a : F) :
    uvConstWitness (n := n) a + uvConstWitness (n := n) a = 0 := by
  ext p q
  by_cases hp : p = 0
  · simp [uvConstWitness, uvLiftProfile, constProfile, hp, F_add_self]
  · simp [uvConstWitness, uvLiftProfile, constProfile, hp]

abbrev ConstAggUV (n : ℕ) [NeZero n] :=
  { u : UVFun n // ∃ a : F, uvAgg u = constProfile a }

noncomputable def constAggUVToData {n : ℕ} [NeZero n] :
    ConstAggUV n → F × LinearMap.ker (uvAggMap (n := n))
  | ⟨u, hu⟩ =>
      let a : F := uvAgg u 0
      let ku : LinearMap.ker (uvAggMap (n := n)) := ⟨u + uvConstWitness (n := n) a, by
        rcases hu with ⟨a0, ha0⟩
        have ha : a = a0 := by
          simpa [a, ha0, constProfile] using congrFun ha0 (0 : I n)
        show uvAgg (u + uvConstWitness (n := n) a) = 0
        rw [uvAgg_add, ha0, uvAgg_uvConstWitness, ha]
        ext s
        simp [constProfile, F_add_self]⟩
      (a, ku)

noncomputable def dataToConstAggUV {n : ℕ} [NeZero n] :
    F × LinearMap.ker (uvAggMap (n := n)) → ConstAggUV n
  | (a, ku) =>
      ⟨uvConstWitness (n := n) a + ku.1, ⟨a, by
        have hku : uvAgg ku.1 = 0 := ku.2
        calc
          uvAgg (uvConstWitness (n := n) a + ku.1)
              = uvAgg (uvConstWitness (n := n) a) + uvAgg ku.1 := uvAgg_add _ _
          _ = constProfile a + 0 := by rw [uvAgg_uvConstWitness, hku]
          _ = constProfile a := by simp⟩⟩

lemma dataToConstAggUV_constAggUVToData {n : ℕ} [NeZero n] (u : ConstAggUV n) :
    dataToConstAggUV (n := n) (constAggUVToData (n := n) u) = u := by
  rcases u with ⟨u, hu⟩
  apply Subtype.ext
  ext p q
  by_cases hp : p = 0
  · simp [constAggUVToData, dataToConstAggUV, uvConstWitness, uvLiftProfile, constProfile,
      hp, add_assoc, add_left_comm, add_comm, F_add_self]
  · simp [constAggUVToData, dataToConstAggUV, uvConstWitness, uvLiftProfile, constProfile,
      hp, add_assoc, add_left_comm, add_comm]

lemma constAggUVToData_dataToConstAggUV {n : ℕ} [NeZero n]
    (x : F × LinearMap.ker (uvAggMap (n := n))) :
    constAggUVToData (n := n) (dataToConstAggUV (n := n) x) = x := by
  rcases x with ⟨a, ku⟩
  have hku : uvAgg ku.1 = 0 := ku.2
  have hku0 : uvAgg ku.1 0 = 0 := by
    simpa using congrFun hku (0 : I n)
  have hfst : uvAgg (uvConstWitness (n := n) a + ku.1) 0 = a := by
    calc
      uvAgg (uvConstWitness (n := n) a + ku.1) 0
          = (uvAgg (uvConstWitness (n := n) a) + uvAgg ku.1) 0 := by
              rw [uvAgg_add]
      _ = a := by
            simp [uvAgg_uvConstWitness, constProfile, hku0]
  have hswap : uvAgg (ku.1 + uvConstWitness (n := n) a) 0 = a := by
    calc
      uvAgg (ku.1 + uvConstWitness (n := n) a) 0
          = (uvAgg ku.1 + uvAgg (uvConstWitness (n := n) a)) 0 := by
              rw [uvAgg_add]
      _ = a := by
            simp [uvAgg_uvConstWitness, constProfile, hku0]
  apply Prod.ext
  · simpa [constAggUVToData, dataToConstAggUV] using hfst
  · apply Subtype.ext
    ext p q
    by_cases hp : p = 0
    · have hswap' : uvAgg (ku.1 + uvLiftProfile (constProfile a)) 0 = a := by
        simpa [uvConstWitness] using hswap
      simp [constAggUVToData, dataToConstAggUV, hswap', uvConstWitness, uvLiftProfile,
        constProfile, hp, add_assoc, add_left_comm, add_comm, F_add_self]
    · simp [constAggUVToData, dataToConstAggUV, hfst, hswap, uvConstWitness, uvLiftProfile,
        constProfile, hp, add_assoc, add_left_comm, add_comm]

noncomputable def constAggUVEquiv {n : ℕ} [NeZero n] :
    ConstAggUV n ≃ F × LinearMap.ker (uvAggMap (n := n)) where
  toFun := constAggUVToData (n := n)
  invFun := dataToConstAggUV (n := n)
  left_inv := dataToConstAggUV_constAggUVToData (n := n)
  right_inv := constAggUVToData_dataToConstAggUV (n := n)

lemma natCard_constAggUV {n : ℕ} [NeZero n] :
    Nat.card (ConstAggUV n) = 2 ^ (n ^ 2 - n + 1) := by
  rw [Nat.card_congr (constAggUVEquiv (n := n))]
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F)]
  have hF : Fintype.card F = 2 := by simp [F, ZMod.card]
  rw [hF]
  simp [finrank_ker_uvAgg]
  have hk : n ^ 2 - n + 1 = (n ^ 2 - n) + 1 := by omega
  rw [hk, pow_add, pow_one, Nat.mul_comm]

lemma natCard_constAggUV_prod {n : ℕ} [NeZero n] :
    Nat.card (ConstAggUV n × ConstAggUV n) = 2 ^ ((n ^ 2 - n + 1) + (n ^ 2 - n + 1)) := by
  rw [Nat.card_prod, natCard_constAggUV]
  exact (pow_add 2 (n ^ 2 - n + 1) (n ^ 2 - n + 1)).symm

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
    sigma (basisProfile (0 : I n)) = 1 := by
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
    refine ⟨a • basisProfile (0 : I n), ?_⟩
    simp [profileSigmaMap, sigma_basisProfile_zero]

lemma finrank_profileZeroSum {n : ℕ} [NeZero n] :
    Module.finrank F (ProfileZeroSum n) = n - 1 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (profileSigmaMap (n := n))
  rw [range_sigmaMap_top (n := n)] at hdim
  have htopfin : Module.finrank F (⊤ : Submodule F F) = 1 := by
    simp
  rw [htopfin, finrank_profile_vis] at hdim
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
  have hdim' := congrArg (fun m => m - 1) hdim
  simpa using hdim'

lemma natCard_profileZeroSum {n : ℕ} [NeZero n] :
    Nat.card (ProfileZeroSum n) = 2 ^ (n - 1) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F, finrank_profileZeroSum]

abbrev RowColBalancedBase (n : ℕ) [NeZero n] :=
  { rc : Profile n × Profile n // sigma rc.1 = sigma rc.2 }

noncomputable instance rowColBalancedBaseFintype {n : ℕ} [NeZero n] :
    Fintype (RowColBalancedBase n) := by
  classical
  infer_instance

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

lemma natCard_rowColBalancedBase {n : ℕ} [NeZero n] :
    Nat.card (RowColBalancedBase n) = 2 ^ (2 * n - 1) := by
  rw [Nat.card_congr (rowColBalancedBaseEquivData (n := n))]
  rw [Nat.card_prod]
  have hProf : Nat.card (Profile n) = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := F), finrank_profile_vis]
    simp [F]
  rw [hProf, natCard_profileZeroSum]
  calc
    2 ^ n * 2 ^ (n - 1) = 2 ^ (n + (n - 1)) := by
      symm
      exact pow_add 2 n (n - 1)
    _ = 2 ^ (2 * n - 1) := by
      congr
      omega

lemma sigma_rowSum_eq_sigma_colSum {n : ℕ} [NeZero n] (h : HFun n) :
    sigma (rowSum h) = sigma (colSum h) := by
  unfold sigma rowSum colSum
  rw [Finset.sum_comm]

lemma rowSum_add {n : ℕ} [NeZero n] (h k : HFun n) :
    rowSum (h + k) = rowSum h + rowSum k := by
  funext t
  simp [rowSum, Finset.sum_add_distrib]

lemma colSum_add {n : ℕ} [NeZero n] (h k : HFun n) :
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

noncomputable def rowColBalancedBaseMap {n : ℕ} [NeZero n] : HFun n → RowColBalancedBase n
  | h => ⟨(rowSum h, colSum h), sigma_rowSum_eq_sigma_colSum (h := h)⟩

noncomputable def rowColBalancedBaseLift {n : ℕ} [NeZero n] (rc : RowColBalancedBase n) : HFun n :=
  fun t s =>
    (if s = 0 then rowSeed rc.1.1 t else 0) + (if t = 0 then rc.1.2 s else 0)

lemma rowSum_rowColBalancedBaseLift {n : ℕ} [NeZero n] (rc : RowColBalancedBase n) :
    rowSum (rowColBalancedBaseLift (n := n) rc) = rc.1.1 := by
  rcases rc with ⟨⟨r, c⟩, hrc⟩
  have hrc' : sigma r = sigma c := hrc
  funext t
  by_cases ht : t = 0
  · subst ht
    unfold rowSum rowColBalancedBaseLift
    rw [Finset.sum_add_distrib, Finset.sum_eq_single 0]
    · have hseed : (if (0 : I n) = 0 then rowSeed r 0 else 0) = r 0 + sigma r := by
        simp [rowSeed]
      have hsigma : (∑ x : I n, if (0 : I n) = 0 then c x else 0) = sigma c := by
        simp [sigma]
      rw [hseed, hsigma, hrc']
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
    · intro t _
      simp [hs]

lemma rowColBalancedBaseMap_rowColBalancedBaseLift {n : ℕ} [NeZero n] (rc : RowColBalancedBase n) :
    rowColBalancedBaseMap (n := n) (rowColBalancedBaseLift (n := n) rc) = rc := by
  rcases rc with ⟨⟨r, c⟩, hrc⟩
  apply Subtype.ext
  apply Prod.ext
  · exact rowSum_rowColBalancedBaseLift (n := n) ⟨(r, c), hrc⟩
  · exact colSum_rowColBalancedBaseLift (n := n) ⟨(r, c), hrc⟩

noncomputable def hResidualBase {n : ℕ} [NeZero n] (h : HFun n) : HFun n :=
  h + rowColBalancedBaseLift (n := n) (rowColBalancedBaseMap (n := n) h)

lemma hResidualBase_mem_HSpace {n : ℕ} [NeZero n] (h : HFun n) :
    hResidualBase (n := n) h ∈ HSpace (n := n) := by
  change hResidualBase (n := n) h ∈ LinearMap.ker (rowSumMap (n := n)) ∧
      hResidualBase (n := n) h ∈ LinearMap.ker (colSumMap (n := n))
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

noncomputable def hFunToRowColHSpaceBase {n : ℕ} [NeZero n] :
    HFun n → RowColBalancedBase n × HSpace (n := n)
  | h => (rowColBalancedBaseMap (n := n) h, ⟨hResidualBase (n := n) h, hResidualBase_mem_HSpace (n := n) h⟩)

noncomputable def rowColHSpaceBaseToHFun {n : ℕ} [NeZero n] :
    RowColBalancedBase n × HSpace (n := n) → HFun n
  | (rc, kh) => rowColBalancedBaseLift (n := n) rc + kh.1

lemma rowColHSpaceBaseToHFun_hFunToRowColHSpaceBase {n : ℕ} [NeZero n] (h : HFun n) :
    rowColHSpaceBaseToHFun (n := n) (hFunToRowColHSpaceBase (n := n) h) = h := by
  funext t s
  simp [rowColHSpaceBaseToHFun, hFunToRowColHSpaceBase, hResidualBase,
    add_assoc, add_left_comm, add_comm, F_add_self]

lemma rowColBalancedBaseMap_add_hspace {n : ℕ} [NeZero n] (rc : RowColBalancedBase n)
    {k : HFun n} (hk : k ∈ HSpace (n := n)) :
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

lemma hFunToRowColHSpaceBase_rowColHSpaceBaseToHFun {n : ℕ} [NeZero n]
    (x : RowColBalancedBase n × HSpace (n := n)) :
    hFunToRowColHSpaceBase (n := n) (rowColHSpaceBaseToHFun (n := n) x) = x := by
  rcases x with ⟨rc, kh⟩
  rcases kh with ⟨k, hk⟩
  have hmap :
      rowColBalancedBaseMap (n := n) (rowColHSpaceBaseToHFun (n := n) (rc, ⟨k, hk⟩)) = rc := by
    exact rowColBalancedBaseMap_add_hspace (n := n) rc hk
  have hmap' :
      rowColBalancedBaseMap (n := n) (k + rowColBalancedBaseLift (n := n) rc) = rc := by
    simpa [add_comm] using rowColBalancedBaseMap_add_hspace (n := n) rc hk
  apply Prod.ext
  · exact hmap
  · apply Subtype.ext
    funext t s
    simp [hFunToRowColHSpaceBase, rowColHSpaceBaseToHFun, hResidualBase, hmap',
      add_assoc, add_left_comm, add_comm, F_add_self]

noncomputable def hFunEquivRowColHSpaceBase {n : ℕ} [NeZero n] :
    HFun n ≃ (RowColBalancedBase n × HSpace (n := n)) where
  toFun := hFunToRowColHSpaceBase (n := n)
  invFun := rowColHSpaceBaseToHFun (n := n)
  left_inv := rowColHSpaceBaseToHFun_hFunToRowColHSpaceBase (n := n)
  right_inv := hFunToRowColHSpaceBase_rowColHSpaceBaseToHFun (n := n)

lemma natCard_HFun_base {n : ℕ} [NeZero n] :
    Nat.card (HFun n) = 2 ^ (n ^ 2) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F, finrank_uvFun]

lemma finrank_HSpace {n : ℕ} [NeZero n] :
    Module.finrank F (HSpace (n := n)) = (n - 1) ^ 2 := by
  have hcard :
      Nat.card (HFun n) = Nat.card (RowColBalancedBase n) * Nat.card (HSpace (n := n)) := by
    calc
      Nat.card (HFun n) = Nat.card (RowColBalancedBase n × HSpace (n := n)) := by
        rw [Nat.card_congr (hFunEquivRowColHSpaceBase (n := n))]
      _ = Nat.card (RowColBalancedBase n) * Nat.card (HSpace (n := n)) := by
        rw [Nat.card_prod]
  rw [natCard_HFun_base, natCard_rowColBalancedBase, Module.natCard_eq_pow_finrank (K := F)] at hcard
  simp [F] at hcard
  rw [← pow_add] at hcard
  have hexp : n ^ 2 = (2 * n - 1) + Module.finrank F (HSpace (n := n)) := by
    exact Nat.pow_right_injective (by omega : 1 < 2) hcard
  have hdim : Module.finrank F (HSpace (n := n)) = n ^ 2 - (2 * n - 1) := by
    omega
  have hsq : n ^ 2 - (2 * n - 1) = (n - 1) ^ 2 := by
    rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
    simp [pow_two]
    have hc : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
      ring_nf
    have h2 : 2 * (k + 1) = 2 * k + 2 := by
      omega
    rw [hc, h2]
    omega
  rw [hdim, hsq]

lemma natCard_HSpace {n : ℕ} [NeZero n] :
    Nat.card (HSpace (n := n)) = 2 ^ ((n - 1) ^ 2) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F, finrank_HSpace]

noncomputable def buildB {n : ℕ} [NeZero n] (h : HFun n) (u : UVFun n) : BCoef n :=
  fun t p q' => u p q' + prefixT h t (p + q')

noncomputable def buildC {n : ℕ} [NeZero n] (h : HFun n) (v : UVFun n) : CCoef n :=
  fun x y r => v x y + prefixR h (x + y) r

noncomputable def visibleCore {n : ℕ} [NeZero n] (h : HFun n) (t s : I n) : F :=
  prefixT h t s + prefixT h (t + 1) s + prefixR h t s + prefixR h t (s + 1)

lemma buildB_zero {n : ℕ} [NeZero n] (h : HFun n) (u : UVFun n) (p q' : I n) :
    buildB h u 0 p q' = u p q' := by
  simp [buildB, prefixT_zero]

lemma buildC_zero {n : ℕ} [NeZero n] (h : HFun n) (v : UVFun n) (x y : I n) :
    buildC h v x y 0 = v x y := by
  simp [buildC, prefixR_zero]

lemma buildB_natCast_succ {n k : ℕ} [NeZero n] (h : HFun n) (u : UVFun n)
    (p q' : I n) (hk : k + 1 < n) :
    buildB h u ((k + 1 : ℕ) : I n) p q' = buildB h u (k : I n) p q' + h (k : I n) (p + q') := by
  rw [buildB, buildB, prefixT_natCast_succ (h := h) (s := p + q') hk]
  simp [add_assoc, add_left_comm, add_comm]

lemma buildC_natCast_succ {n k : ℕ} [NeZero n] (h : HFun n) (v : UVFun n)
    (x y : I n) (hk : k + 1 < n) :
    buildC h v x y ((k + 1 : ℕ) : I n) = buildC h v x y (k : I n) + h (x + y) (k : I n) := by
  rw [buildC, buildC, prefixR_natCast_succ (h := h) (t := x + y) hk]
  simp [add_assoc, add_left_comm, add_comm]

noncomputable def visibleHData {n : ℕ} [NeZero n] (bc : BCoef n × CCoef n) : HFun n :=
  fun t s => bc.1 (t + 1) 0 s + bc.1 t 0 s

noncomputable def visibleUData {n : ℕ} [NeZero n] (bc : BCoef n × CCoef n) : UVFun n :=
  fun p q' => bc.1 0 p q'

noncomputable def visibleVData {n : ℕ} [NeZero n] (bc : BCoef n × CCoef n) : UVFun n :=
  fun x y => bc.2 x y 0

lemma visibleH_eq_c_increment {n : ℕ} [NeZero n] {bc : BCoef n × CCoef n}
    (hbc : bc ∈ SSpace (n := n)) (x y r : I n) :
    visibleHData bc (x + y) r = bc.2 x y (r + 1) + bc.2 x y r := by
  have hker : visibleConstraint bc = 0 := hbc
  have hs := congrFun (congrFun (congrFun (congrFun hker x) y) 0) r
  have hs0 :
      bc.1 (x + y) 0 r + bc.1 (x + y + 1) 0 r + (bc.2 x y r + bc.2 x y (r + 1)) = 0 := by
    simpa [visibleConstraint, add_assoc, add_left_comm, add_comm] using hs
  have hs' :
      bc.1 (x + y) 0 r + bc.1 (x + y + 1) 0 r = -(bc.2 x y r + bc.2 x y (r + 1)) := by
    exact eq_neg_of_add_eq_zero_left hs0
  simpa [visibleHData, add_assoc, add_left_comm, add_comm] using hs'

lemma visibleH_eq_b_increment {n : ℕ} [NeZero n] {bc : BCoef n × CCoef n}
    (hbc : bc ∈ SSpace (n := n)) (t p q' : I n) :
    visibleHData bc t (p + q') = bc.1 t p q' + bc.1 (t + 1) p q' := by
  have hker : visibleConstraint bc = 0 := hbc
  have hs := congrFun (congrFun (congrFun (congrFun hker t) 0) p) q'
  have hs0 :
      bc.1 t p q' + bc.1 (t + 1) p q' + (bc.2 t 0 (p + q') + bc.2 t 0 (p + q' + 1)) = 0 := by
    simpa [visibleConstraint, add_assoc, add_left_comm, add_comm] using hs
  have hc0 : bc.2 t 0 (p + q') + bc.2 t 0 (p + q' + 1) = visibleHData bc t (p + q') := by
    simpa [add_comm] using (visibleH_eq_c_increment (n := n) hbc t 0 (p + q')).symm
  have hc : -(bc.2 t 0 (p + q') + bc.2 t 0 (p + q' + 1)) = visibleHData bc t (p + q') := by
    simpa [hc0]
  have hs' : bc.1 t p q' + bc.1 (t + 1) p q' = -(bc.2 t 0 (p + q') + bc.2 t 0 (p + q' + 1)) := by
    exact eq_neg_of_add_eq_zero_left hs0
  calc
    visibleHData bc t (p + q') = -(bc.2 t 0 (p + q') + bc.2 t 0 (p + q' + 1)) := by
      simpa using hc.symm
    _ = bc.1 t p q' + bc.1 (t + 1) p q' := by
      simpa [add_comm] using hs'.symm

lemma buildB_visibleData_eq {n : ℕ} [NeZero n] {bc : BCoef n × CCoef n}
    (hbc : bc ∈ SSpace (n := n)) :
    buildB (visibleHData bc) (visibleUData bc) = bc.1 := by
  funext t p q'
  have hrec :
      ∀ k, k < n →
        buildB (visibleHData bc) (visibleUData bc) (k : I n) p q' = bc.1 (k : I n) p q' := by
    intro k hk
    induction' k with k ih
    · simpa [visibleUData] using buildB_zero (h := visibleHData bc) (u := visibleUData bc) p q'
    · rw [buildB_natCast_succ (h := visibleHData bc) (u := visibleUData bc)
        (p := p) (q' := q') hk]
      rw [ih (Nat.lt_of_succ_lt hk)]
      have hinc := visibleH_eq_b_increment (n := n) hbc (k : I n) p q'
      rw [show visibleHData bc (k : I n) (p + q') =
          bc.1 (k : I n) p q' + bc.1 ((k + 1 : ℕ) : I n) p q' by
            simpa [visibleHData] using hinc]
      calc
        bc.1 (k : I n) p q' + (bc.1 (k : I n) p q' + bc.1 ((k + 1 : ℕ) : I n) p q')
            = (bc.1 (k : I n) p q' + bc.1 (k : I n) p q') + bc.1 ((k + 1 : ℕ) : I n) p q' := by
                ac_rfl
        _ = bc.1 ((k + 1 : ℕ) : I n) p q' := by
              simp [F_add_self]
  have htlt : t.val < n := by
    simpa using ZMod.val_lt t
  simpa using hrec t.val htlt

lemma buildC_visibleData_eq {n : ℕ} [NeZero n] {bc : BCoef n × CCoef n}
    (hbc : bc ∈ SSpace (n := n)) :
    buildC (visibleHData bc) (visibleVData bc) = bc.2 := by
  funext x y r
  have hrec :
      ∀ k, k < n →
        buildC (visibleHData bc) (visibleVData bc) x y (k : I n) = bc.2 x y (k : I n) := by
    intro k hk
    induction' k with k ih
    · simpa [visibleVData] using buildC_zero (h := visibleHData bc) (v := visibleVData bc) x y
    · rw [buildC_natCast_succ (h := visibleHData bc) (v := visibleVData bc)
        (x := x) (y := y) hk]
      rw [ih (Nat.lt_of_succ_lt hk)]
      have hinc := visibleH_eq_c_increment (n := n) hbc x y (k : I n)
      rw [show visibleHData bc (x + y) (k : I n) =
          bc.2 x y ((k + 1 : ℕ) : I n) + bc.2 x y (k : I n) by
            simpa [visibleHData] using hinc]
      calc
        bc.2 x y (k : I n) + (bc.2 x y ((k + 1 : ℕ) : I n) + bc.2 x y (k : I n))
            = (bc.2 x y (k : I n) + bc.2 x y (k : I n)) + bc.2 x y ((k + 1 : ℕ) : I n) := by
                ac_rfl
        _ = bc.2 x y ((k + 1 : ℕ) : I n) := by
              simp [F_add_self]
  have hrlt : r.val < n := by
    simpa using ZMod.val_lt r
  simpa using hrec r.val hrlt

lemma visibleHData_mem_HSpace {n : ℕ} [NeZero n] {bc : BCoef n × CCoef n}
    (hbc : bc ∈ SSpace (n := n)) :
    visibleHData bc ∈ HSpace (n := n) := by
  constructor
  · change rowSum (visibleHData bc) = 0
    funext t
    have hshift :
        (∑ s : I n, bc.2 t 0 (s + 1)) = ∑ s : I n, bc.2 t 0 s := by
      exact
        Fintype.sum_equiv (Equiv.addRight (1 : I n))
          (fun s : I n => bc.2 t 0 (s + 1))
          (fun s : I n => bc.2 t 0 s)
          (by
            intro s
            simp)
    calc
      rowSum (visibleHData bc) t
          = ∑ s : I n, (bc.2 t 0 (s + 1) + bc.2 t 0 s) := by
              refine Finset.sum_congr rfl ?_
              intro s hs
              simpa [add_comm, add_left_comm, add_assoc] using
                (visibleH_eq_c_increment (n := n) hbc t 0 s)
      _ = (∑ s : I n, bc.2 t 0 (s + 1)) + ∑ s : I n, bc.2 t 0 s := by
            rw [Finset.sum_add_distrib]
      _ = 0 := by
            rw [hshift]
            exact F_add_self _
  · change colSum (visibleHData bc) = 0
    funext s
    have hshift :
        (∑ t : I n, bc.1 (t + 1) 0 s) = ∑ t : I n, bc.1 t 0 s := by
      exact
        Fintype.sum_equiv (Equiv.addRight (1 : I n))
          (fun t : I n => bc.1 (t + 1) 0 s)
          (fun t : I n => bc.1 t 0 s)
          (by
            intro t
            simp)
    calc
      colSum (visibleHData bc) s
          = ∑ t : I n, (bc.1 t 0 s + bc.1 (t + 1) 0 s) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              simpa [add_comm, add_left_comm, add_assoc] using
                (visibleH_eq_b_increment (n := n) hbc t 0 s)
      _ = (∑ t : I n, bc.1 t 0 s) + ∑ t : I n, bc.1 (t + 1) 0 s := by
            rw [Finset.sum_add_distrib]
      _ = 0 := by
            rw [hshift]
            exact F_add_self _

lemma visibleConstraint_build_eq_visibleCore {n : ℕ} [NeZero n] (h : HFun n)
    (u v : UVFun n) (x y p q' : I n) :
    visibleConstraint (buildB h u, buildC h v) x y p q' =
      visibleCore h (x + y) (p + q') := by
  unfold visibleConstraint buildB buildC visibleCore
  ring_nf
  have h2 : (2 : F) = 0 := by decide
  simp [h2, add_assoc, add_left_comm, add_comm]

lemma visibleCore_natCast_eq_zero {n k l : ℕ} [NeZero n] (h : HFun n)
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

lemma prefixT_last_eq_of_colSum_eq_zero {n : ℕ} [NeZero n] (h : HFun n) (s : I n)
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

lemma prefixR_last_eq_of_rowSum_eq_zero {n : ℕ} [NeZero n] (h : HFun n) (t : I n)
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


def pointH {n : ℕ} (t0 s0 : I n) : HFun n :=
  fun t s => if t = t0 ∧ s = s0 then 1 else 0

def rect {n : ℕ} (a b : I n) : HFun n :=
  pointH 0 0 + pointH a 0 + pointH 0 b + pointH a b

lemma rect_apply_nonzero_nonzero {n : ℕ} [NeZero n] {a b t s : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) (hs : s ≠ 0) :
    rect a b t s = if t = a ∧ s = b then 1 else 0 := by
  unfold rect pointH
  by_cases hta : t = a
  · by_cases hsb : s = b
    · simp [ha, hb, ht, hs, hta, hsb]
    · simp [ha, hb, ht, hs, hta, hsb]
  · by_cases hsb : s = b
    · simp [ha, hb, ht, hs, hta, hsb]
    · simp [ha, hb, ht, hs, hta, hsb]

lemma rowSum_pointH {n : ℕ} [NeZero n] (t0 s0 : I n) :
    rowSum (pointH t0 s0) = basisProfile t0 := by
  funext t
  unfold rowSum pointH basisProfile
  by_cases ht : t = t0
  · subst ht
    rw [Finset.sum_eq_single s0]
    · simp
    · intro s _ hs
      simp [hs]
    · simp
  · have hzero : ∀ s : I n, (if t = t0 ∧ s = s0 then 1 else 0) = 0 := by
      intro s
      simp [ht]
    simp [hzero, ht]

lemma colSum_pointH {n : ℕ} [NeZero n] (t0 s0 : I n) :
    colSum (pointH t0 s0) = basisProfile s0 := by
  funext s
  unfold colSum pointH basisProfile
  by_cases hs : s = s0
  · subst hs
    rw [Finset.sum_eq_single t0]
    · simp
    · intro t _ ht
      simp [ht]
    · simp
  · have hzero : ∀ t : I n, (if t = t0 ∧ s = s0 then 1 else 0) = 0 := by
      intro t
      simp [hs]
    simp [hzero, hs]

lemma rect_mem_HSpace {n : ℕ} [NeZero n] (a b : I n) : rect a b ∈ (HSpace (n := n)) := by
  refine ⟨?_, ?_⟩
  · change rowSumMap (n := n) (rect a b) = 0
    unfold rect
    rw [map_add, map_add, map_add]
    rw [show rowSumMap (n := n) (pointH a b) = basisProfile a by simpa [rowSumMap] using rowSum_pointH a b]
    rw [show rowSumMap (n := n) (pointH a 0) = basisProfile a by simpa [rowSumMap] using rowSum_pointH a 0]
    rw [show rowSumMap (n := n) (pointH 0 b) = basisProfile 0 by simpa [rowSumMap] using rowSum_pointH 0 b]
    rw [show rowSumMap (n := n) (pointH 0 0) = basisProfile 0 by simpa [rowSumMap] using rowSum_pointH 0 0]
    funext t
    simp [basisProfile, F_add_self, add_assoc, add_left_comm, add_comm]
  · change colSumMap (n := n) (rect a b) = 0
    unfold rect
    rw [map_add, map_add, map_add]
    rw [show colSumMap (n := n) (pointH a b) = basisProfile b by simpa [colSumMap] using colSum_pointH a b]
    rw [show colSumMap (n := n) (pointH a 0) = basisProfile 0 by simpa [colSumMap] using colSum_pointH a 0]
    rw [show colSumMap (n := n) (pointH 0 b) = basisProfile b by simpa [colSumMap] using colSum_pointH 0 b]
    rw [show colSumMap (n := n) (pointH 0 0) = basisProfile 0 by simpa [colSumMap] using colSum_pointH 0 0]
    funext s
    simp [basisProfile, F_add_self, add_assoc, add_left_comm, add_comm]

lemma rowSum_eq_zero_of_mem_HSpace {n : ℕ} [NeZero n] {h : HFun n}
    (hh : h ∈ HSpace (n := n)) (t : I n) :
    rowSum h t = 0 := by
  have hker : rowSumMap (n := n) h = 0 := hh.1
  simpa [rowSumMap] using congrFun hker t

lemma colSum_eq_zero_of_mem_HSpace {n : ℕ} [NeZero n] {h : HFun n}
    (hh : h ∈ HSpace (n := n)) (s : I n) :
    colSum h s = 0 := by
  have hker : colSumMap (n := n) h = 0 := hh.2
  simpa [colSumMap] using congrFun hker s

lemma totalSum_eq_zero_of_mem_HSpace {n : ℕ} [NeZero n] {h : HFun n}
    (hh : h ∈ HSpace (n := n)) :
    (∑ a : I n, ∑ b : I n, h a b) = 0 := by
  calc
    ∑ a : I n, ∑ b : I n, h a b = ∑ a : I n, rowSum h a := by
      simp [rowSum]
    _ = ∑ a : I n, 0 := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      exact rowSum_eq_zero_of_mem_HSpace hh a
    _ = 0 := by simp

lemma visibleCore_eq_zero_of_mem_HSpace {n : ℕ} [NeZero n] {h : HFun n}
    (hh : h ∈ HSpace (n := n)) (t s : I n) :
    visibleCore h t s = 0 := by
  rcases val_add_one_lt_or_eq_pred (n := n) t with ht | rfl
  · rcases val_add_one_lt_or_eq_pred (n := n) s with hs | rfl
    · rw [← ZMod.natCast_zmod_val t, ← ZMod.natCast_zmod_val s]
      simpa using visibleCore_natCast_eq_zero (h := h) (k := t.val) (l := s.val) ht hs
    · rw [visibleCore, natCast_pred_add_one_eq_zero, prefixR_zero]
      rw [← ZMod.natCast_zmod_val t, natCast_val_add_one t ht]
      rw [prefixT_natCast_succ (h := h) (s := ((n - 1 : ℕ) : I n)) ht]
      have hrow := rowSum_eq_zero_of_mem_HSpace (n := n) hh t
      have hlast := prefixR_last_eq_of_rowSum_eq_zero (h := h) t hrow
      simp [hlast, add_assoc, add_left_comm, add_comm, F_add_self]
  · rcases val_add_one_lt_or_eq_pred (n := n) s with hs | rfl
    · rw [visibleCore, natCast_pred_add_one_eq_zero, prefixT_zero]
      rw [← ZMod.natCast_zmod_val s, natCast_val_add_one s hs]
      rw [prefixR_natCast_succ (h := h) (t := ((n - 1 : ℕ) : I n)) hs]
      have hcol := colSum_eq_zero_of_mem_HSpace (n := n) hh s
      have hlast := prefixT_last_eq_of_colSum_eq_zero (h := h) s hcol
      simp [hlast, add_assoc, add_left_comm, add_comm, F_add_self]
    · rw [visibleCore, natCast_pred_add_one_eq_zero, prefixT_zero, prefixR_zero]
      have hcol := colSum_eq_zero_of_mem_HSpace (n := n) hh ((n - 1 : ℕ) : I n)
      have hrow := rowSum_eq_zero_of_mem_HSpace (n := n) hh ((n - 1 : ℕ) : I n)
      have hlastT := prefixT_last_eq_of_colSum_eq_zero (h := h) ((n - 1 : ℕ) : I n) hcol
      have hlastR := prefixR_last_eq_of_rowSum_eq_zero (h := h) ((n - 1 : ℕ) : I n) hrow
      simp [hlastT, hlastR, add_assoc, add_left_comm, add_comm, F_add_self]

lemma prefixT_pair_eq_of_mem_HSpace {n : ℕ} [NeZero n] {h : HFun n}
    (hh : h ∈ HSpace (n := n)) (t s : I n) :
    prefixT h t s + prefixT h (t + 1) s = h t s := by
  rcases val_add_one_lt_or_eq_pred (n := n) t with ht | rfl
  · rw [← ZMod.natCast_zmod_val t, natCast_val_add_one t ht]
    rw [prefixT_natCast_succ (h := h) (s := s) ht]
    simp [add_assoc, add_left_comm, add_comm, F_add_self]
  · rw [natCast_pred_add_one_eq_zero, prefixT_zero]
    simpa using prefixT_last_eq_of_colSum_eq_zero (h := h) s (colSum_eq_zero_of_mem_HSpace hh s)

lemma prefixR_pair_eq_of_mem_HSpace {n : ℕ} [NeZero n] {h : HFun n}
    (hh : h ∈ HSpace (n := n)) (t s : I n) :
    prefixR h t s + prefixR h t (s + 1) = h t s := by
  rcases val_add_one_lt_or_eq_pred (n := n) s with hs | rfl
  · rw [← ZMod.natCast_zmod_val s, natCast_val_add_one s hs]
    rw [prefixR_natCast_succ (h := h) (t := t) hs]
    simp [add_assoc, add_left_comm, add_comm, F_add_self]
  · rw [natCast_pred_add_one_eq_zero, prefixR_zero]
    simpa using prefixR_last_eq_of_rowSum_eq_zero (h := h) t (rowSum_eq_zero_of_mem_HSpace hh t)

lemma build_mem_SSpace_of_mem_HSpace {n : ℕ} [NeZero n] (h : HSpace (n := n))
    (u v : UVFun n) :
    (buildB h.1 u, buildC h.1 v) ∈ SSpace (n := n) := by
  change visibleConstraintMap (buildB h.1 u, buildC h.1 v) = 0
  funext x y p q'
  simp [visibleConstraintMap, visibleConstraint_build_eq_visibleCore,
    visibleCore_eq_zero_of_mem_HSpace h.2 (x + y) (p + q')]

lemma visibleHData_build_eq {n : ℕ} [NeZero n] (h : HSpace (n := n)) (u : UVFun n) (v : UVFun n) :
    visibleHData (buildB h.1 u, buildC h.1 v) = h.1 := by
  funext t s
  calc
    visibleHData (buildB h.1 u, buildC h.1 v) t s
      = prefixT h.1 t s + prefixT h.1 (t + 1) s := by
          calc
            visibleHData (buildB h.1 u, buildC h.1 v) t s
                = (u 0 s + u 0 s) + (prefixT h.1 t s + prefixT h.1 (t + 1) s) := by
                    simp [visibleHData, buildB, add_assoc, add_left_comm, add_comm]
            _ = prefixT h.1 t s + prefixT h.1 (t + 1) s := by
                    simp [F_add_self]
    _ = h.1 t s := prefixT_pair_eq_of_mem_HSpace h.2 t s

lemma visibleUData_build_eq {n : ℕ} [NeZero n] (h : HSpace (n := n)) (u : UVFun n) (v : UVFun n) :
    visibleUData (buildB h.1 u, buildC h.1 v) = u := by
  funext p q'
  exact buildB_zero h.1 u p q'

lemma visibleVData_build_eq {n : ℕ} [NeZero n] (h : HSpace (n := n)) (u : UVFun n) (v : UVFun n) :
    visibleVData (buildB h.1 u, buildC h.1 v) = v := by
  funext x y
  exact buildC_zero h.1 v x y

noncomputable def rectDecomp {n : ℕ} [NeZero n] (h : HFun n) : HFun n :=
  ∑ a : I n, ∑ b : I n, h a b • rect a b

def tensorB {n : ℕ} (x : Profile n) (b : BCoef n) : BFun n :=
  fun a t p q => x a * b t p q

def tensorC {n : ℕ} (y : Profile n) (c : CCoef n) : CFun n :=
  fun a v w r => y a * c v w r

def kappaB {n : ℕ} (b : BCoef n) : AFun n :=
  fun u2 u3 u4 u5 => b (u2 + u3) u4 u5 + b (u2 + u3 + 1) u4 u5

def kappaC {n : ℕ} (c : CCoef n) : AFun n :=
  fun u2 u3 u4 u5 => c u2 u3 (u4 + u5) + c u2 u3 (u4 + u5 + 1)

noncomputable def Qpair {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) : F :=
  ∑ a : I n, ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
    ((B a (v + w) p q' * C a v w (p + q')) +
      (B a (v + w + 1) p q' * C a v w (p + q' + 1)))

noncomputable def q {n : ℕ} [NeZero n] (b : BCoef n) (c : CCoef n) : F :=
  ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
    ((b (v + w) p q' * c v w (p + q')) + (b (v + w + 1) p q' * c v w (p + q' + 1)))

lemma kappa_tensor {n : ℕ} [NeZero n] (x y : Profile n) (b : BCoef n) (c : CCoef n) :
    kappa (tensorB x b) (tensorC y c) = sigma x • kappaB b + sigma y • kappaC c := by
  funext u2 u3 u4 u5
  unfold kappa tensorB tensorC sigma kappaB kappaC
  change
    ((∑ u1 : I n, (x u1 * b (u2 + u3) u4 u5 + x u1 * b (u2 + u3 + 1) u4 u5)) +
        (∑ u1 : I n, (y u1 * c u2 u3 (u4 + u5) + y u1 * c u2 u3 (u4 + u5 + 1)))) =
      ((∑ a : I n, x a) * (b (u2 + u3) u4 u5 + b (u2 + u3 + 1) u4 u5)) +
        ((∑ a : I n, y a) * (c u2 u3 (u4 + u5) + c u2 u3 (u4 + u5 + 1)))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [mul_add, mul_add]
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]

lemma Qpair_tensor {n : ℕ} [NeZero n] (x y : Profile n) (b : BCoef n) (c : CCoef n) :
    Qpair (tensorB x b) (tensorC y c) = dot x y * q b c := by
  unfold Qpair dot q tensorB tensorC
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [mul_assoc]
  refine Finset.sum_congr rfl ?_
  intro a ha
  refine Finset.sum_congr rfl ?_
  intro v hv
  refine Finset.sum_congr rfl ?_
  intro w hw
  refine Finset.sum_congr rfl ?_
  intro p hp
  refine Finset.sum_congr rfl ?_
  intro q' hq
  ring

end No16
