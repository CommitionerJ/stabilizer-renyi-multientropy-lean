import Core3loop.Basic

open scoped BigOperators

namespace Core3loop

abbrev ProfileCard (a n : ℕ) [NeZero n] : ℕ := n ^ (a - 1)

instance instNeZeroProfileCard {a n : ℕ} [NeZero n] : NeZero (ProfileCard a n) := by
  dsimp [ProfileCard]
  exact ⟨pow_ne_zero (a - 1) (NeZero.ne n)⟩

noncomputable def sigmaProfile {a n : ℕ} [NeZero n] (x : ProfileABC a n) : F :=
  ∑ p, x p

noncomputable def dotProfile {a n : ℕ} [NeZero n] (x y : ProfileABC a n) : F :=
  ∑ p, x p * y p

def oneProfile {a n : ℕ} : ProfileABC a n := fun _ => 1

def deltaProfile {a n : ℕ} (p0 : XCoord a n) : ProfileABC a n :=
  fun p => if p = p0 then 1 else 0

lemma profile_dim {a n : ℕ} [NeZero n] :
    Module.finrank F (ProfileABC a n) = n ^ (a - 1) := by
  change Module.finrank F (XCoord a n → F) = n ^ (a - 1)
  rw [Module.finrank_pi_fintype (R := F) (M := fun _ : XCoord a n => F)]
  simp [F, ZMod.card]

lemma sigma_oneProfile_eq_card {a n : ℕ} [NeZero n] :
    sigmaProfile (a := a) (n := n) oneProfile = (Fintype.card (XCoord a n) : F) := by
  unfold sigmaProfile oneProfile
  simp

lemma sigma_oneProfile_eq_one_of_odd {a n : ℕ} [NeZero n]
    (hodd : Odd (Fintype.card (XCoord a n))) :
    sigmaProfile (a := a) (n := n) oneProfile = 1 := by
  rcases hodd with ⟨k, hk⟩
  rw [sigma_oneProfile_eq_card (a := a) (n := n), hk, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  have h2 : (((2 : ℕ) : F)) = 0 := by decide
  rw [h2, zero_mul, zero_add]

lemma sigma_oneProfile_eq_zero_of_even {a n : ℕ} [NeZero n]
    (heven : Even (Fintype.card (XCoord a n))) :
    sigmaProfile (a := a) (n := n) oneProfile = 0 := by
  rcases heven with ⟨k, hk⟩
  rw [sigma_oneProfile_eq_card (a := a) (n := n), hk, Nat.cast_add]
  exact F_add_self (k : F)

lemma odd_card_XCoord_of_odd {a n : ℕ} [NeZero n] (hn : Odd n) :
    Odd (Fintype.card (XCoord a n)) := by
  simpa [card_XCoord] using Odd.pow (a := n) (n := a - 1) hn

lemma odd_card_XCoord_of_a_eq_one {a n : ℕ} [NeZero n] (ha : a = 1) :
    Odd (Fintype.card (XCoord a n)) := by
  subst ha
  simp [card_XCoord]

lemma even_card_XCoord_of_even {a n : ℕ} [NeZero n] (heven : Even n) (ha2 : 2 ≤ a) :
    Even (Fintype.card (XCoord a n)) := by
  have hexp : a - 1 ≠ 0 := by omega
  simpa [card_XCoord] using Even.pow_of_ne_zero (a := n) heven hexp

lemma dot_deltaProfile {a n : ℕ} [NeZero n] (x : ProfileABC a n) (p0 : XCoord a n) :
    dotProfile x (deltaProfile p0) = x p0 := by
  unfold dotProfile deltaProfile
  rw [Finset.sum_eq_single p0]
  · simp
  · intro p _ hp
    simp [hp]
  · simp

lemma dot_add_right {a n : ℕ} [NeZero n] (x y z : ProfileABC a n) :
    dotProfile x (y + z) = dotProfile x y + dotProfile x z := by
  unfold dotProfile
  simp [mul_add, Finset.sum_add_distrib]

lemma dot_add_left {a n : ℕ} [NeZero n] (x y z : ProfileABC a n) :
    dotProfile (x + y) z = dotProfile x z + dotProfile y z := by
  unfold dotProfile
  simp [add_mul, Finset.sum_add_distrib]

lemma dot_comm {a n : ℕ} [NeZero n] (x y : ProfileABC a n) :
    dotProfile x y = dotProfile y x := by
  unfold dotProfile
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [mul_comm]

lemma dot_smul_right {a n : ℕ} [NeZero n] (x y : ProfileABC a n) (c : F) :
    dotProfile x (c • y) = dotProfile x y * c := by
  unfold dotProfile
  calc
    ∑ i : XCoord a n, x i * (c * y i) = ∑ i : XCoord a n, c * (x i * y i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    _ = c * ∑ i : XCoord a n, x i * y i := by
      symm
      exact Finset.mul_sum Finset.univ (fun i : XCoord a n => x i * y i) c
    _ = (∑ i : XCoord a n, x i * y i) * c := by
      simp [mul_comm]

lemma dot_smul_left {a n : ℕ} [NeZero n] (c : F) (x y : ProfileABC a n) :
    dotProfile (c • x) y = c * dotProfile x y := by
  unfold dotProfile
  calc
    ∑ i : XCoord a n, (c * x i) * y i = ∑ i : XCoord a n, c * (x i * y i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    _ = c * ∑ i : XCoord a n, x i * y i := by
      symm
      exact Finset.mul_sum Finset.univ (fun i : XCoord a n => x i * y i) c

lemma sigma_eq_dot_oneProfile {a n : ℕ} [NeZero n] (x : ProfileABC a n) :
    sigmaProfile x = dotProfile x oneProfile := by
  unfold sigmaProfile dotProfile oneProfile
  congr with p
  simp

lemma dot_self_eq_sigma {a n : ℕ} [NeZero n] (x : ProfileABC a n) :
    dotProfile x x = sigmaProfile x := by
  have hsq : ∀ z : F, z * z = z := by
    intro z
    fin_cases z <;> decide
  unfold dotProfile sigmaProfile
  congr with p
  exact hsq (x p)

lemma dot_nondegenerate {a n : ℕ} [NeZero n] {x : ProfileABC a n}
    (hx : ∀ y : ProfileABC a n, dotProfile x y = 0) : x = 0 := by
  funext p
  have hp := hx (deltaProfile p)
  simpa [dot_deltaProfile] using hp

noncomputable def sigmaProfileMap {a n : ℕ} [NeZero n] : ProfileABC a n →ₗ[F] F where
  toFun := sigmaProfile
  map_add' := by
    intro x y
    unfold sigmaProfile
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    unfold sigmaProfile
    simp [Finset.mul_sum]

noncomputable def dotLeftProfileMap {a n : ℕ} [NeZero n] (y : ProfileABC a n) :
    ProfileABC a n →ₗ[F] F where
  toFun := fun x => dotProfile x y
  map_add' := by
    intro x z
    exact dot_add_left x z y
  map_smul' := by
    intro c x
    simpa [mul_comm] using dot_smul_left (a := a) (n := n) c x y

noncomputable def OddLine {a n : ℕ} [NeZero n] : Submodule F (ProfileABC a n) :=
  F ∙ oneProfile

noncomputable def Wodd {a n : ℕ} [NeZero n] : Submodule F (ProfileABC a n) :=
  LinearMap.ker (sigmaProfileMap (a := a) (n := n))

lemma sigma_eq_zero_of_mem_Wodd {a n : ℕ} [NeZero n] {x : ProfileABC a n}
    (hx : x ∈ Wodd (a := a) (n := n)) :
    sigmaProfile x = 0 := by
  change sigmaProfileMap (a := a) (n := n) x = 0 at hx
  simpa [sigmaProfileMap] using hx

lemma dot_self_eq_zero_of_mem_Wodd {a n : ℕ} [NeZero n] {x : ProfileABC a n}
    (hx : x ∈ Wodd (a := a) (n := n)) :
    dotProfile x x = 0 := by
  rw [dot_self_eq_sigma]
  exact sigma_eq_zero_of_mem_Wodd hx

lemma oneProfile_ne_zero {a n : ℕ} [NeZero n] : (oneProfile (a := a) (n := n)) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [oneProfile] at h0

lemma sigmaProfileMap_surjective_of_odd {a n : ℕ} [NeZero n]
    (hodd : Odd (Fintype.card (XCoord a n))) :
    Function.Surjective (sigmaProfileMap (a := a) (n := n)) := by
  intro b
  fin_cases b
  · exact ⟨0, by
      change sigmaProfile (0 : ProfileABC a n) = 0
      simp [sigmaProfile]⟩
  · exact ⟨oneProfile, sigma_oneProfile_eq_one_of_odd (a := a) (n := n) hodd⟩

lemma finrank_Wodd_of_odd {a n : ℕ} [NeZero n]
    (hodd : Odd (Fintype.card (XCoord a n))) :
    Module.finrank F (Wodd (a := a) (n := n)) = n ^ (a - 1) - 1 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (sigmaProfileMap (a := a) (n := n))
  have hsurj : LinearMap.range (sigmaProfileMap (a := a) (n := n)) = ⊤ :=
    (LinearMap.range_eq_top).2 (sigmaProfileMap_surjective_of_odd (a := a) (n := n) hodd)
  rw [hsurj] at hdim
  rw [profile_dim] at hdim
  have hdim' : Module.finrank F ↥(⊤ : Submodule F F) + Module.finrank F (Wodd (a := a) (n := n)) =
      n ^ (a - 1) := by
    simpa [Wodd] using hdim
  have htop : Module.finrank F ↥(⊤ : Submodule F F) = 1 := by
    simp
  rw [htop] at hdim'
  omega

lemma oddLine_disjoint_Wodd_of_odd {a n : ℕ} [NeZero n]
    (hodd : Odd (Fintype.card (XCoord a n))) :
    Disjoint (OddLine (a := a) (n := n)) (Wodd (a := a) (n := n)) := by
  rw [Submodule.disjoint_def]
  intro x hxL hxW
  rcases Submodule.mem_span_singleton.mp hxL with ⟨c, rfl⟩
  change sigmaProfileMap (a := a) (n := n) (c • oneProfile) = 0 at hxW
  have hc : c = 0 := by
    simpa [sigmaProfileMap, sigma_oneProfile_eq_one_of_odd (a := a) (n := n) hodd] using hxW
  simp [hc]

lemma oddLine_sup_Wodd_eq_top_of_odd {a n : ℕ} [NeZero n]
    (hodd : Odd (Fintype.card (XCoord a n))) :
    OddLine (a := a) (n := n) ⊔ Wodd (a := a) (n := n) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  let y : ProfileABC a n := x + sigmaProfile x • oneProfile
  have hyW : y ∈ Wodd (a := a) (n := n) := by
    change sigmaProfileMap (a := a) (n := n) y = 0
    calc
      sigmaProfileMap (a := a) (n := n) y
          = sigmaProfileMap (a := a) (n := n) x +
              sigmaProfileMap (a := a) (n := n) (sigmaProfile x • oneProfile) := by
                simp [y]
      _ = sigmaProfile x + sigmaProfile x := by
            simp [sigmaProfileMap, sigma_oneProfile_eq_one_of_odd (a := a) (n := n) hodd]
      _ = 0 := F_add_self (sigmaProfile x)
  have hxL : sigmaProfile x • oneProfile ∈ OddLine (a := a) (n := n) := by
    exact Submodule.mem_span_singleton.2 ⟨sigmaProfile x, rfl⟩
  have hcancel : sigmaProfile x • oneProfile + y = x := by
    funext p
    change sigmaProfile x * 1 + (x p + sigmaProfile x * 1) = x p
    simp [y, add_assoc, add_left_comm, add_comm, F_add_self]
  exact Submodule.mem_sup.2 ⟨sigmaProfile x • oneProfile, hxL, y, hyW, hcancel⟩

lemma dot_nondegenerate_on_Wodd_of_odd {a n : ℕ} [NeZero n]
    (hodd : Odd (Fintype.card (XCoord a n))) {x : ProfileABC a n}
    (hxW : x ∈ Wodd (a := a) (n := n))
    (hx : ∀ y : ProfileABC a n, y ∈ Wodd (a := a) (n := n) → dotProfile x y = 0) :
    x = 0 := by
  apply dot_nondegenerate
  intro y
  have hyTop : y ∈ (⊤ : Submodule F (ProfileABC a n)) := by simp
  rw [← oddLine_sup_Wodd_eq_top_of_odd (a := a) (n := n) hodd] at hyTop
  rcases Submodule.mem_sup.1 hyTop with ⟨l, hl, w, hw, rfl⟩
  rw [dot_add_right, hx w hw]
  rcases Submodule.mem_span_singleton.1 hl with ⟨c, rfl⟩
  rw [dot_smul_right, ← sigma_eq_dot_oneProfile]
  simp [sigma_eq_zero_of_mem_Wodd hxW]

lemma finrank_Wodd_of_odd_n {a n : ℕ} [NeZero n] (hn : Odd n) :
    Module.finrank F (Wodd (a := a) (n := n)) = n ^ (a - 1) - 1 := by
  exact finrank_Wodd_of_odd (a := a) (n := n) (odd_card_XCoord_of_odd (a := a) hn)

lemma oddLine_sup_Wodd_eq_top_of_odd_n {a n : ℕ} [NeZero n] (hn : Odd n) :
    OddLine (a := a) (n := n) ⊔ Wodd (a := a) (n := n) = ⊤ := by
  exact oddLine_sup_Wodd_eq_top_of_odd (a := a) (n := n) (odd_card_XCoord_of_odd (a := a) hn)

lemma oddLine_sup_Wodd_eq_top_of_a_eq_one {n : ℕ} [NeZero n] :
    OddLine (a := 1) (n := n) ⊔ Wodd (a := 1) (n := n) = ⊤ := by
  exact oddLine_sup_Wodd_eq_top_of_odd (a := 1) (n := n) (odd_card_XCoord_of_a_eq_one rfl)

def eProfile {a n : ℕ} : ProfileABC a n := oneProfile

def fProfile {a n : ℕ} : ProfileABC a n := deltaProfile (0 : XCoord a n)

noncomputable def evenPairMap {a n : ℕ} [NeZero n] : ProfileABC a n →ₗ[F] F × F where
  toFun := fun x => (dotProfile x (eProfile (a := a) (n := n)), dotProfile x (fProfile (a := a) (n := n)))
  map_add' := by
    intro x y
    ext <;> simp [dot_add_left, eProfile, fProfile]
  map_smul' := by
    intro c x
    ext <;> simp [dot_smul_left, eProfile, fProfile]

noncomputable def Ueven {a n : ℕ} [NeZero n] : Submodule F (ProfileABC a n) :=
  LinearMap.ker (evenPairMap (a := a) (n := n))

noncomputable def EvenLineE {a n : ℕ} [NeZero n] : Submodule F (ProfileABC a n) :=
  F ∙ eProfile (a := a) (n := n)

noncomputable def EvenLineEF {a n : ℕ} [NeZero n] : Submodule F (ProfileABC a n) :=
  F ∙ (eProfile (a := a) (n := n) + fProfile (a := a) (n := n))

noncomputable def EvenPlane {a n : ℕ} [NeZero n] : Submodule F (ProfileABC a n) :=
  EvenLineEF (a := a) (n := n) ⊔ EvenLineE (a := a) (n := n)

lemma dot_eProfile_eProfile_even {a n : ℕ} [NeZero n]
    (heven : Even (Fintype.card (XCoord a n))) :
    dotProfile (eProfile (a := a) (n := n)) (eProfile (a := a) (n := n)) = 0 := by
  rw [dot_self_eq_sigma]
  simpa [eProfile] using sigma_oneProfile_eq_zero_of_even (a := a) (n := n) heven

lemma dot_eProfile_fProfile {a n : ℕ} [NeZero n] :
    dotProfile (eProfile (a := a) (n := n)) (fProfile (a := a) (n := n)) = 1 := by
  simpa [eProfile, fProfile] using dot_deltaProfile (a := a) (n := n) (oneProfile (a := a) (n := n))
    (0 : XCoord a n)

lemma dot_fProfile_fProfile {a n : ℕ} [NeZero n] :
    dotProfile (fProfile (a := a) (n := n)) (fProfile (a := a) (n := n)) = 1 := by
  calc
    dotProfile (fProfile (a := a) (n := n)) (fProfile (a := a) (n := n))
        = deltaProfile (a := a) (n := n) (0 : XCoord a n) (0 : XCoord a n) := by
            simpa [fProfile] using
              dot_deltaProfile (a := a) (n := n)
                (deltaProfile (a := a) (n := n) (0 : XCoord a n))
                (0 : XCoord a n)
    _ = 1 := by
          simp [deltaProfile]

lemma evenPairMap_eProfile {a n : ℕ} [NeZero n]
    (heven : Even (Fintype.card (XCoord a n))) :
    evenPairMap (a := a) (n := n) (eProfile (a := a) (n := n)) = (0, 1) := by
  ext
  · simpa [evenPairMap] using dot_eProfile_eProfile_even (a := a) (n := n) heven
  · simpa [evenPairMap] using dot_eProfile_fProfile (a := a) (n := n)

lemma evenPairMap_fProfile {a n : ℕ} [NeZero n] :
    evenPairMap (a := a) (n := n) (fProfile (a := a) (n := n)) = (1, 1) := by
  ext
  · simpa [evenPairMap, dot_comm] using dot_eProfile_fProfile (a := a) (n := n)
  · simpa [evenPairMap] using dot_fProfile_fProfile (a := a) (n := n)

lemma evenPairMap_e_add_f {a n : ℕ} [NeZero n]
    (heven : Even (Fintype.card (XCoord a n))) :
    evenPairMap (a := a) (n := n) (eProfile (a := a) (n := n) + fProfile (a := a) (n := n)) = (1, 0) := by
  rw [LinearMap.map_add]
  rw [evenPairMap_eProfile (a := a) (n := n) heven, evenPairMap_fProfile (a := a) (n := n)]
  ext <;> decide

lemma evenPairMap_surjective {a n : ℕ} [NeZero n]
    (heven : Even (Fintype.card (XCoord a n))) :
    Function.Surjective (evenPairMap (a := a) (n := n)) := by
  intro z
  rcases z with ⟨u, v⟩
  fin_cases u <;> fin_cases v
  · exact ⟨0, by
      change evenPairMap (a := a) (n := n) (0 : ProfileABC a n) = (0, 0)
      ext <;> simp [evenPairMap, dotProfile, eProfile, fProfile]⟩
  · exact ⟨eProfile (a := a) (n := n), evenPairMap_eProfile (a := a) (n := n) heven⟩
  · exact ⟨eProfile (a := a) (n := n) + fProfile (a := a) (n := n),
      evenPairMap_e_add_f (a := a) (n := n) heven⟩
  · exact ⟨fProfile (a := a) (n := n), evenPairMap_fProfile (a := a) (n := n)⟩

lemma finrank_Ueven_of_even {a n : ℕ} [NeZero n]
    (heven : Even (Fintype.card (XCoord a n))) :
    Module.finrank F (Ueven (a := a) (n := n)) = n ^ (a - 1) - 2 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (evenPairMap (a := a) (n := n))
  have hsurj : LinearMap.range (evenPairMap (a := a) (n := n)) = ⊤ :=
    (LinearMap.range_eq_top).2 (evenPairMap_surjective (a := a) (n := n) heven)
  rw [hsurj] at hdim
  rw [profile_dim] at hdim
  have hdim' : Module.finrank F ↥(⊤ : Submodule F (F × F)) + Module.finrank F (Ueven (a := a) (n := n)) =
      n ^ (a - 1) := by
    simpa [Ueven] using hdim
  have htop : Module.finrank F ↥(⊤ : Submodule F (F × F)) = 2 := by
    simp [Module.finrank_prod]
  rw [htop] at hdim'
  omega

lemma finrank_Ueven_of_even_n {a n : ℕ} [NeZero n] (hn : Even n) (ha2 : 2 ≤ a) :
    Module.finrank F (Ueven (a := a) (n := n)) = n ^ (a - 1) - 2 := by
  exact finrank_Ueven_of_even (a := a) (n := n) (even_card_XCoord_of_even (a := a) hn ha2)

lemma evenPlane_disjoint_Ueven {a n : ℕ} [NeZero n]
    (heven : Even (Fintype.card (XCoord a n))) :
    Disjoint (EvenPlane (a := a) (n := n)) (Ueven (a := a) (n := n)) := by
  rw [Submodule.disjoint_def]
  intro x hxP hxU
  rcases Submodule.mem_sup.1 hxP with ⟨xEF, hxEF, xE, hxE, rfl⟩
  rcases Submodule.mem_span_singleton.1 hxEF with ⟨u, rfl⟩
  rcases Submodule.mem_span_singleton.1 hxE with ⟨v, rfl⟩
  change evenPairMap (a := a) (n := n)
      (u • (eProfile (a := a) (n := n) + fProfile (a := a) (n := n)) + v • eProfile (a := a) (n := n)) = 0 at hxU
  rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
    evenPairMap_e_add_f (a := a) (n := n) heven, evenPairMap_eProfile (a := a) (n := n) heven] at hxU
  have hu : u = 0 := by
    have hfst := congrArg Prod.fst hxU
    simpa using hfst
  have hv : v = 0 := by
    have hsnd := congrArg Prod.snd hxU
    simpa using hsnd
  simp [hu, hv]

lemma evenPlane_sup_Ueven_eq_top {a n : ℕ} [NeZero n]
    (heven : Even (Fintype.card (XCoord a n))) :
    EvenPlane (a := a) (n := n) ⊔ Ueven (a := a) (n := n) = ⊤ := by
  apply top_unique
  intro x hx
  let u : F := (evenPairMap (a := a) (n := n) x).1
  let v : F := (evenPairMap (a := a) (n := n) x).2
  let y : ProfileABC a n :=
    u • (eProfile (a := a) (n := n) + fProfile (a := a) (n := n)) + v • eProfile (a := a) (n := n)
  have hyP : y ∈ EvenPlane (a := a) (n := n) := by
    refine Submodule.mem_sup.2 ?_
    refine ⟨u • (eProfile (a := a) (n := n) + fProfile (a := a) (n := n)), ?_,
      v • eProfile (a := a) (n := n), ?_, rfl⟩
    · exact Submodule.mem_span_singleton.2 ⟨u, rfl⟩
    · exact Submodule.mem_span_singleton.2 ⟨v, rfl⟩
  have hyMap : evenPairMap (a := a) (n := n) y = (u, v) := by
    dsimp [y, u, v]
    rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
      evenPairMap_e_add_f (a := a) (n := n) heven, evenPairMap_eProfile (a := a) (n := n) heven]
    ext <;> simp
  have hzU : x + y ∈ Ueven (a := a) (n := n) := by
    change evenPairMap (a := a) (n := n) (x + y) = 0
    rw [LinearMap.map_add, hyMap]
    ext <;> simp [u, v, F_add_self]
  refine Submodule.mem_sup.2 ?_
  exact ⟨y, hyP, x + y, hzU, by
    funext p
    simp [y, add_assoc, add_left_comm, add_comm, F_add_self]⟩

end Core3loop
