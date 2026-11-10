import No16.OperatorT

open scoped BigOperators

namespace No16

abbrev ProfilePair (n : ℕ) := Profile n × Profile n

noncomputable def sigmaMap {n : ℕ} [NeZero n] : Profile n →ₗ[F] F where
  toFun := sigma
  map_add' := by
    intro x y
    unfold sigma
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    unfold sigma
    simp [Finset.mul_sum]

noncomputable def dotLeftMap {n : ℕ} [NeZero n] (y : Profile n) : Profile n →ₗ[F] F where
  toFun := fun x => dot x y
  map_add' := by
    intro x z
    unfold dot
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    unfold dot
    simp [Pi.smul_apply, mul_assoc, Finset.mul_sum]

def oneProfile {n : ℕ} : Profile n := fun _ => 1

noncomputable def OddLine {n : ℕ} [NeZero n] : Submodule F (Profile n) :=
  F ∙ oneProfile (n := n)

noncomputable def Wodd {n : ℕ} [NeZero n] : Submodule F (Profile n) :=
  LinearMap.ker (sigmaMap (n := n))

abbrev INonzero (n : ℕ) [NeZero n] := { a : I n // a ≠ 0 }

def nzProfile {n : ℕ} [NeZero n] (a : INonzero n) : Profile n :=
  basisProfile a.1 + basisProfile 0

def eProfile {n : ℕ} : Profile n := oneProfile

def fProfile {n : ℕ} : Profile n := basisProfile 0

noncomputable def evenPairMap {n : ℕ} [NeZero n] : Profile n →ₗ[F] F × F where
  toFun := fun x => (dot x (eProfile (n := n)), dot x (fProfile (n := n)))
  map_add' := by
    intro x y
    ext <;> simp [dotLeftMap, dot, add_mul, Finset.sum_add_distrib, eProfile, fProfile]
  map_smul' := by
    intro a x
    ext <;> simp [dotLeftMap, dot, Pi.smul_apply, mul_assoc, Finset.mul_sum, eProfile, fProfile]

noncomputable def Ueven {n : ℕ} [NeZero n] : Submodule F (Profile n) :=
  LinearMap.ker (evenPairMap (n := n))

noncomputable def EvenLineE {n : ℕ} [NeZero n] : Submodule F (Profile n) :=
  F ∙ eProfile (n := n)

noncomputable def EvenLineEF {n : ℕ} [NeZero n] : Submodule F (Profile n) :=
  F ∙ (eProfile (n := n) + fProfile (n := n))

noncomputable def EvenPlane {n : ℕ} [NeZero n] : Submodule F (Profile n) :=
  EvenLineEF (n := n) ⊔ EvenLineE (n := n)

lemma sigma_eq_dot_oneProfile {n : ℕ} [NeZero n] (x : Profile n) :
    sigma x = dot x (oneProfile (n := n)) := by
  unfold sigma dot oneProfile
  congr with a
  simp

lemma sigma_eq_zero_of_mem_Wodd {n : ℕ} [NeZero n] {x : Profile n} (hx : x ∈ Wodd (n := n)) :
    sigma x = 0 := by
  change sigmaMap (n := n) x = 0 at hx
  simpa [sigmaMap] using hx

lemma dot_add_right {n : ℕ} [NeZero n] (x y z : Profile n) :
    dot x (y + z) = dot x y + dot x z := by
  unfold dot
  simp [mul_add, Finset.sum_add_distrib]

lemma dot_smul_right {n : ℕ} [NeZero n] (x y : Profile n) (a : F) :
    dot x (a • y) = dot x y * a := by
  unfold dot
  calc
    ∑ i : I n, x i * (a * y i) = ∑ i : I n, a * (x i * y i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    _ = a * ∑ i : I n, x i * y i := by
      symm
      exact Finset.mul_sum Finset.univ (fun i : I n => x i * y i) a
    _ = (∑ i : I n, x i * y i) * a := by
      simp [mul_comm]

lemma dot_self_eq_sigma {n : ℕ} [NeZero n] (x : Profile n) :
    dot x x = sigma x := by
  have hsq : ∀ z : F, z * z = z := by
    intro z
    fin_cases z <;> decide
  unfold dot sigma
  congr with a
  exact hsq (x a)

lemma dot_self_eq_zero_of_mem_Wodd {n : ℕ} [NeZero n] {x : Profile n} (hx : x ∈ Wodd (n := n)) :
    dot x x = 0 := by
  rw [dot_self_eq_sigma]
  exact sigma_eq_zero_of_mem_Wodd hx

lemma oneProfile_ne_zero {n : ℕ} [NeZero n] : oneProfile (n := n) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [oneProfile] at h0

lemma sigma_oneProfile_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    sigma (oneProfile (n := n)) = 1 := by
  rcases hn with ⟨k, rfl⟩
  unfold sigma oneProfile
  rw [show (∑ _ : I (2 * k + 1), (1 : F)) = (((2 * k + 1 : ℕ) : F)) by
    simp [I, ZMod.card]]
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  have h2 : (((2 : ℕ) : F)) = 0 := by decide
  rw [h2, zero_mul, zero_add]

lemma sigma_eProfile_even {n : ℕ} [NeZero n] (hn : Even n) :
    sigma (eProfile (n := n)) = 0 := by
  rcases hn with ⟨k, rfl⟩
  unfold sigma eProfile oneProfile
  rw [show (∑ _ : I (k + k), (1 : F)) = (((k + k : ℕ) : F)) by
    simp [I, ZMod.card]]
  rw [Nat.cast_add]
  exact F_add_self (k : F)

lemma sigma_fProfile {n : ℕ} [NeZero n] :
    sigma (fProfile (n := n)) = 1 := by
  unfold sigma fProfile basisProfile
  rw [Finset.sum_eq_single 0]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

lemma sigma_basisProfile {n : ℕ} [NeZero n] (a : I n) :
    sigma (basisProfile a) = 1 := by
  unfold sigma basisProfile
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

lemma nzProfile_mem_Wodd {n : ℕ} [NeZero n] (a : INonzero n) :
    nzProfile a ∈ Wodd (n := n) := by
  change sigmaMap (n := n) (nzProfile a) = 0
  change sigma (nzProfile a) = 0
  calc
    sigma (nzProfile a) = sigma (basisProfile a.1) + sigma (basisProfile (0 : I n)) := by
      unfold nzProfile sigma
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib]
    _ = 1 + 1 := by rw [sigma_basisProfile, sigma_basisProfile (a := (0 : I n))]
    _ = 0 := by simp [F_add_self]

lemma nzProfile_apply_zero {n : ℕ} [NeZero n] (a : INonzero n) :
    nzProfile a 0 = 1 := by
  have h0 : (0 : I n) ≠ a.1 := by
    simpa using a.2.symm
  simp [nzProfile, basisProfile, h0]

lemma nzProfile_apply_self {n : ℕ} [NeZero n] (a : INonzero n) :
    nzProfile a a.1 = 1 := by
  simp [nzProfile, basisProfile, a.2]

lemma nzProfile_apply_of_ne {n : ℕ} [NeZero n] (a : INonzero n) {t : I n}
    (ht0 : t ≠ 0) (hta : t ≠ a.1) :
    nzProfile a t = 0 := by
  simp [nzProfile, basisProfile, ht0, hta]

lemma dot_nzProfile_self {n : ℕ} [NeZero n] (a : INonzero n) :
    dot (nzProfile a) (nzProfile a) = 0 := by
  rw [dot_self_eq_sigma]
  exact sigma_eq_zero_of_mem_Wodd (nzProfile_mem_Wodd (n := n) a)

lemma dot_nzProfile_of_ne {n : ℕ} [NeZero n] (a b : INonzero n) (hab : a ≠ b) :
    dot (nzProfile a) (nzProfile b) = 1 := by
  rw [nzProfile, nzProfile, dot_add_right, dot_basisProfile, dot_basisProfile]
  have hab' : a.1 ≠ b.1 := by
    intro h
    apply hab
    apply Subtype.ext
    exact h
  have hba : b.1 ≠ a.1 := by
    intro h
    exact hab' h.symm
  have h0a : (0 : I n) ≠ a.1 := by
    simpa using a.2.symm
  simp [basisProfile, hab', hba, b.2, h0a]

noncomputable def nzProfileSum {n : ℕ} [NeZero n] (x : Profile n) : Profile n :=
  Finset.sum (Finset.univ.erase (0 : I n)) fun a => x a • (basisProfile a + basisProfile 0)

lemma nzProfileSum_apply_zero {n : ℕ} [NeZero n] (x : Profile n) :
    nzProfileSum x 0 = Finset.sum (Finset.univ.erase (0 : I n)) (fun a => x a) := by
  unfold nzProfileSum
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
  have h0a : (0 : I n) ≠ a := by
    intro h
    exact ha0 h.symm
  simp [Pi.smul_apply, basisProfile, h0a]

lemma nzProfileSum_apply_ne_zero {n : ℕ} [NeZero n] (x : Profile n) {t : I n} (ht : t ≠ 0) :
    nzProfileSum x t = x t := by
  unfold nzProfileSum
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single t]
  · simp [Pi.smul_apply, basisProfile, ht]
  · intro a ha hat
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have hta : t ≠ a := by
      intro h
      exact hat h.symm
    have h0a : (0 : I n) ≠ a := by
      intro h
      exact ha0 h.symm
    simp [Pi.smul_apply, basisProfile, ht, h0a, hta]
  · intro hnot
    have htmem : t ∈ Finset.univ.erase (0 : I n) := by
      simp [ht]
    exact False.elim (hnot htmem)

lemma sigma_basis_zero_add_nzProfileSum_eq {n : ℕ} [NeZero n] (x : Profile n) :
    sigma x • basisProfile (0 : I n) + nzProfileSum x = x := by
  funext t
  by_cases ht : t = 0
  · subst ht
    let s : F := Finset.sum (Finset.univ.erase (0 : I n)) (fun a => x a)
    have hsplit : s + x 0 = sigma x := by
      dsimp [s]
      simpa [sigma] using
        (Finset.sum_erase_add (Finset.univ : Finset (I n)) (fun a : I n => x a) (a := (0 : I n)) (by simp))
    calc
      (sigma x • basisProfile (0 : I n) + nzProfileSum x) 0
          = sigma x + nzProfileSum x 0 := by
              simp [Pi.smul_apply, basisProfile]
      _ = sigma x + s := by
            rw [nzProfileSum_apply_zero]
      _ = (s + x 0) + s := by
            rw [hsplit.symm]
      _ = x 0 := by
            have hcancel : ∀ a b : F, a + (a - b) = b := by
              intro a b
              fin_cases a <;> fin_cases b <;> decide
            simpa [s] using hcancel (sigma x) (x 0)
  · calc
      (sigma x • basisProfile (0 : I n) + nzProfileSum x) t
          = 0 + nzProfileSum x t := by
              simp [Pi.smul_apply, basisProfile, ht]
      _ = x t := by
            simpa [ht] using nzProfileSum_apply_ne_zero (x := x) ht

lemma nzProfileSum_eq_of_mem_Wodd {n : ℕ} [NeZero n] {x : Profile n} (hx : x ∈ Wodd (n := n)) :
    nzProfileSum x = x := by
  have hs : sigma x = 0 := sigma_eq_zero_of_mem_Wodd hx
  simpa [hs] using sigma_basis_zero_add_nzProfileSum_eq (x := x)

lemma mem_span_nzProfile_of_mem_Wodd {n : ℕ} [NeZero n] {x : Profile n}
    (hx : x ∈ Wodd (n := n)) :
    x ∈ Submodule.span F (Set.range (fun a : INonzero n => nzProfile a)) := by
  let P : Submodule F (Profile n) := Submodule.span F (Set.range (fun a : INonzero n => nzProfile a))
  rw [← nzProfileSum_eq_of_mem_Wodd hx]
  unfold nzProfileSum
  change Finset.sum (Finset.univ.erase (0 : I n))
      (fun a => x a • (basisProfile a + basisProfile 0)) ∈ P
  refine Submodule.sum_mem P ?_
  intro a ha
  have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
  change x a • nzProfile ⟨a, ha0⟩ ∈ P
  exact Submodule.smul_mem P _ (Submodule.subset_span ⟨⟨a, ha0⟩, rfl⟩)

lemma Wodd_le_span_nzProfile {n : ℕ} [NeZero n] :
    Wodd (n := n) ≤ Submodule.span F (Set.range (fun a : INonzero n => nzProfile a)) := by
  intro x hx
  exact mem_span_nzProfile_of_mem_Wodd hx

lemma span_nzProfile_le_Wodd {n : ℕ} [NeZero n] :
    Submodule.span F (Set.range (fun a : INonzero n => nzProfile a)) ≤ Wodd (n := n) := by
  rw [Submodule.span_le]
  intro x hx
  rcases hx with ⟨a, rfl⟩
  exact nzProfile_mem_Wodd a

lemma span_nzProfile_eq_Wodd {n : ℕ} [NeZero n] :
    Submodule.span F (Set.range (fun a : INonzero n => nzProfile a)) = Wodd (n := n) := by
  exact le_antisymm span_nzProfile_le_Wodd Wodd_le_span_nzProfile

lemma linearIndependent_nzProfile {n : ℕ} [NeZero n] :
    LinearIndependent F (fun a : INonzero n => nzProfile a) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hEval := congrFun hg i.1
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hEval
  rw [Finset.sum_eq_single i] at hEval
  · simpa [nzProfile_apply_self] using hEval
  · intro j _ hij
    have hji : j.1 ≠ i.1 := by
      intro h
      apply hij
      exact Subtype.ext h
    simp [nzProfile_apply_of_ne (a := j) (t := i.1) i.2 hji.symm]
  · simp

def nzSubprofile {n : ℕ} [NeZero n] (a : INonzero n) : ↥(Wodd (n := n)) :=
  ⟨nzProfile a, nzProfile_mem_Wodd a⟩

lemma linearIndependent_nzSubprofile {n : ℕ} [NeZero n] :
    LinearIndependent F (fun a : INonzero n => nzSubprofile a) := by
  have hcomp : LinearIndependent F ((Wodd (n := n)).subtype ∘ fun a : INonzero n => nzSubprofile a) := by
    simpa [nzSubprofile]
      using (linearIndependent_nzProfile (n := n))
  exact (LinearMap.linearIndependent_iff ((Wodd (n := n)).subtype) (Submodule.ker_subtype _)).1 hcomp

lemma top_le_span_nzSubprofile {n : ℕ} [NeZero n] :
    (⊤ : Submodule F ↥(Wodd (n := n))) ≤
      Submodule.span F (Set.range (fun a : INonzero n => nzSubprofile a)) := by
  intro x hx
  rw [Submodule.mem_span_range_iff_exists_fun]
  have hx' : x.1 ∈ Submodule.span F (Set.range (fun a : INonzero n => nzProfile a)) := by
    exact Wodd_le_span_nzProfile (n := n) x.2
  rcases (Submodule.mem_span_range_iff_exists_fun (R := F) (v := fun a : INonzero n => nzProfile a)
      (x := x.1)).1 hx' with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  simpa [nzSubprofile] using hc

noncomputable def nzBasis {n : ℕ} [NeZero n] : Module.Basis (INonzero n) F ↥(Wodd (n := n)) :=
  Module.Basis.mk (linearIndependent_nzSubprofile (n := n)) (top_le_span_nzSubprofile (n := n))

lemma finrank_Wodd_eq_card_INonzero {n : ℕ} [NeZero n] :
    Module.finrank F (Wodd (n := n)) = Fintype.card (INonzero n) := by
  exact Module.finrank_eq_card_basis (nzBasis (n := n))

lemma card_INonzero {n : ℕ} [NeZero n] :
    Fintype.card (INonzero n) = n - 1 := by
  have hcompl := Fintype.card_subtype_compl (fun a : I n => a = 0)
  simpa [INonzero, I, ZMod.card] using hcompl

lemma finrank_Wodd_eq {n : ℕ} [NeZero n] :
    Module.finrank F (Wodd (n := n)) = n - 1 := by
  rw [finrank_Wodd_eq_card_INonzero, card_INonzero]

lemma dot_add_left {n : ℕ} [NeZero n] (x y z : Profile n) :
    dot (x + y) z = dot x z + dot y z := by
  rw [dot_comm, dot_add_right, dot_comm x z, dot_comm y z]

lemma dot_smul_left {n : ℕ} [NeZero n] (a : F) (x y : Profile n) :
    dot (a • x) y = a * dot x y := by
  rw [dot_comm, dot_smul_right, dot_comm]
  simp [mul_comm]

lemma dot_sum_right {n : ℕ} [NeZero n] {α : Type*} (x : Profile n) (s : Finset α) (f : α → Profile n) :
    dot x (Finset.sum s f) = Finset.sum s (fun a => dot x (f a)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [dot_zero_right]
  · intro a s ha hs
    simp [ha, dot_add_right, hs]

lemma dot_sum_left {n : ℕ} [NeZero n] {α : Type*} (x : Profile n) (s : Finset α) (f : α → Profile n) :
    dot (Finset.sum s f) x = Finset.sum s (fun a => dot (f a) x) := by
  rw [dot_comm, dot_sum_right]
  simp_rw [dot_comm]

lemma dot_nzProfile_eq_indicator {n : ℕ} [NeZero n] (a b : INonzero n) :
    dot (nzProfile a) (nzProfile b) = if a = b then 0 else 1 := by
  by_cases h : a = b
  · subst h
    rw [dot_nzProfile_self]
    simp
  · rw [dot_nzProfile_of_ne _ _ h]
    simp [h]

def oddNzFin {m : ℕ} (k : Fin (2 * m)) : INonzero (2 * m + 1) :=
  ⟨((k.1 + 1 : ℕ) : I (2 * m + 1)), by
    have hk : k.1 + 1 < 2 * m + 1 := by omega
    intro h
    have hdiv : 2 * m + 1 ∣ k.1 + 1 := by
      exact (ZMod.natCast_eq_zero_iff (k.1 + 1) (2 * m + 1)).mp h
    have hle : 2 * m + 1 ≤ k.1 + 1 := Nat.le_of_dvd (by omega) hdiv
    omega⟩

lemma val_oddNzFin {m : ℕ} (k : Fin (2 * m)) :
    ((oddNzFin (m := m) k).1 : I (2 * m + 1)).val = k.1 + 1 := by
  have hk : k.1 + 1 < 2 * m + 1 := by omega
  show (((k.1 + 1 : ℕ) : I (2 * m + 1))).val = k.1 + 1
  exact ZMod.val_natCast_of_lt hk

lemma oddNzFin_injective {m : ℕ} : Function.Injective (oddNzFin (m := m)) := by
  intro k l h
  apply Fin.ext
  have hval :
      ((oddNzFin (m := m) k).1 : I (2 * m + 1)).val =
        ((oddNzFin (m := m) l).1 : I (2 * m + 1)).val :=
    congrArg (fun x : INonzero (2 * m + 1) => (x.1 : I (2 * m + 1)).val) h
  have : k.1 + 1 = l.1 + 1 := by
    simpa [val_oddNzFin] using hval
  omega

def oddIndexL {m : ℕ} (i : Fin m) : INonzero (2 * m + 1) :=
  oddNzFin (m := m) ⟨2 * i.1, by omega⟩

def oddIndexR {m : ℕ} (i : Fin m) : INonzero (2 * m + 1) :=
  oddNzFin (m := m) ⟨2 * i.1 + 1, by omega⟩

lemma val_oddIndexL {m : ℕ} (i : Fin m) :
    ((oddIndexL (m := m) i).1 : I (2 * m + 1)).val = 2 * i.1 + 1 := by
  simp [oddIndexL, val_oddNzFin]

lemma val_oddIndexR {m : ℕ} (i : Fin m) :
    ((oddIndexR (m := m) i).1 : I (2 * m + 1)).val = 2 * i.1 + 2 := by
  simp [oddIndexR, val_oddNzFin]

lemma oddIndexL_ne_oddIndexR {m : ℕ} (i j : Fin m) :
    oddIndexL i ≠ oddIndexR j := by
  intro h
  have hval :
      ((oddIndexL (m := m) i).1 : I (2 * m + 1)).val =
        ((oddIndexR (m := m) j).1 : I (2 * m + 1)).val :=
    congrArg (fun x : INonzero (2 * m + 1) => (x.1 : I (2 * m + 1)).val) h
  rw [val_oddIndexL, val_oddIndexR] at hval
  omega

lemma oddIndexR_ne_oddIndexL {m : ℕ} (i j : Fin m) :
    oddIndexR i ≠ oddIndexL j := by
  intro h
  have hval :
      ((oddIndexR (m := m) i).1 : I (2 * m + 1)).val =
        ((oddIndexL (m := m) j).1 : I (2 * m + 1)).val :=
    congrArg (fun x : INonzero (2 * m + 1) => (x.1 : I (2 * m + 1)).val) h
  rw [val_oddIndexR, val_oddIndexL] at hval
  omega

lemma oddIndexL_ne_oddIndexL {m : ℕ} {i j : Fin m} (h : i ≠ j) :
    oddIndexL i ≠ oddIndexL j := by
  intro hij
  apply h
  apply Fin.ext
  have hval :
      ((oddIndexL (m := m) i).1 : I (2 * m + 1)).val =
        ((oddIndexL (m := m) j).1 : I (2 * m + 1)).val :=
    congrArg (fun x : INonzero (2 * m + 1) => (x.1 : I (2 * m + 1)).val) hij
  rw [val_oddIndexL, val_oddIndexL] at hval
  omega

lemma oddIndexR_ne_oddIndexR {m : ℕ} {i j : Fin m} (h : i ≠ j) :
    oddIndexR i ≠ oddIndexR j := by
  intro hij
  apply h
  apply Fin.ext
  have hval :
      ((oddIndexR (m := m) i).1 : I (2 * m + 1)).val =
        ((oddIndexR (m := m) j).1 : I (2 * m + 1)).val :=
    congrArg (fun x : INonzero (2 * m + 1) => (x.1 : I (2 * m + 1)).val) hij
  rw [val_oddIndexR, val_oddIndexR] at hval
  omega

def oddPairU {m : ℕ} (i : Fin m) : Profile (2 * m + 1) :=
  nzProfile (oddIndexL i) + nzProfile (oddIndexR i)

noncomputable def oddPairPrev {m : ℕ} (i : Fin m) : Profile (2 * m + 1) :=
  Finset.sum Finset.univ (fun j : Fin i.1 => oddPairU (m := m) ⟨j.1, lt_trans j.2 i.2⟩)

noncomputable def oddPairV {m : ℕ} (i : Fin m) : Profile (2 * m + 1) :=
  nzProfile (oddIndexR i) + oddPairPrev (m := m) i

noncomputable def oddSymplecticFam {m : ℕ} : Fin m ⊕ Fin m → Profile (2 * m + 1)
  | Sum.inl i => oddPairU (m := m) i
  | Sum.inr i => oddPairV (m := m) i

lemma oddPairU_mem_Wodd {m : ℕ} (i : Fin m) :
    oddPairU (m := m) i ∈ Wodd (n := 2 * m + 1) := by
  exact Submodule.add_mem _ (nzProfile_mem_Wodd (oddIndexL i)) (nzProfile_mem_Wodd (oddIndexR i))

lemma oddPairPrev_mem_Wodd {m : ℕ} (i : Fin m) :
    oddPairPrev (m := m) i ∈ Wodd (n := 2 * m + 1) := by
  classical
  unfold oddPairPrev
  refine Submodule.sum_mem _ ?_
  intro j hj
  exact oddPairU_mem_Wodd (m := m) ⟨j.1, lt_trans j.2 i.2⟩

lemma oddPairV_mem_Wodd {m : ℕ} (i : Fin m) :
    oddPairV (m := m) i ∈ Wodd (n := 2 * m + 1) := by
  exact Submodule.add_mem _ (nzProfile_mem_Wodd (oddIndexR i)) (oddPairPrev_mem_Wodd (m := m) i)

lemma sum_range_indicator {m : ℕ} (i j : Fin m) :
    Finset.sum (Finset.range j.1) (fun k => if k = i.1 then (1 : F) else 0) =
      if i.1 < j.1 then 1 else 0 := by
  by_cases hij : i.1 < j.1
  · have himem : i.1 ∈ Finset.range j.1 := by simpa [Finset.mem_range] using hij
    rw [Finset.sum_eq_single_of_mem i.1 himem]
    · simp [hij]
    · intro b hb hbne
      simp [hbne]
  · have hnot : i.1 ∉ Finset.range j.1 := by simpa [Finset.mem_range] using hij
    have hzero : Finset.sum (Finset.range j.1) (fun k => if k = i.1 then (1 : F) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b hb
      have hbne : b ≠ i.1 := by
        intro hbi
        apply hnot
        simpa [hbi] using hb
      simp [hbne]
    rw [hzero]
    simp [hij]

lemma dot_oddPairU_right {m : ℕ} (i j : Fin m) :
    dot (oddPairU (m := m) i) (nzProfile (oddIndexR j)) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    unfold oddPairU
    rw [dot_add_left, dot_nzProfile_eq_indicator, dot_nzProfile_eq_indicator]
    simp [oddIndexL_ne_oddIndexR]
  · unfold oddPairU
    rw [dot_add_left, dot_nzProfile_eq_indicator, dot_nzProfile_eq_indicator]
    simp [h, oddIndexL_ne_oddIndexR, oddIndexR_ne_oddIndexR h, F_add_self]

lemma dot_oddPairU_oddPairU {m : ℕ} (i j : Fin m) :
    dot (oddPairU (m := m) i) (oddPairU (m := m) j) = 0 := by
  by_cases h : i = j
  · subst h
    exact dot_self_eq_zero_of_mem_Wodd (oddPairU_mem_Wodd (m := m) i)
  · unfold oddPairU
    rw [dot_add_left, dot_add_right, dot_add_right]
    rw [dot_nzProfile_eq_indicator, dot_nzProfile_eq_indicator,
      dot_nzProfile_eq_indicator, dot_nzProfile_eq_indicator]
    simp [h, oddIndexL_ne_oddIndexL h, oddIndexR_ne_oddIndexR h,
      oddIndexL_ne_oddIndexR, oddIndexR_ne_oddIndexL, F_add_self]

lemma dot_nzProfile_right_oddPairPrev {m : ℕ} (i j : Fin m) :
    dot (nzProfile (oddIndexR i)) (oddPairPrev (m := m) j) = if i.1 < j.1 then 1 else 0 := by
  classical
  unfold oddPairPrev
  rw [dot_sum_right]
  have hterm :
      ∀ a : Fin j.1,
        dot (nzProfile (oddIndexR i)) (oddPairU (m := m) ⟨a.1, lt_trans a.2 j.2⟩) =
          if a.1 = i.1 then 1 else 0 := by
    intro a
    have hbase := dot_oddPairU_right (m := m) ⟨a.1, lt_trans a.2 j.2⟩ i
    rw [dot_comm] at hbase
    by_cases h : a.1 = i.1
    · have hfin : (⟨a.1, lt_trans a.2 j.2⟩ : Fin m) = i := by
        exact Fin.ext h
      simpa [h, hfin] using hbase
    · have hfin : (⟨a.1, lt_trans a.2 j.2⟩ : Fin m) ≠ i := by
        intro hEq
        apply h
        exact congrArg Fin.val hEq
      simpa [h, hfin] using hbase
  simp_rw [hterm]
  by_cases hij : i.1 < j.1
  · let a0 : Fin j.1 := ⟨i.1, hij⟩
    rw [Finset.sum_eq_single_of_mem a0 (by simp)]
    · simp [a0, hij]
    · intro b hb hbne
      have hbne' : b.1 ≠ i.1 := by
        intro hEq
        apply hbne
        exact Fin.ext hEq
      simp [hbne']
  · have hzero : Finset.sum Finset.univ (fun a : Fin j.1 => if a.1 = i.1 then (1 : F) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro a ha
      have ha' : a.1 ≠ i.1 := by
        intro hEq
        apply hij
        rw [← hEq]
        exact a.2
      simp [ha']
    rw [hzero]
    simp [hij]

lemma dot_oddPairU_oddPairV {m : ℕ} (i j : Fin m) :
    dot (oddPairU (m := m) i) (oddPairV (m := m) j) = if i = j then 1 else 0 := by
  classical
  unfold oddPairV
  rw [dot_add_right, dot_oddPairU_right]
  have hsum : dot (oddPairU (m := m) i) (oddPairPrev (m := m) j) = 0 := by
    unfold oddPairPrev
    rw [dot_sum_right]
    refine Finset.sum_eq_zero ?_
    intro a ha
    simpa using dot_oddPairU_oddPairU (m := m) i ⟨a.1, lt_trans a.2 j.2⟩
  simp [hsum]

lemma dot_oddPairPrev_oddPairPrev {m : ℕ} (i j : Fin m) :
    dot (oddPairPrev (m := m) i) (oddPairPrev (m := m) j) = 0 := by
  classical
  unfold oddPairPrev
  rw [dot_sum_left]
  simp_rw [dot_sum_right]
  refine Finset.sum_eq_zero ?_
  intro a ha
  refine Finset.sum_eq_zero ?_
  intro b hb
  simpa using
    dot_oddPairU_oddPairU (m := m) ⟨a.1, lt_trans a.2 i.2⟩ ⟨b.1, lt_trans b.2 j.2⟩

lemma dot_oddPairV_oddPairV {m : ℕ} (i j : Fin m) :
    dot (oddPairV (m := m) i) (oddPairV (m := m) j) = 0 := by
  unfold oddPairV
  rw [dot_add_left, dot_add_right, dot_add_right]
  rw [dot_nzProfile_eq_indicator, dot_nzProfile_right_oddPairPrev,
    dot_comm, dot_nzProfile_right_oddPairPrev, dot_oddPairPrev_oddPairPrev]
  by_cases hij : i = j
  · subst hij
    simp
  · have hlt : i.1 < j.1 ∨ j.1 < i.1 := lt_or_gt_of_ne (by
        intro h
        apply hij
        exact Fin.ext h)
    have hneqR : oddIndexR i ≠ oddIndexR j := oddIndexR_ne_oddIndexR hij
    rcases hlt with hij' | hji'
    · simp [hneqR, hij', Nat.not_lt.mpr (Nat.le_of_lt hij'), F_add_self]
    · simp [hneqR, hji', Nat.not_lt.mpr (Nat.le_of_lt hji'), F_add_self]

lemma dot_oddPairV_oddPairU {m : ℕ} (i j : Fin m) :
    dot (oddPairV (m := m) i) (oddPairU (m := m) j) = if i = j then 1 else 0 := by
  rw [dot_comm, dot_oddPairU_oddPairV]
  simp [eq_comm]

lemma linearIndependent_oddSymplecticFam {m : ℕ} :
    LinearIndependent F (oddSymplecticFam (m := m)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro f hfg s
  cases s with
  | inl i =>
      have hEval := congrArg (fun x : Profile (2 * m + 1) => dot x (oddPairV (m := m) i)) hfg
      simpa [Fintype.sum_sum_type, oddSymplecticFam, dot_sum_left, dot_smul_left,
        dot_add_left, dot_add_right, dot_zero_left, dot_zero_right,
        dot_oddPairU_oddPairV, dot_oddPairV_oddPairV]
        using hEval
  | inr i =>
      have hEval := congrArg (fun x : Profile (2 * m + 1) => dot (oddPairU (m := m) i) x) hfg
      simpa [Fintype.sum_sum_type, oddSymplecticFam, dot_sum_right, dot_smul_right,
        dot_add_left, dot_add_right, dot_zero_left, dot_zero_right,
        dot_oddPairU_oddPairU, dot_oddPairV_oddPairV, dot_oddPairU_oddPairV, dot_comm]
        using hEval

noncomputable def oddSymplecticSubFam {m : ℕ} : Fin m ⊕ Fin m → ↥(Wodd (n := 2 * m + 1))
  | Sum.inl i => ⟨oddPairU (m := m) i, oddPairU_mem_Wodd (m := m) i⟩
  | Sum.inr i => ⟨oddPairV (m := m) i, oddPairV_mem_Wodd (m := m) i⟩

lemma linearIndependent_oddSymplecticSubFam {m : ℕ} :
    LinearIndependent F (oddSymplecticSubFam (m := m)) := by
  have hcomp :
      LinearIndependent F
        (fun s => (((oddSymplecticSubFam (m := m) s : ↥(Wodd (n := 2 * m + 1))) :
          Profile (2 * m + 1)))) := by
    have hEq :
        (fun s => (((oddSymplecticSubFam (m := m) s : ↥(Wodd (n := 2 * m + 1))) :
          Profile (2 * m + 1)))) = oddSymplecticFam (m := m) := by
      funext s
      cases s <;> rfl
    rw [hEq]
    exact linearIndependent_oddSymplecticFam (m := m)
  exact
    (LinearMap.linearIndependent_iff ((Wodd (n := 2 * m + 1)).subtype)
      (Submodule.ker_subtype _)).1 hcomp

lemma finrank_Wodd_oddIndex {m : ℕ} :
    Module.finrank F (Wodd (n := 2 * m + 1)) = 2 * m := by
  calc
    Module.finrank F (Wodd (n := 2 * m + 1)) = (2 * m + 1) - 1 := by
      simpa using (finrank_Wodd_eq (n := 2 * m + 1))
    _ = 2 * m := by omega

lemma span_oddSymplecticSubFam_eq_top {m : ℕ} :
    Submodule.span F (Set.range (oddSymplecticSubFam (m := m))) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card (linearIndependent_oddSymplecticSubFam (m := m))]
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  simpa [Fintype.card_sum, hcard, finrank_Wodd_oddIndex, two_mul]

noncomputable def oddSymplecticBasis {m : ℕ} :
    Module.Basis (Fin m ⊕ Fin m) F ↥(Wodd (n := 2 * m + 1)) :=
  Module.Basis.mk (linearIndependent_oddSymplecticSubFam (m := m))
    (by simpa [span_oddSymplecticSubFam_eq_top])

noncomputable def oddUCoord {m : ℕ} (x : ↥(Wodd (n := 2 * m + 1))) (i : Fin m) : F :=
  oddSymplecticBasis (m := m).repr x (Sum.inl i)

noncomputable def oddVCoord {m : ℕ} (x : ↥(Wodd (n := 2 * m + 1))) (i : Fin m) : F :=
  oddSymplecticBasis (m := m).repr x (Sum.inr i)

lemma oddSymplectic_sum_repr {m : ℕ} (x : ↥(Wodd (n := 2 * m + 1))) :
    ((x : ↥(Wodd (n := 2 * m + 1))) : Profile (2 * m + 1)) =
      (∑ i : Fin m, oddUCoord x i • oddPairU (m := m) i) +
        ∑ i : Fin m, oddVCoord x i • oddPairV (m := m) i := by
  have h := oddSymplecticBasis (m := m).sum_repr x
  have h' := congrArg (fun z : ↥(Wodd (n := 2 * m + 1)) => ((z : ↥(Wodd (n := 2 * m + 1))) :
    Profile (2 * m + 1))) h
  simpa [oddUCoord, oddVCoord, oddSymplecticBasis, oddSymplecticSubFam, Fintype.sum_sum_type]
    using h'.symm

lemma dot_sum_oddPairU_oddPairU {m : ℕ} (f g : Fin m → F) :
    dot (∑ i : Fin m, f i • oddPairU (m := m) i) (∑ j : Fin m, g j • oddPairU (m := m) j) = 0 := by
  rw [dot_sum_left]
  simp_rw [dot_sum_right]
  refine Finset.sum_eq_zero ?_
  intro i hi
  refine Finset.sum_eq_zero ?_
  intro j hj
  simp [dot_smul_left, dot_smul_right, dot_oddPairU_oddPairU]

lemma dot_sum_oddPairV_oddPairV {m : ℕ} (f g : Fin m → F) :
    dot (∑ i : Fin m, f i • oddPairV (m := m) i) (∑ j : Fin m, g j • oddPairV (m := m) j) = 0 := by
  rw [dot_sum_left]
  simp_rw [dot_sum_right]
  refine Finset.sum_eq_zero ?_
  intro i hi
  refine Finset.sum_eq_zero ?_
  intro j hj
  simp [dot_smul_left, dot_smul_right, dot_oddPairV_oddPairV]

lemma dot_sum_oddPairU_oddPairV {m : ℕ} (f g : Fin m → F) :
    dot (∑ i : Fin m, f i • oddPairU (m := m) i) (∑ j : Fin m, g j • oddPairV (m := m) j) =
      ∑ i : Fin m, f i * g i := by
  rw [dot_sum_left]
  simp_rw [dot_sum_right]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp [dot_smul_left, dot_smul_right, dot_oddPairU_oddPairV]
  · intro j hj hij
    have hij' : i ≠ j := by
      simpa [eq_comm] using hij
    simp [dot_smul_left, dot_smul_right, dot_oddPairU_oddPairV, hij']
  · simp [dot_smul_left, dot_smul_right, dot_oddPairU_oddPairV]

lemma dot_sum_oddPairV_oddPairU {m : ℕ} (f g : Fin m → F) :
    dot (∑ i : Fin m, f i • oddPairV (m := m) i) (∑ j : Fin m, g j • oddPairU (m := m) j) =
      ∑ i : Fin m, f i * g i := by
  rw [dot_sum_left]
  simp_rw [dot_sum_right]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp [dot_smul_left, dot_smul_right, dot_oddPairV_oddPairU]
  · intro j hj hij
    have hij' : i ≠ j := by
      simpa [eq_comm] using hij
    simp [dot_smul_left, dot_smul_right, dot_oddPairV_oddPairU, hij']
  · simp [dot_smul_left, dot_smul_right, dot_oddPairV_oddPairU]

lemma dot_oddSymplectic_coords {m : ℕ} (x y : ↥(Wodd (n := 2 * m + 1))) :
    dot (x : Profile (2 * m + 1)) (y : Profile (2 * m + 1)) =
      ∑ i : Fin m, (oddUCoord x i * oddVCoord y i + oddVCoord x i * oddUCoord y i) := by
  rw [oddSymplectic_sum_repr (m := m) x, oddSymplectic_sum_repr (m := m) y]
  rw [dot_add_left, dot_add_right, dot_add_right]
  rw [dot_sum_oddPairU_oddPairU, dot_sum_oddPairU_oddPairV,
    dot_sum_oddPairV_oddPairU, dot_sum_oddPairV_oddPairV]
  rw [zero_add, add_zero]
  simp_rw [← Finset.sum_add_distrib]

lemma dot_oneProfile_oneProfile_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    dot (oneProfile (n := n)) (oneProfile (n := n)) = 1 := by
  rw [← sigma_eq_dot_oneProfile]
  exact sigma_oneProfile_odd (n := n) hn

lemma dot_eProfile_eProfile_even {n : ℕ} [NeZero n] (hn : Even n) :
    dot (eProfile (n := n)) (eProfile (n := n)) = 0 := by
  have hs : sigma (oneProfile (n := n)) = 0 := by
    simpa [eProfile] using sigma_eProfile_even (n := n) hn
  rw [show eProfile (n := n) = oneProfile (n := n) by rfl]
  rw [← sigma_eq_dot_oneProfile (x := oneProfile (n := n))]
  exact hs

lemma dot_eProfile_fProfile {n : ℕ} [NeZero n] :
    dot (eProfile (n := n)) (fProfile (n := n)) = 1 := by
  rw [show eProfile (n := n) = oneProfile (n := n) by rfl]
  rw [show fProfile (n := n) = basisProfile 0 by rfl]
  rw [dot_basisProfile]
  simp [oneProfile]

lemma dot_fProfile_fProfile {n : ℕ} [NeZero n] :
    dot (fProfile (n := n)) (fProfile (n := n)) = 1 := by
  rw [show fProfile (n := n) = basisProfile 0 by rfl]
  rw [dot_basisProfile]
  simp [basisProfile]

lemma finrank_profile {n : ℕ} [NeZero n] : Module.finrank F (Profile n) = n := by
  change Module.finrank F (I n → F) = n
  rw [Module.finrank_pi_fintype (R := F) (M := fun _ : I n => F)]
  simp [I, ZMod.card]

lemma sigmaMap_surjective_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    Function.Surjective (sigmaMap (n := n)) := by
  intro a
  fin_cases a
  · exact ⟨0, by
      change sigma (0 : Profile n) = 0
      simp [sigma]⟩
  · exact ⟨oneProfile (n := n), by simpa [sigmaMap] using sigma_oneProfile_odd (n := n) hn⟩

lemma finrank_Wodd {n : ℕ} [NeZero n] (hn : Odd n) :
    Module.finrank F (Wodd (n := n)) = n - 1 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (sigmaMap (n := n))
  have hsurj : LinearMap.range (sigmaMap (n := n)) = ⊤ :=
    (LinearMap.range_eq_top).2 (sigmaMap_surjective_odd (n := n) hn)
  rw [hsurj] at hdim
  rw [finrank_profile] at hdim
  have hdim' : Module.finrank F ↥(⊤ : Submodule F F) + Module.finrank F (Wodd (n := n)) = n := by
    simpa [Wodd] using hdim
  have htop : Module.finrank F ↥(⊤ : Submodule F F) = 1 := by
    simp
  rw [htop] at hdim'
  omega

lemma oddLine_disjoint_Wodd {n : ℕ} [NeZero n] (hn : Odd n) :
    Disjoint (OddLine (n := n)) (Wodd (n := n)) := by
  rw [Submodule.disjoint_def]
  intro x hxL hxW
  rcases (Submodule.mem_span_singleton.mp hxL) with ⟨a, rfl⟩
  change sigmaMap (n := n) (a • oneProfile (n := n)) = 0 at hxW
  have ha : a = 0 := by
    simpa [sigmaMap, sigma_oneProfile_odd (n := n) hn] using hxW
  simp [ha]

lemma oddLine_sup_Wodd_eq_top {n : ℕ} [NeZero n] (hn : Odd n) :
    OddLine (n := n) ⊔ Wodd (n := n) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  let y : Profile n := x + sigma x • oneProfile (n := n)
  have hyW : y ∈ Wodd (n := n) := by
    change sigmaMap (n := n) y = 0
    calc
      sigmaMap (n := n) y
          = sigmaMap (n := n) x + sigmaMap (n := n) (sigma x • oneProfile (n := n)) := by
              simp [y]
      _ = sigma x + sigma x := by
            simp [sigmaMap, sigma_oneProfile_odd (n := n) hn]
      _ = 0 := F_add_self (sigma x)
  have hxL : sigma x • oneProfile (n := n) ∈ OddLine (n := n) := by
    exact Submodule.mem_span_singleton.2 ⟨sigma x, rfl⟩
  have hcancel : sigma x • oneProfile (n := n) + sigma x • oneProfile (n := n) = 0 := by
    funext a
    simp [F_add_self]
  refine Submodule.mem_sup.2 ?_
  refine ⟨sigma x • oneProfile (n := n), hxL, y, hyW, ?_⟩
  unfold y
  calc
    sigma x • oneProfile (n := n) + (x + sigma x • oneProfile (n := n))
        = (sigma x • oneProfile (n := n) + sigma x • oneProfile (n := n)) + x := by
            ac_rfl
    _ = 0 + x := by rw [hcancel]
    _ = x := by simp

lemma dot_nondegenerate_on_Wodd {n : ℕ} [NeZero n] (hn : Odd n) {x : Profile n}
    (hxW : x ∈ Wodd (n := n)) (hx : ∀ y : Profile n, y ∈ Wodd (n := n) → dot x y = 0) :
    x = 0 := by
  apply dot_nondegenerate
  intro y
  have hyTop : y ∈ (⊤ : Submodule F (Profile n)) := by simp
  rw [← oddLine_sup_Wodd_eq_top (n := n) hn] at hyTop
  rcases Submodule.mem_sup.1 hyTop with ⟨l, hl, w, hw, rfl⟩
  rw [dot_add_right, hx w hw]
  rcases Submodule.mem_span_singleton.1 hl with ⟨a, rfl⟩
  rw [dot_smul_right, ← sigma_eq_dot_oneProfile]
  simp [sigma_eq_zero_of_mem_Wodd hxW]

lemma evenPairMap_eProfile {n : ℕ} [NeZero n] (hn : Even n) :
    evenPairMap (n := n) (eProfile (n := n)) = (0, 1) := by
  ext <;> simp [evenPairMap, dot_eProfile_eProfile_even, dot_eProfile_fProfile, hn]

lemma evenPairMap_fProfile {n : ℕ} [NeZero n] :
    evenPairMap (n := n) (fProfile (n := n)) = (1, 1) := by
  ext <;> simp [evenPairMap, dot_eProfile_fProfile, dot_fProfile_fProfile, dot_comm]

lemma evenPairMap_e_add_f {n : ℕ} [NeZero n] (hn : Even n) :
    evenPairMap (n := n) (eProfile (n := n) + fProfile (n := n)) = (1, 0) := by
  rw [LinearMap.map_add]
  rw [evenPairMap_eProfile (n := n) hn, evenPairMap_fProfile (n := n)]
  ext <;> decide

lemma evenPairMap_surjective {n : ℕ} [NeZero n] (hn : Even n) :
    Function.Surjective (evenPairMap (n := n)) := by
  intro z
  rcases z with ⟨a, b⟩
  fin_cases a <;> fin_cases b
  · exact ⟨0, by
      ext <;> simp [evenPairMap, dot_zero_left]
      · rfl
      · rfl⟩
  · exact ⟨eProfile (n := n), evenPairMap_eProfile (n := n) hn⟩
  · exact ⟨eProfile (n := n) + fProfile (n := n), evenPairMap_e_add_f (n := n) hn⟩
  · exact ⟨fProfile (n := n), evenPairMap_fProfile (n := n)⟩

lemma finrank_Ueven {n : ℕ} [NeZero n] (hn : Even n) :
    Module.finrank F (Ueven (n := n)) = n - 2 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (evenPairMap (n := n))
  have hsurj : LinearMap.range (evenPairMap (n := n)) = ⊤ :=
    (LinearMap.range_eq_top).2 (evenPairMap_surjective (n := n) hn)
  rw [hsurj] at hdim
  rw [finrank_profile] at hdim
  have hdim' : Module.finrank F ↥(⊤ : Submodule F (F × F)) + Module.finrank F (Ueven (n := n)) = n := by
    simpa [Ueven] using hdim
  have htop : Module.finrank F ↥(⊤ : Submodule F (F × F)) = 2 := by
    simp [Module.finrank_prod]
  rw [htop] at hdim'
  omega

lemma evenPlane_disjoint_Ueven {n : ℕ} [NeZero n] (hn : Even n) :
    Disjoint (EvenPlane (n := n)) (Ueven (n := n)) := by
  rw [Submodule.disjoint_def]
  intro x hxP hxU
  rcases Submodule.mem_sup.1 hxP with ⟨xEF, hxEF, xE, hxE, rfl⟩
  rcases Submodule.mem_span_singleton.1 hxEF with ⟨a, rfl⟩
  rcases Submodule.mem_span_singleton.1 hxE with ⟨b, rfl⟩
  change
    evenPairMap (n := n) (a • (eProfile (n := n) + fProfile (n := n)) + b • eProfile (n := n)) = 0 at hxU
  rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
    evenPairMap_e_add_f (n := n) hn, evenPairMap_eProfile (n := n) hn] at hxU
  have ha : a = 0 := by
    have hfst := congrArg Prod.fst hxU
    simpa using hfst
  have hb : b = 0 := by
    have hsnd := congrArg Prod.snd hxU
    simpa using hsnd
  simp [ha, hb]

lemma evenPlane_sup_Ueven_eq_top {n : ℕ} [NeZero n] (hn : Even n) :
    EvenPlane (n := n) ⊔ Ueven (n := n) = ⊤ := by
  apply top_unique
  intro x hx
  let a : F := (evenPairMap (n := n) x).1
  let b : F := (evenPairMap (n := n) x).2
  let y : Profile n := a • (eProfile (n := n) + fProfile (n := n)) + b • eProfile (n := n)
  have hyP : y ∈ EvenPlane (n := n) := by
    refine Submodule.mem_sup.2 ?_
    refine ⟨a • (eProfile (n := n) + fProfile (n := n)), ?_, b • eProfile (n := n), ?_, rfl⟩
    · exact Submodule.mem_span_singleton.2 ⟨a, rfl⟩
    · exact Submodule.mem_span_singleton.2 ⟨b, rfl⟩
  have hyMap : evenPairMap (n := n) y = (a, b) := by
    rw [show y = a • (eProfile (n := n) + fProfile (n := n)) + b • eProfile (n := n) by rfl]
    rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
      evenPairMap_e_add_f (n := n) hn, evenPairMap_eProfile (n := n) hn]
    ext <;> simp [a, b]
  have hzU : x + y ∈ Ueven (n := n) := by
    change evenPairMap (n := n) (x + y) = 0
    rw [LinearMap.map_add, hyMap]
    ext <;> simp [a, b, F_add_self]
  refine Submodule.mem_sup.2 ?_
  exact ⟨y, hyP, x + y, hzU, by
    dsimp [y]
    funext i
    simp [eProfile, oneProfile, fProfile, basisProfile, add_assoc, add_left_comm, add_comm, F_add_self]
  ⟩

noncomputable def evenPlaneCoordInv {n : ℕ} [NeZero n] (z : F × F) : ↥(EvenPlane (n := n)) := by
  rcases z with ⟨a, b⟩
  refine ⟨a • (eProfile (n := n) + fProfile (n := n)) + b • eProfile (n := n), ?_⟩
  refine Submodule.mem_sup.2 ?_
  refine ⟨a • (eProfile (n := n) + fProfile (n := n)), ?_, b • eProfile (n := n), ?_, rfl⟩
  · exact Submodule.mem_span_singleton.2 ⟨a, rfl⟩
  · exact Submodule.mem_span_singleton.2 ⟨b, rfl⟩

noncomputable def evenPlaneCoordMap {n : ℕ} [NeZero n] : ↥(EvenPlane (n := n)) →ₗ[F] F × F where
  toFun x := evenPairMap (n := n) x.1
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro a x
    simp

lemma evenPlaneCoordMap_inv_apply {n : ℕ} [NeZero n] (hn : Even n) (z : F × F) :
    evenPlaneCoordMap (n := n) (evenPlaneCoordInv (n := n) z) = z := by
  rcases z with ⟨a, b⟩
  change evenPairMap (n := n) (a • (eProfile (n := n) + fProfile (n := n)) + b • eProfile (n := n)) = (a, b)
  rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
    evenPairMap_e_add_f (n := n) hn, evenPairMap_eProfile (n := n) hn]
  ext <;> simp

lemma evenPlaneCoordInv_map_apply {n : ℕ} [NeZero n] (hn : Even n) (x : ↥(EvenPlane (n := n))) :
    evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) x) = x := by
  apply Subtype.ext
  have hxP : (x : Profile n) ∈ EvenPlane (n := n) := x.2
  have hzU : (x : Profile n) + (evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) x)).1 ∈ Ueven (n := n) := by
    change evenPairMap (n := n) ((x : Profile n) + (evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) x)).1) = 0
    rw [LinearMap.map_add]
    change evenPlaneCoordMap (n := n) x + evenPlaneCoordMap (n := n) (evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) x)) = 0
    rw [evenPlaneCoordMap_inv_apply (n := n) hn]
    ext <;> simp [evenPlaneCoordMap, F_add_self]
  have hzP : (x : Profile n) + (evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) x)).1 ∈ EvenPlane (n := n) := by
    exact Submodule.add_mem _ hxP (evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) x)).2
  have hdisj := evenPlane_disjoint_Ueven (n := n) hn
  rw [Submodule.disjoint_def] at hdisj
  have hz0 : (x : Profile n) + (evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) x)).1 = 0 :=
    hdisj _ hzP hzU
  calc
    (evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) x)).1
        = (evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) x)).1 +
            ((x : Profile n) + (evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) x)).1) := by
              rw [hz0]
              simp
    _ = x := by
          funext i
          simp [add_assoc, add_left_comm, add_comm, F_add_self]

noncomputable def evenPlaneEquivProd {n : ℕ} [NeZero n] (hn : Even n) : ↥(EvenPlane (n := n)) ≃ₗ[F] F × F where
  toFun := evenPlaneCoordMap (n := n)
  invFun := evenPlaneCoordInv (n := n)
  left_inv := evenPlaneCoordInv_map_apply (n := n) hn
  right_inv := evenPlaneCoordMap_inv_apply (n := n) hn
  map_add' := (evenPlaneCoordMap (n := n)).map_add
  map_smul' := (evenPlaneCoordMap (n := n)).map_smul

lemma finrank_EvenPlane {n : ℕ} [NeZero n] (hn : Even n) :
    Module.finrank F (EvenPlane (n := n)) = 2 := by
  let e := evenPlaneEquivProd (n := n) hn
  calc
    Module.finrank F (EvenPlane (n := n)) = Module.finrank F (F × F) := by
      exact LinearEquiv.finrank_eq e
    _ = 2 := by
      simp [Module.finrank_prod]

noncomputable def omega {n : ℕ} [NeZero n] (x y : ProfilePair n) : F :=
  dot x.1 y.2 + dot x.2 y.1

lemma omega_self {n : ℕ} [NeZero n] (x : ProfilePair n) : omega x x = 0 := by
  unfold omega
  rw [dot_comm, F_add_self]

lemma omega_nondegenerate {n : ℕ} [NeZero n] {x : ProfilePair n}
    (hx : ∀ y : ProfilePair n, omega x y = 0) : x = 0 := by
  rcases x with ⟨x₁, x₂⟩
  apply Prod.ext
  · funext a
    have ha := hx (0, basisProfile a)
    simpa [omega, dot_zero_right, dot_zero_left, dot_basisProfile] using ha
  · funext a
    have ha := hx (basisProfile a, 0)
    simpa [omega, dot_zero_right, dot_zero_left, dot_basisProfile] using ha

end No16
