import TreeGraph.Basic

namespace TreeGraph

def indicatorZ (P : Prop) [Decidable P] : ℤ :=
  if P then 1 else 0

@[simp] theorem indicatorZ_true : indicatorZ True = 1 := by
  simp [indicatorZ]

@[simp] theorem indicatorZ_false : indicatorZ False = 0 := by
  simp [indicatorZ]

@[simp] theorem indicatorZ_of_pos {P : Prop} [Decidable P] (hP : P) :
    indicatorZ P = 1 := by
  simp [indicatorZ, hP]

@[simp] theorem indicatorZ_of_neg {P : Prop} [Decidable P] (hP : ¬ P) :
    indicatorZ P = 0 := by
  simp [indicatorZ, hP]

theorem indicatorZ_and_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    indicatorZ (P ∧ Q) = indicatorZ P * indicatorZ Q := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [indicatorZ, hP, hQ]

theorem prod_indicatorZ_eq_indicatorZ_forall
    {ι : Type} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] :
    (∏ i : ι, indicatorZ (P i)) = indicatorZ (∀ i, P i) := by
  classical
  by_cases h : ∀ i, P i
  · simp [indicatorZ, h]
  · have hexists : ∃ i, ¬ P i := by
      simpa [not_forall] using h
    rcases hexists with ⟨i, hi⟩
    have hprod : (∏ j : ι, indicatorZ (P j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [indicatorZ, hi])
    calc
      (∏ j : ι, indicatorZ (P j)) = 0 := hprod
      _ = indicatorZ (∀ i, P i) := by
        simp [indicatorZ, h]

theorem sum_indicatorZ_subtype
    {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (∑ x : α, indicatorZ (P x)) =
      (Fintype.card { x : α // P x } : ℤ) := by
  classical
  calc
    (∑ x : α, indicatorZ (P x)) =
        (Finset.univ.filter P).sum (fun _ : α => (1 : ℤ)) := by
      simp [indicatorZ]
    _ = ((Finset.univ.filter P).card : ℤ) := by
      simp
    _ = (Fintype.card { x : α // P x } : ℤ) := by
      exact congrArg Nat.cast
        ((Fintype.card_subtype P).symm)

private lemma F2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem sum_bitSign_linear
    {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
    (ℓ : V →ₗ[F2] F2) :
    (∑ v : V, bitSign (ℓ v)) =
      if ℓ = 0 then (Fintype.card V : ℤ) else 0 := by
  classical
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp
  · have hsurj : Function.Surjective ℓ := by
      intro y
      fin_cases y
      · use 0
        change ℓ 0 = 0
        simp
      · by_contra hnone
        have hzero_fun : ∀ v, ℓ v = 0 := by
          intro v
          have hv : ℓ v = 0 ∨ ℓ v = 1 := F2_eq_zero_or_one (ℓ v)
          rcases hv with hv | hv
          · exact hv
          · exfalso
            exact hnone ⟨v, hv⟩
        have hzero : ℓ = 0 := by
          ext v
          exact hzero_fun v
        exact hℓ hzero
    obtain ⟨v0, hv0⟩ := hsurj 1
    have htranslate :
        (∑ v : V, bitSign (ℓ (v + v0))) =
          ∑ v : V, bitSign (ℓ v) := by
      simpa using (Equiv.sum_comp (Equiv.addRight v0) (fun v : V => bitSign (ℓ v)))
    have hneg :
        (∑ v : V, bitSign (ℓ (v + v0))) =
          -∑ v : V, bitSign (ℓ v) := by
      calc
        (∑ v : V, bitSign (ℓ (v + v0))) =
            ∑ v : V, -bitSign (ℓ v) := by
              refine Finset.sum_congr rfl ?_
              intro v _
              simp [LinearMap.map_add, hv0, bitSign_add, mul_comm]
        _ = -∑ v : V, bitSign (ℓ v) := by
              simp
    have hsum : (∑ v : V, bitSign (ℓ v)) = 0 := by
      have h : (∑ v : V, bitSign (ℓ v)) = -∑ v : V, bitSign (ℓ v) := by
        calc
          (∑ v : V, bitSign (ℓ v)) =
              (∑ v : V, bitSign (ℓ (v + v0))) := htranslate.symm
          _ = -∑ v : V, bitSign (ℓ v) := hneg
      omega
    simp [hℓ, hsum]

theorem exists_apply_eq_one_of_linearMap_ne_zero
    {V : Type} [AddCommGroup V] [Module F2 V]
    (ℓ : V →ₗ[F2] F2) (hℓ : ℓ ≠ 0) :
    ∃ v : V, ℓ v = 1 := by
  by_contra hnone
  have hzero_fun : ∀ v, ℓ v = 0 := by
    intro v
    rcases F2_eq_zero_or_one (ℓ v) with hv | hv
    · exact hv
    · exfalso
      exact hnone ⟨v, hv⟩
  have hzero : ℓ = 0 := by
    ext v
    exact hzero_fun v
  exact hℓ hzero

theorem sum_bitSign_linear_mul_eq_zero_of_translate_invariant
    {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
    (ℓ : V →ₗ[F2] F2) (K : V → ℤ) (v0 : V)
    (hv0 : ℓ v0 = 1)
    (hK : ∀ v, K (v + v0) = K v) :
    (∑ v : V, bitSign (ℓ v) * K v) = 0 := by
  classical
  let S : ℤ := ∑ v : V, bitSign (ℓ v) * K v
  have htranslate :
      (∑ v : V, bitSign (ℓ (v + v0)) * K (v + v0)) = S := by
    simpa [S] using
      (Equiv.sum_comp (Equiv.addRight v0)
        (fun v : V => bitSign (ℓ v) * K v))
  have hneg :
      (∑ v : V, bitSign (ℓ (v + v0)) * K (v + v0)) = -S := by
    calc
      (∑ v : V, bitSign (ℓ (v + v0)) * K (v + v0)) =
          ∑ v : V, (-bitSign (ℓ v)) * K v := by
            refine Finset.sum_congr rfl ?_
            intro v _
            have hsign :
                bitSign (ℓ (v + v0)) = -bitSign (ℓ v) := by
              simp [LinearMap.map_add, hv0, bitSign_add, mul_comm]
            rw [hsign, hK v]
      _ = -S := by
            simp [S]
  have hS : S = -S := by
    calc
      S = (∑ v : V, bitSign (ℓ (v + v0)) * K (v + v0)) :=
        htranslate.symm
      _ = -S := hneg
  omega

theorem sum_bitSign_linear_mul_eq_zero_of_forall_translate_invariant
    {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
    (ℓ : V →ₗ[F2] F2) (K : V → ℤ)
    (hℓ : ℓ ≠ 0)
    (hK : ∀ v0, ℓ v0 = 1 → ∀ v, K (v + v0) = K v) :
    (∑ v : V, bitSign (ℓ v) * K v) = 0 := by
  rcases exists_apply_eq_one_of_linearMap_ne_zero ℓ hℓ with ⟨v0, hv0⟩
  exact
    sum_bitSign_linear_mul_eq_zero_of_translate_invariant
      ℓ K v0 hv0 (hK v0 hv0)

noncomputable def dotLinear (D : Type) [Fintype D] (c : D → F2) :
    (D → F2) →ₗ[F2] F2 where
  toFun α := ∑ d : D, α d * c d
  map_add' α β := by
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r α := by
    simp [Pi.smul_apply, Finset.mul_sum, mul_assoc]

@[simp] theorem dotLinear_apply (D : Type) [Fintype D]
    (c : D → F2) (α : D → F2) :
    dotLinear D c α = ∑ d : D, α d * c d := rfl

theorem dotLinear_eq_zero_iff (D : Type) [Fintype D] (c : D → F2) :
    dotLinear D c = 0 ↔ c = 0 := by
  classical
  constructor
  · intro h
    funext d
    have hd :=
      congrArg (fun ℓ : (D → F2) →ₗ[F2] F2 =>
        ℓ (Pi.single (M := fun _ : D => F2) d (1 : F2))) h
    have hsingle :
        (∑ d' : D,
          Pi.single (M := fun _ : D => F2) d (1 : F2) d' * c d') =
            c d := by
      rw [Fintype.sum_eq_single d]
      · simp
      · intro d' hd'
        simp [Pi.single_eq_of_ne, hd']
    simpa [dotLinear, hsingle] using hd
  · intro h
    subst h
    ext α
    simp [dotLinear]

noncomputable def linearFunctionalCoeff
    (D : Type) [Fintype D] [DecidableEq D]
    (ℓ : (D → F2) →ₗ[F2] F2) : D → F2 :=
  fun d => ℓ (Pi.single (M := fun _ : D => F2) d (1 : F2))

@[simp] theorem linearFunctionalCoeff_add
    (D : Type) [Fintype D] [DecidableEq D]
    (ℓ η : (D → F2) →ₗ[F2] F2) :
    linearFunctionalCoeff D (ℓ + η) =
      linearFunctionalCoeff D ℓ + linearFunctionalCoeff D η := by
  ext d
  simp [linearFunctionalCoeff]

@[simp] theorem linearFunctionalCoeff_smul
    (D : Type) [Fintype D] [DecidableEq D]
    (r : F2) (ℓ : (D → F2) →ₗ[F2] F2) :
    linearFunctionalCoeff D (r • ℓ) =
      r • linearFunctionalCoeff D ℓ := by
  ext d
  simp [linearFunctionalCoeff]

theorem function_eq_sum_single
    (D : Type) [Fintype D] [DecidableEq D] (α : D → F2) :
    α =
      ∑ d : D, α d • Pi.single (M := fun _ : D => F2) d (1 : F2) := by
  classical
  funext d
  rw [Finset.sum_apply]
  rw [Fintype.sum_eq_single d]
  · simp
  · intro d' hd'
    simp [hd']

theorem linearFunctional_eq_dotLinear_coeff
    (D : Type) [Fintype D] [DecidableEq D]
    (ℓ : (D → F2) →ₗ[F2] F2) :
    ℓ = dotLinear D (linearFunctionalCoeff D ℓ) := by
  classical
  apply LinearMap.ext
  intro α
  calc
    ℓ α =
        ℓ (∑ d : D,
          α d • Pi.single (M := fun _ : D => F2) d (1 : F2)) := by
          rw [← function_eq_sum_single D α]
    _ =
        ∑ d : D,
          α d • ℓ (Pi.single (M := fun _ : D => F2) d (1 : F2)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro d _
          rw [map_smul]
    _ = dotLinear D (linearFunctionalCoeff D ℓ) α := by
          simp [dotLinear, linearFunctionalCoeff, smul_eq_mul]

theorem linearFunctional_eq_zero_iff_coeff_zero
    (D : Type) [Fintype D] [DecidableEq D]
    (ℓ : (D → F2) →ₗ[F2] F2) :
    ℓ = 0 ↔ linearFunctionalCoeff D ℓ = 0 := by
  constructor
  · intro h
    subst ℓ
    ext d
    simp [linearFunctionalCoeff]
  · intro hcoeff
    rw [linearFunctional_eq_dotLinear_coeff D ℓ]
    exact (dotLinear_eq_zero_iff D (linearFunctionalCoeff D ℓ)).2 hcoeff

theorem sum_bitSign_dotLinear (D : Type) [Fintype D] [Fintype (D → F2)]
    (c : D → F2) :
    (∑ α : D → F2, bitSign (dotLinear D c α)) =
      if c = 0 then (Fintype.card (D → F2) : ℤ) else 0 := by
  classical
  calc
    (∑ α : D → F2, bitSign (dotLinear D c α)) =
        if dotLinear D c = 0 then (Fintype.card (D → F2) : ℤ) else 0 :=
      sum_bitSign_linear (dotLinear D c)
    _ = if c = 0 then (Fintype.card (D → F2) : ℤ) else 0 := by
      by_cases hc : c = 0
      · subst c
        have hzero : dotLinear D (0 : D → F2) = 0 := by
          ext α
          simp [dotLinear]
        simp [hzero]
      · have hL : dotLinear D c ≠ 0 := by
          intro h
          exact hc ((dotLinear_eq_zero_iff D c).1 h)
        simp [hc, hL]

theorem sum_prod_mul
    {α β R : Type} [Fintype α] [Fintype β] [CommSemiring R]
    (f : α → R) (g : β → R) :
    (∑ p : α × β, f p.1 * g p.2) =
      (∑ a : α, f a) * (∑ b : β, g b) := by
  classical
  calc
    (∑ p : α × β, f p.1 * g p.2) =
        ∑ a : α, ∑ b : β, f a * g b := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : α, f a * ∑ b : β, g b := by
      simp [Finset.mul_sum]
    _ = (∑ a : α, f a) * (∑ b : β, g b) := by
      rw [Finset.sum_mul]

theorem sum_prod_mul_left
    {α β R : Type} [Fintype α] [Fintype β] [CommSemiring R]
    (f : α → R) (g : β → R) :
    (∑ p : α × β, g p.2 * f p.1) =
      (∑ b : β, g b) * (∑ a : α, f a) := by
  calc
    (∑ p : α × β, g p.2 * f p.1) =
        ∑ p : α × β, f p.1 * g p.2 := by
      refine Finset.sum_congr rfl ?_
      intro p _
      rw [mul_comm]
    _ = (∑ a : α, f a) * (∑ b : β, g b) :=
      sum_prod_mul f g
    _ = (∑ b : β, g b) * (∑ a : α, f a) := by
      rw [mul_comm]

theorem sum_pi_product
    {ι α R : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [CommSemiring R]
    (g : ι → α → R) :
    (∑ f : ι → α, ∏ i, g i (f i)) =
      ∏ i, ∑ x : α, g i x := by
  simpa using
    (Fintype.prod_sum (ι := ι) (κ := fun _ : ι => α)
      (R := R) (fun i x => g i x)).symm

theorem sum_pi_product_dep
    {ι R : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] [CommSemiring R]
    (g : ∀ i, α i → R) :
    (∑ f : (i : ι) → α i, ∏ i, g i (f i)) =
      ∏ i, ∑ x : α i, g i x := by
  simpa using
    (Fintype.prod_sum (ι := ι) (κ := α)
      (R := R) (fun i x => g i x)).symm

theorem sum_pi_product_const
    {ι α R : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [CommSemiring R]
    (g : α → R) :
    (∑ f : ι → α, ∏ i, g (f i)) =
      (∑ x : α, g x) ^ Fintype.card ι := by
  rw [sum_pi_product (ι := ι) (α := α) (R := R)
    (fun _ x => g x)]
  rw [Finset.prod_const, Finset.card_univ]

theorem prod_bitSign_eq_bitSign_sum {α : Type} (s : Finset α)
    (f : α → F2) :
    s.prod (fun a => bitSign (f a)) = bitSign (s.sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, bitSign_add, ih]

theorem sum_pi_bitSign_dotLinear_product
    {ι D : Type} [Fintype ι] [DecidableEq ι]
    [Fintype D] [Fintype (D → F2)]
    (c : ι → D → F2) :
    (∑ f : ι → D → F2,
        ∏ i, bitSign (dotLinear D (c i) (f i))) =
      ∏ i, if c i = 0 then (Fintype.card (D → F2) : ℤ) else 0 := by
  rw [sum_pi_product
    (ι := ι) (α := D → F2) (R := ℤ)
    (fun i x => bitSign (dotLinear D (c i) x))]
  refine Finset.prod_congr rfl ?_
  intro i _
  exact sum_bitSign_dotLinear D (c i)

theorem sum_pi_bitSign_dotLinear_all_zero
    {ι D : Type} [Fintype ι] [DecidableEq ι]
    [Fintype D] [Fintype (D → F2)]
    (c : ι → D → F2) (hc : ∀ i, c i = 0) :
    (∑ f : ι → D → F2,
        ∏ i, bitSign (dotLinear D (c i) (f i))) =
      (Fintype.card (D → F2) : ℤ) ^ Fintype.card ι := by
  rw [sum_pi_bitSign_dotLinear_product]
  simp [hc]

theorem sum_pi_bitSign_dotLinear_exists_nonzero
    {ι D : Type} [Fintype ι] [DecidableEq ι]
    [Fintype D] [Fintype (D → F2)]
    (c : ι → D → F2) (hc : ∃ i, c i ≠ 0) :
    (∑ f : ι → D → F2,
        ∏ i, bitSign (dotLinear D (c i) (f i))) = 0 := by
  rw [sum_pi_bitSign_dotLinear_product]
  rcases hc with ⟨i, hi⟩
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sum_external_bitSign_dotLinear_pow
    {ι D : Type} [Fintype ι] [DecidableEq ι]
    [Fintype D] [Fintype (D → F2)]
    (c : D → F2) :
    (∑ f : ι → D → F2,
        ∏ i, bitSign (dotLinear D c (f i))) =
      (if c = 0 then (Fintype.card (D → F2) : ℤ) else 0) ^
        Fintype.card ι := by
  rw [sum_pi_bitSign_dotLinear_product
    (ι := ι) (D := D) (fun _ => c)]
  rw [Finset.prod_const, Finset.card_univ]

theorem sum_external_bitSign_dotLinear_zero
    {ι D : Type} [Fintype ι] [DecidableEq ι]
    [Fintype D] [Fintype (D → F2)]
    (c : D → F2) (hc : c = 0) :
    (∑ f : ι → D → F2,
        ∏ i, bitSign (dotLinear D c (f i))) =
      (Fintype.card (D → F2) : ℤ) ^ Fintype.card ι := by
  rw [sum_external_bitSign_dotLinear_pow]
  simp [hc]

theorem sum_external_bitSign_dotLinear_nonzero
    {ι D : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype D] [Fintype (D → F2)]
    (c : D → F2) (hc : c ≠ 0) :
    (∑ f : ι → D → F2,
        ∏ i, bitSign (dotLinear D c (f i))) = 0 := by
  rw [sum_external_bitSign_dotLinear_pow]
  have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
  simp [hc, Nat.pos_iff_ne_zero.mp hcard]

theorem int_two_pow_pow_toNat (E : ℤ) (k : Nat) :
    ((2 : ℤ) ^ Int.toNat E) ^ k =
      (2 : ℤ) ^ (Int.toNat E * k) := by
  rw [pow_mul]

end TreeGraph
