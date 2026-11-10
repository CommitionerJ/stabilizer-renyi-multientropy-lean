import Mathlib

open scoped BigOperators

namespace FormalMathLab
namespace CombinatorialAssignments

abbrev F₂ := ZMod 2

abbrev X (a n : ℕ) := Fin (a - 1) → ZMod n
abbrev Y (b n : ℕ) := Fin b → ZMod n

structure Assignment (a b n : ℕ) where
  f₁ : X a n → Y b n → F₂
  f₂ : X a n → Y b n → F₂
  f₃ : X a n → Y b n → F₂

def assignmentEquiv (a b n : ℕ) :
    Assignment a b n ≃
      (X a n → Y b n → F₂) ×
        ((X a n → Y b n → F₂) × (X a n → Y b n → F₂)) where
  toFun A := ⟨A.f₁, ⟨A.f₂, A.f₃⟩⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv A := by
    cases A
    rfl
  right_inv p := by
    cases p
    rfl

def sigma {b n : ℕ} (y : Y b n) : ZMod n :=
  ∑ i, y i

def Valid {a b n : ℕ} (A : Assignment a b n) : Prop :=
  (∀ x₁ x₂ y, A.f₁ x₁ y = A.f₁ x₂ y) ∧
    ∀ x y j, A.f₃ x y = A.f₂ x (y + Pi.single j 1)

abbrev ValidAssignments (a b n : ℕ) := { A : Assignment a b n // Valid A }

section Core

variable {a b n : ℕ}
variable [NeZero n]

noncomputable instance assignmentFintype (a b : ℕ) :
    Fintype (Assignment a b n) :=
  Fintype.ofEquiv _ (assignmentEquiv a b n).symm

abbrev XC (a : ℕ) := X (a + 1) n
abbrev YC (b : ℕ) := Y (b + 1) n
abbrev Tail (b : ℕ) := Fin b → ZMod n
abbrev AlphaSpace (b : ℕ) := YC (n := n) b → F₂
abbrev PhiSpace (a : ℕ) := XC (n := n) a × ZMod n → F₂

structure NormalForm (a b : ℕ) where
  alpha : AlphaSpace (n := n) b
  phi : PhiSpace (n := n) a

def normalFormEquivProd (a b : ℕ) :
    NormalForm (n := n) a b ≃ AlphaSpace (n := n) b × PhiSpace (n := n) a where
  toFun A := ⟨A.alpha, A.phi⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv A := by
    cases A
    rfl
  right_inv p := by
    cases p
    rfl

noncomputable instance normalFormFintype (a b : ℕ) :
    Fintype (NormalForm (n := n) a b) :=
  Fintype.ofEquiv _ (normalFormEquivProd (n := n) a b).symm

noncomputable instance validAssignmentsFintype (a b : ℕ) :
    Fintype (ValidAssignments a b n) := by
  classical
  exact Subtype.fintype _

def composeY (b : ℕ) (u : Tail (n := n) b) (s : ZMod n) : YC (n := n) b :=
  Fin.cons (s - ∑ i, u i) u

lemma composeY_eq_zero_add (b : ℕ) (u : Tail (n := n) b) (s : ZMod n) :
    composeY (n := n) b u s + Pi.single (0 : Fin (b + 1)) (1 : ZMod n) =
      composeY (n := n) b u (s + 1) := by
  ext i
  cases i using Fin.cases with
  | zero =>
      simp [composeY]
      abel
  | succ i =>
      simp [composeY, Pi.single_eq_of_ne]

lemma composeY_eq_succ_add
    (b : ℕ) (u : Tail (n := n) b) (s : ZMod n) (i : Fin b) :
    composeY (n := n) b u s + Pi.single i.succ (1 : ZMod n) =
      composeY (n := n) b (u + Pi.single i (1 : ZMod n)) (s + 1) := by
  ext j
  cases j using Fin.cases with
  | zero =>
      have hsum :
          (∑ x : Fin b,
              (u x + (Pi.single (M := fun _ : Fin b => ZMod n) i (1 : ZMod n)) x)) =
            (∑ x : Fin b, u x) + 1 := by
        rw [Finset.sum_add_distrib]
        simp
      simp [composeY, hsum]
  | succ j =>
      by_cases h : j = i
      · subst h
        simp [composeY]
      · simp [composeY, Pi.single_eq_of_ne, h]

lemma sigma_composeY (b : ℕ) (u : Tail (n := n) b) (s : ZMod n) :
    sigma (composeY (n := n) b u s) = s := by
  simp [sigma, composeY, Fin.sum_univ_succ]

lemma cons_add_single_zero (b : ℕ) (c : ZMod n) (u : Tail (n := n) b) :
    ((@Fin.cons b (fun _ => ZMod n) c u) +
        Pi.single (M := fun _ : Fin (b + 1) => ZMod n)
          (0 : Fin (b + 1)) (1 : ZMod n)) =
      @Fin.cons b (fun _ => ZMod n) (c + 1) u := by
  ext i
  cases i using Fin.cases with
  | zero =>
      simp
  | succ i =>
      simp [Pi.single_eq_of_ne]

lemma cons_zero_add_single_succ
    (b : ℕ) (u : Tail (n := n) b) (i : Fin b) :
    ((@Fin.cons b (fun _ => ZMod n) (0 : ZMod n) u) +
        Pi.single (M := fun _ : Fin (b + 1) => ZMod n)
          i.succ (1 : ZMod n)) =
      @Fin.cons b (fun _ => ZMod n) (0 : ZMod n)
        (u + Pi.single (M := fun _ : Fin b => ZMod n) i (1 : ZMod n)) := by
  ext j
  cases j using Fin.cases with
  | zero =>
      simp
  | succ j =>
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne, h]

lemma composeY_sigma (b : ℕ) (y : YC (n := n) b) :
    composeY (n := n) b (fun i => y i.succ) (sigma y) = y := by
  ext i
  cases i using Fin.cases with
  | zero =>
      simp [composeY, sigma, Fin.sum_univ_succ]
  | succ i =>
      simp [composeY]

lemma zmod_step_const {α : Type*} (g : ZMod n → α) (h : ∀ s, g (s + 1) = g s) :
    ∀ s, g s = g 0 := by
  intro s
  have hNat : ∀ m : ℕ, g (m : ZMod n) = g 0 := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m hm =>
        calc
          g ((m + 1 : ℕ) : ZMod n) = g ((m : ZMod n) + 1) := by simp
          _ = g (m : ZMod n) := h _
          _ = g 0 := hm
  simpa [ZMod.natCast_val] using hNat s.val

lemma tailInvariant_zero
    {ξ α : Type*}
    (b : ℕ)
    (β : ξ → Tail (n := n) b → ZMod n → α)
    (hstep : ∀ x u s i, β x (u + Pi.single i (1 : ZMod n)) s = β x u s) :
    ∀ x u s, β x u s = β x 0 s := by
  induction b with
  | zero =>
      intro x u s
      have : u = (fun i => nomatch i) := by
        funext i
        nomatch i
      subst this
      have h0 : (0 : Tail (n := n) 0) = (fun i => nomatch i) := by
        funext i
        nomatch i
      rw [h0]
  | succ b ih =>
      let β₀ : ξ → Tail (n := n) b → ZMod n → α := fun x u s => β x (Fin.cons 0 u) s
      have hfirst : ∀ x (u : Tail (n := n) b) s c, β x (Fin.cons c u) s = β₀ x u s := by
        intro x u s c
        let g : ZMod n → α := fun t => β x (Fin.cons t u) s
        have hg : ∀ t, g (t + 1) = g t := by
          intro t
          simpa [g, cons_add_single_zero] using
            (show
              β x (Fin.cons t u + Pi.single (0 : Fin (b + 1)) (1 : ZMod n)) s =
                β x (Fin.cons t u) s
             from
              hstep x (Fin.cons t u) s (0 : Fin (b + 1)))
        simpa [g, β₀] using zmod_step_const (n := n) g hg c
      have hstep₀ : ∀ x u s i, β₀ x (u + Pi.single i (1 : ZMod n)) s = β₀ x u s := by
        intro x u s i
        simpa [β₀, cons_zero_add_single_succ] using
          (show
            β x (Fin.cons 0 u + Pi.single i.succ (1 : ZMod n)) s =
              β x (Fin.cons 0 u) s
           from
            hstep x (Fin.cons 0 u) s i.succ)
      intro x u s
      let c : ZMod n := u 0
      let u' : Tail (n := n) b := fun i => u i.succ
      have hu : u = Fin.cons c u' := by
        ext i
        cases i using Fin.cases with
        | zero => rfl
        | succ i => rfl
      rw [hu]
      have hzero : (0 : Tail (n := n) (b + 1)) = Fin.cons 0 (0 : Tail (n := n) b) := by
        ext i
        cases i using Fin.cases with
        | zero => simp
        | succ i => simp
      rw [hzero]
      simpa [c, u', β₀] using (hfirst x u' s c).trans (ih β₀ hstep₀ x u' s)

lemma sigma_add_single (b : ℕ) (y : YC (n := n) b) (j : Fin (b + 1)) :
    sigma (y + Pi.single j (1 : ZMod n)) = sigma y + 1 := by
  cases j using Fin.cases with
  | zero =>
      simp [sigma, Fin.sum_univ_succ, add_assoc, add_comm]
  | succ j =>
      rw [sigma, sigma, Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h0 :
          (y + Pi.single (M := fun _ : Fin (b + 1) => ZMod n)
              j.succ (1 : ZMod n)) 0 = y 0 := by
        simp
      have hs :
          (∑ i : Fin b,
              (y + Pi.single (M := fun _ : Fin (b + 1) => ZMod n)
                  j.succ (1 : ZMod n)) i.succ) =
            (∑ i : Fin b, y i.succ) + 1 := by
        calc
          ∑ i : Fin b,
              (y + Pi.single (M := fun _ : Fin (b + 1) => ZMod n)
                  j.succ (1 : ZMod n)) i.succ
              =
            ∑ i : Fin b,
              (y i.succ + Pi.single (M := fun _ : Fin b => ZMod n) j (1 : ZMod n) i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hsingle :
                  Pi.single (M := fun _ : Fin (b + 1) => ZMod n)
                      j.succ (1 : ZMod n) i.succ =
                    Pi.single (M := fun _ : Fin b => ZMod n) j (1 : ZMod n) i := by
                by_cases h : i = j
                · subst h
                  simp
                · have hsucc : i.succ ≠ j.succ := by
                    intro hs
                    apply h
                    apply Fin.ext
                    exact Nat.succ.inj <| by
                      simpa using congrArg Fin.val hs
                  simp [Pi.single_eq_of_ne, h, hsucc]
              simpa [Pi.add_apply] using congrArg (fun t => y i.succ + t) hsingle
          _ =
            (∑ i : Fin b, y i.succ) +
              ∑ i : Fin b, Pi.single (M := fun _ : Fin b => ZMod n) j (1 : ZMod n) i := by
              rw [Finset.sum_add_distrib]
          _ = (∑ i : Fin b, y i.succ) + 1 := by
              simp
      rw [h0, hs]
      abel

def toAssignment (a b : ℕ) (nf : NormalForm (n := n) a b) :
    Assignment (a + 1) (b + 1) n where
  f₁ _ y := nf.alpha y
  f₂ x y := nf.phi (x, sigma y)
  f₃ x y := nf.phi (x, sigma y + 1)

lemma valid_toAssignment (a b : ℕ) (nf : NormalForm (n := n) a b) :
    Valid (toAssignment (n := n) a b nf) := by
  constructor
  · intro x₁ x₂ y
    rfl
  · intro x y j
    simp [toAssignment, sigma_add_single]

noncomputable def toNormalForm (a b : ℕ)
    (A : Assignment (a + 1) (b + 1) n) (hA : Valid A) :
    NormalForm (n := n) a b := by
  let alpha : AlphaSpace (n := n) b := fun y => A.f₁ default y
  let phi : PhiSpace (n := n) a := fun p => A.f₂ p.1 (composeY (n := n) b 0 p.2)
  exact
    { alpha := alpha
      phi := phi }

lemma toNormalForm_f₂ (a b : ℕ)
    (A : Assignment (a + 1) (b + 1) n) (hA : Valid A) :
    ∀ x y, A.f₂ x y = (toNormalForm (n := n) a b A hA).phi (x, sigma y) := by
  intro x y
  let beta : XC (n := n) a → Tail (n := n) b → ZMod n → F₂ :=
    fun x u s => A.f₂ x (composeY (n := n) b u s)
  have hstep : ∀ x u s i, beta x (u + Pi.single i (1 : ZMod n)) s = beta x u s := by
    intro x u s i
    have h0 := hA.2 x (composeY (n := n) b u (s - 1)) 0
    have hi := hA.2 x (composeY (n := n) b u (s - 1)) i.succ
    have h0' : A.f₃ x (composeY (n := n) b u (s - 1)) = beta x u s := by
      calc
        A.f₃ x (composeY (n := n) b u (s - 1))
            = A.f₂ x
                (composeY (n := n) b u (s - 1) +
                  Pi.single (0 : Fin (b + 1)) (1 : ZMod n)) := h0
        _ = beta x u s := by
          simp [beta, composeY_eq_zero_add]
    have hi' : A.f₃ x (composeY (n := n) b u (s - 1)) =
        beta x (u + Pi.single i (1 : ZMod n)) s := by
      calc
        A.f₃ x (composeY (n := n) b u (s - 1))
            = A.f₂ x
                (composeY (n := n) b u (s - 1) +
                  Pi.single i.succ (1 : ZMod n)) := hi
        _ = beta x (u + Pi.single i (1 : ZMod n)) s := by
          simp [beta, composeY_eq_succ_add]
    exact hi'.symm.trans h0'
  have hy : composeY (n := n) b (fun i => y i.succ) (sigma y) = y :=
    composeY_sigma (n := n) b y
  have hzero :=
    tailInvariant_zero (n := n) b beta hstep x (fun i => y i.succ) (sigma y)
  have hzero' : A.f₂ x y = A.f₂ x (composeY (n := n) b 0 (sigma y)) := by
    simpa [beta, hy] using hzero
  simpa [toNormalForm] using hzero'

lemma toNormalForm_f₃ (a b : ℕ)
    (A : Assignment (a + 1) (b + 1) n) (hA : Valid A) :
    ∀ x y, A.f₃ x y = (toNormalForm (n := n) a b A hA).phi (x, sigma y + 1) := by
  intro x y
  calc
    A.f₃ x y = A.f₂ x (y + Pi.single (0 : Fin (b + 1)) (1 : ZMod n)) := hA.2 x y 0
    _ =
      (toNormalForm (n := n) a b A hA).phi
        (x, sigma (y + Pi.single (0 : Fin (b + 1)) (1 : ZMod n))) := by
          exact toNormalForm_f₂ (n := n) a b A hA x
            (y + Pi.single (0 : Fin (b + 1)) (1 : ZMod n))
    _ = (toNormalForm (n := n) a b A hA).phi (x, sigma y + 1) := by
      rw [sigma_add_single]

lemma toNormalForm_toAssignment (a b : ℕ) (nf : NormalForm (n := n) a b) :
    toNormalForm (n := n) a b
        (toAssignment (n := n) a b nf)
        (valid_toAssignment (n := n) a b nf) =
      nf := by
  cases nf with
  | mk alpha phi =>
      simp [toNormalForm, toAssignment, sigma_composeY]

lemma toAssignment_toNormalForm (a b : ℕ)
    (A : Assignment (a + 1) (b + 1) n) (hA : Valid A) :
    toAssignment (n := n) a b (toNormalForm (n := n) a b A hA) = A := by
  cases A with
  | mk f₁ f₂ f₃ =>
      simp only [toAssignment, toNormalForm, Assignment.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · funext x y
        exact (hA.1 x default y).symm
      · funext x y
        exact (toNormalForm_f₂ (n := n) a b ⟨f₁, f₂, f₃⟩ hA x y).symm
      · funext x y
        exact (toNormalForm_f₃ (n := n) a b ⟨f₁, f₂, f₃⟩ hA x y).symm

noncomputable def normalFormEquiv (a b : ℕ) :
    ValidAssignments (a + 1) (b + 1) n ≃ NormalForm (n := n) a b where
  toFun A := toNormalForm (n := n) a b A.1 A.2
  invFun nf := ⟨toAssignment (n := n) a b nf, valid_toAssignment (n := n) a b nf⟩
  left_inv A := by
    apply Subtype.ext
    exact toAssignment_toNormalForm (n := n) a b A.1 A.2
  right_inv nf := toNormalForm_toAssignment (n := n) a b nf

lemma card_X (a : ℕ) :
    Fintype.card (XC (n := n) a) = n ^ a := by
  simpa [XC, X, ZMod.card] using
    (Fintype.card_fun (α := Fin a) (β := ZMod n))

lemma card_Y (b : ℕ) :
    Fintype.card (YC (n := n) b) = n ^ (b + 1) := by
  simpa [YC, Y, ZMod.card] using
    (Fintype.card_fun (α := Fin (b + 1)) (β := ZMod n))

lemma card_phiSpace (a : ℕ) :
    Fintype.card (PhiSpace (n := n) a) = 2 ^ (n ^ (a + 1)) := by
  change Fintype.card ((XC (n := n) a × ZMod n) → F₂) = 2 ^ (n ^ (a + 1))
  rw [Fintype.card_fun, Fintype.card_prod, card_X]
  simp [F₂, ZMod.card, ← Nat.pow_succ]

lemma card_alphaSpace (b : ℕ) :
    Fintype.card (AlphaSpace (n := n) b) = 2 ^ (n ^ (b + 1)) := by
  change Fintype.card (YC (n := n) b → F₂) = 2 ^ (n ^ (b + 1))
  rw [Fintype.card_fun, card_Y]
  simp [F₂]

theorem card_validAssignments_core (a b : ℕ) :
    Fintype.card (ValidAssignments (a + 1) (b + 1) n) =
      2 ^ (n ^ (b + 1) + n ^ (a + 1)) := by
  rw [Fintype.card_congr (normalFormEquiv (n := n) a b)]
  rw [Fintype.card_congr (normalFormEquivProd (n := n) a b), Fintype.card_prod]
  rw [card_alphaSpace, card_phiSpace]
  simpa [pow_add, Nat.pow_succ, mul_comm, mul_left_comm, mul_assoc]

def shift : (ZMod n → F₂) →ₗ[F₂] (ZMod n → F₂) where
  toFun u s := u s + u (s + 1)
  map_add' u v := by
    ext s
    simp [add_assoc, add_left_comm, add_comm]
  map_smul' c u := by
    ext s
    simp [mul_add]

def collapse (a : ℕ) : PhiSpace (n := n) a →ₗ[F₂] (ZMod n → F₂) where
  toFun φ s := ∑ x : XC (n := n) a, φ (x, s)
  map_add' φ ψ := by
    ext s
    simp [Finset.sum_add_distrib]
  map_smul' c φ := by
    ext s
    simp [Finset.mul_sum]

def constraint (a : ℕ) : PhiSpace (n := n) a →ₗ[F₂] (ZMod n → F₂) :=
  shift (n := n) ∘ₗ collapse (n := n) a

noncomputable instance constraintKerFintype (a : ℕ) :
    Fintype (LinearMap.ker (constraint (n := n) a)) := by
  classical
  exact Subtype.fintype _

lemma constraint_apply (a : ℕ) (φ : PhiSpace (n := n) a) (s : ZMod n) :
    constraint (n := n) a φ s =
      ∑ x : XC (n := n) a, (φ (x, s) + φ (x, s + 1)) := by
  simp [constraint, shift, collapse, Finset.sum_add_distrib]

lemma shift_ker_eq_const (u : LinearMap.ker (shift (n := n))) :
    ∀ s, u.1 s = u.1 0 := by
  have hstep : ∀ s, u.1 (s + 1) = u.1 s := by
    intro s
    have hs : shift (n := n) u.1 s = 0 := by
      have hu0 : u.1 ∈ LinearMap.ker (shift (n := n)) := u.2
      simpa [LinearMap.mem_ker, shift] using hu0
    have hs' : u.1 s = -u.1 (s + 1) := add_eq_zero_iff_eq_neg.mp hs
    simpa using hs'.symm
  exact zmod_step_const (n := n) u.1 hstep

noncomputable def shiftKerEquiv :
    LinearMap.ker (shift (n := n)) ≃ₗ[F₂] F₂ where
  toFun u := u.1 0
  map_add' u v := rfl
  map_smul' c u := rfl
  invFun c :=
    ⟨fun _ => c, LinearMap.mem_ker.mpr <| by
      ext s
      have : c + c = 0 := by
        fin_cases c <;> decide
      simpa [shift] using this⟩
  left_inv u := by
    apply Subtype.ext
    funext s
    exact (shift_ker_eq_const (n := n) u s).symm
  right_inv c := rfl

lemma finrank_shift_range :
    Module.finrank F₂ (LinearMap.range (shift (n := n))) = n - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (shift (n := n))
  rw [LinearEquiv.finrank_eq (shiftKerEquiv (n := n)),
    Module.finrank_fintype_fun_eq_card] at h
  have h' : Module.finrank F₂ (LinearMap.range (shift (n := n))) + 1 = n := by
    simpa [ZMod.card] using h
  omega

lemma sum_indicator_single (a : ℕ) (x0 : XC (n := n) a) (c : F₂) :
    (∑ x : XC (n := n) a, if x = x0 then c else 0) = c := by
  classical
  rw [Finset.sum_eq_single x0]
  · simp
  · intro x hx hxne
    simp [hxne]
  · intro hx0
    have hx0_mem : x0 ∈ (Finset.univ : Finset (XC (n := n) a)) := by
      simp
    exact (hx0 hx0_mem).elim

lemma range_constraint_eq_range_shift (a : ℕ) :
    LinearMap.range (constraint (n := n) a) = LinearMap.range (shift (n := n)) := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    refine ⟨collapse (n := n) a φ, rfl⟩
  · rintro _ ⟨u, rfl⟩
    classical
    let x0 : XC (n := n) a := 0
    let φ : PhiSpace (n := n) a := fun p => if p.1 = x0 then u p.2 else 0
    refine ⟨φ, ?_⟩
    ext s
    rw [constraint_apply, Finset.sum_add_distrib]
    simp only [φ]
    have hs :
        (∑ x : XC (n := n) a, if x = x0 then u s else 0) = u s :=
      sum_indicator_single (n := n) a x0 (u s)
    have hs' :
        (∑ x : XC (n := n) a, if x = x0 then u (s + 1) else 0) = u (s + 1) :=
      sum_indicator_single (n := n) a x0 (u (s + 1))
    rw [hs, hs']
    simp [shift]

lemma finrank_constraint_range (a : ℕ) :
    Module.finrank F₂ (LinearMap.range (constraint (n := n) a)) = n - 1 := by
  rw [range_constraint_eq_range_shift]
  exact finrank_shift_range (n := n)

theorem card_constraint_ker (a : ℕ) :
    Fintype.card (LinearMap.ker (constraint (n := n) a)) =
      2 ^ (n ^ (a + 1) - (n - 1)) := by
  classical
  letI : Fintype (LinearMap.ker (constraint (n := n) a)) := Subtype.fintype _
  have h := LinearMap.finrank_range_add_finrank_ker (constraint (n := n) a)
  have hphi : Module.finrank F₂ (PhiSpace (n := n) a) = n ^ (a + 1) := by
    change Module.finrank F₂ (((XC (n := n) a × ZMod n) → F₂)) = n ^ (a + 1)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, card_X, ZMod.card,
      ← Nat.pow_succ]
  rw [finrank_constraint_range, hphi] at h
  have hker :
      Module.finrank F₂ (LinearMap.ker (constraint (n := n) a)) =
        n ^ (a + 1) - (n - 1) := by
    omega
  rw [Module.card_eq_pow_finrank
      (K := F₂) (V := LinearMap.ker (constraint (n := n) a)), hker]
  norm_num

def coeffFromPhi (a b : ℕ) (φ : PhiSpace (n := n) a) : AlphaSpace (n := n) b :=
  fun y => constraint (n := n) a φ (sigma y)

def alphaCoeff (b : ℕ) (c α : AlphaSpace (n := n) b) : F₂ :=
  ∑ y : YC (n := n) b, α y * c y

def alphaSigned (b : ℕ) (c α : AlphaSpace (n := n) b) : ℤ :=
  if alphaCoeff (n := n) b c α = 0 then 1 else -1

def alphaSignedSum (b : ℕ) (c : AlphaSpace (n := n) b) : ℤ :=
  ∑ α : AlphaSpace (n := n) b, alphaSigned (n := n) b c α

noncomputable def deltaCore (a b : ℕ) : ℤ :=
  ∑ φ : PhiSpace (n := n) a, alphaSignedSum (n := n) b (coeffFromPhi (n := n) a b φ)

def toggleAt (b : ℕ) (y0 : YC (n := n) b) (α : AlphaSpace (n := n) b) :
    AlphaSpace (n := n) b :=
  α + Pi.single y0 (1 : F₂)

lemma toggleAt_involutive (b : ℕ) (y0 : YC (n := n) b) (α : AlphaSpace (n := n) b) :
    toggleAt (n := n) b y0 (toggleAt (n := n) b y0 α) = α := by
  ext y
  by_cases h : y = y0
  · subst y
    have h11 : ((1 : F₂) + 1) = 0 := by decide
    simp [toggleAt, add_assoc, h11]
  · simp [toggleAt, h]

lemma bit_cases (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma bit_ne_zero_iff_eq_one (x : F₂) : x ≠ 0 ↔ x = 1 := by
  constructor
  · intro hx
    cases bit_cases x with
    | inl h0 => exact False.elim (hx h0)
    | inr h1 => exact h1
  · intro hx
    subst hx
    decide

lemma alphaCoeff_toggleAt (b : ℕ) (c : AlphaSpace (n := n) b)
    (y0 : YC (n := n) b) (α : AlphaSpace (n := n) b) :
    alphaCoeff (n := n) b c (toggleAt (n := n) b y0 α) =
      alphaCoeff (n := n) b c α + c y0 := by
  unfold alphaCoeff toggleAt
  simp_rw [Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  classical
  rw [Finset.sum_eq_single y0]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

lemma alphaSigned_toggleAt (b : ℕ) (c : AlphaSpace (n := n) b)
    (y0 : YC (n := n) b) (hc : c y0 = 1) (α : AlphaSpace (n := n) b) :
    alphaSigned (n := n) b c (toggleAt (n := n) b y0 α) =
      - alphaSigned (n := n) b c α := by
  have hcoeff :
      alphaCoeff (n := n) b c (toggleAt (n := n) b y0 α) =
        alphaCoeff (n := n) b c α + 1 := by
    simpa [hc] using alphaCoeff_toggleAt (n := n) b c y0 α
  cases bit_cases (alphaCoeff (n := n) b c α) with
  | inl h0 =>
      simp [alphaSigned, h0, hcoeff]
  | inr h1 =>
      have h11 : ((1 : F₂) + 1) = 0 := by decide
      simp [alphaSigned, h1, hcoeff, h11]

lemma exists_one_of_ne_zero_alpha (b : ℕ) (c : AlphaSpace (n := n) b) (hc : c ≠ 0) :
    ∃ y0 : YC (n := n) b, c y0 = 1 := by
  classical
  by_contra h
  apply hc
  funext y
  have hnot1 : c y ≠ 1 := by
    intro hy1
    exact h ⟨y, hy1⟩
  cases bit_cases (c y) with
  | inl h0 =>
      exact h0
  | inr h1 =>
      exact False.elim (hnot1 h1)

lemma alphaSignedSum_zero (b : ℕ) :
    alphaSignedSum (n := n) b (0 : AlphaSpace (n := n) b) =
      (2 : ℤ) ^ (n ^ (b + 1)) := by
  unfold alphaSignedSum alphaSigned alphaCoeff
  simpa [card_alphaSpace]

noncomputable def zeroFiber (b : ℕ) (c : AlphaSpace (n := n) b) :=
  { α : AlphaSpace (n := n) b // alphaCoeff (n := n) b c α = 0 }

noncomputable def oneFiber (b : ℕ) (c : AlphaSpace (n := n) b) :=
  { α : AlphaSpace (n := n) b // alphaCoeff (n := n) b c α = 1 }

noncomputable instance zeroFiberFintype (b : ℕ) (c : AlphaSpace (n := n) b) :
    Fintype (zeroFiber (n := n) b c) := by
  classical
  exact Subtype.fintype _

noncomputable instance oneFiberFintype (b : ℕ) (c : AlphaSpace (n := n) b) :
    Fintype (oneFiber (n := n) b c) := by
  classical
  exact Subtype.fintype _

noncomputable def zeroOneEquiv (b : ℕ) (c : AlphaSpace (n := n) b)
    (y0 : YC (n := n) b) (hy0 : c y0 = 1) :
    zeroFiber (n := n) b c ≃ oneFiber (n := n) b c where
  toFun α := ⟨toggleAt (n := n) b y0 α.1, by
    have h :
        alphaCoeff (n := n) b c (toggleAt (n := n) b y0 α.1) =
          alphaCoeff (n := n) b c α.1 + c y0 :=
      alphaCoeff_toggleAt (n := n) b c y0 α.1
    have h1 :
        alphaCoeff (n := n) b c α.1 + c y0 = 1 := by
      simpa [α.2, hy0]
    exact h.trans h1⟩
  invFun α := ⟨toggleAt (n := n) b y0 α.1, by
    have h :
        alphaCoeff (n := n) b c (toggleAt (n := n) b y0 α.1) =
          alphaCoeff (n := n) b c α.1 + c y0 :=
      alphaCoeff_toggleAt (n := n) b c y0 α.1
    have h0 :
        alphaCoeff (n := n) b c α.1 + c y0 = 0 := by
      have h11 : ((1 : F₂) + 1) = 0 := by decide
      simpa [α.2, hy0] using h11
    exact h.trans h0⟩
  left_inv α := by
    apply Subtype.ext
    exact toggleAt_involutive (n := n) b y0 α.1
  right_inv α := by
    apply Subtype.ext
    exact toggleAt_involutive (n := n) b y0 α.1

lemma alphaSignedSum_nonzero (b : ℕ) (c : AlphaSpace (n := n) b) (hc : c ≠ 0) :
    alphaSignedSum (n := n) b c = 0 := by
  classical
  obtain ⟨y0, hy0⟩ := exists_one_of_ne_zero_alpha (n := n) b c hc
  have hcard :
      Fintype.card (zeroFiber (n := n) b c) = Fintype.card (oneFiber (n := n) b c) := by
    exact Fintype.card_congr (zeroOneEquiv (n := n) b c y0 hy0)
  let p : AlphaSpace (n := n) b → Prop := fun α => alphaCoeff (n := n) b c α = 0
  have hsplit :
      alphaSignedSum (n := n) b c =
        Finset.sum (Finset.univ.filter p) (fun α => alphaSigned (n := n) b c α) +
          Finset.sum (Finset.univ.filter (fun α => ¬ p α))
            (fun α => alphaSigned (n := n) b c α) := by
    unfold alphaSignedSum p
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (AlphaSpace (n := n) b)))
        (p := fun α : AlphaSpace (n := n) b => alphaCoeff (n := n) b c α = 0)
        (f := fun α => alphaSigned (n := n) b c α)).symm
  have hzeroSum :
      Finset.sum (Finset.univ.filter p) (fun α => alphaSigned (n := n) b c α)
        =
      (Fintype.card (zeroFiber (n := n) b c) : ℤ) := by
    unfold p zeroFiber
    calc
      Finset.sum
          (Finset.univ.filter (fun α : AlphaSpace (n := n) b => alphaCoeff (n := n) b c α = 0))
          (fun α => alphaSigned (n := n) b c α)
        =
          Finset.sum
            (Finset.univ.filter
              (fun α : AlphaSpace (n := n) b => alphaCoeff (n := n) b c α = 0))
            (fun _ => (1 : ℤ)) := by
              refine Finset.sum_congr rfl ?_
              intro α hα
              have hα0 : alphaCoeff (n := n) b c α = 0 := by
                exact (Finset.mem_filter.mp hα).2
              simp [alphaSigned, hα0]
      _ = (Fintype.card (zeroFiber (n := n) b c) : ℤ) := by
        simpa using
          congrArg (fun t : ℕ => (t : ℤ))
            ((Fintype.card_subtype
              (fun α : AlphaSpace (n := n) b => alphaCoeff (n := n) b c α = 0)).symm)
  have hfilter1 :
      (Finset.univ.filter fun α : AlphaSpace (n := n) b => ¬ p α)
        =
      (Finset.univ.filter fun α : AlphaSpace (n := n) b =>
        alphaCoeff (n := n) b c α = 1) := by
    ext α
    unfold p
    simp [bit_ne_zero_iff_eq_one]
  have honeSum :
      Finset.sum (Finset.univ.filter (fun α => ¬ p α))
        (fun α => alphaSigned (n := n) b c α)
        =
      - (Fintype.card (oneFiber (n := n) b c) : ℤ) := by
    rw [hfilter1]
    unfold oneFiber
    calc
      Finset.sum
          (Finset.univ.filter
            (fun α : AlphaSpace (n := n) b => alphaCoeff (n := n) b c α = 1))
          (fun α => alphaSigned (n := n) b c α)
        =
          Finset.sum
            (Finset.univ.filter
              (fun α : AlphaSpace (n := n) b => alphaCoeff (n := n) b c α = 1))
            (fun _ => (-1 : ℤ)) := by
              refine Finset.sum_congr rfl ?_
              intro α hα
              have hα1 : alphaCoeff (n := n) b c α = 1 := by
                exact (Finset.mem_filter.mp hα).2
              simp [alphaSigned, hα1]
      _ = - (Fintype.card (oneFiber (n := n) b c) : ℤ) := by
        simpa using
          congrArg (fun t : ℕ => -(t : ℤ))
            ((Fintype.card_subtype
              (fun α : AlphaSpace (n := n) b => alphaCoeff (n := n) b c α = 1)).symm)
  rw [hsplit, hzeroSum, honeSum, hcard]
  ring

theorem alphaSignedSum_formula (b : ℕ) (c : AlphaSpace (n := n) b) :
    alphaSignedSum (n := n) b c =
      if c = 0 then (2 : ℤ) ^ (n ^ (b + 1)) else 0 := by
  by_cases hc : c = 0
  · rw [if_pos hc]
    subst hc
    exact alphaSignedSum_zero (n := n) b
  · rw [if_neg hc]
    exact alphaSignedSum_nonzero (n := n) b c hc

lemma coeffFromPhi_eq_zero_iff (a b : ℕ) (φ : PhiSpace (n := n) a) :
    coeffFromPhi (n := n) a b φ = 0 ↔ constraint (n := n) a φ = 0 := by
  constructor
  · intro h
    ext s
    have hs := congrArg (fun f : AlphaSpace (n := n) b => f (composeY (n := n) b 0 s)) h
    simpa [coeffFromPhi, sigma_composeY] using hs
  · intro h
    ext y
    simp [coeffFromPhi, h]

theorem deltaCore_formula (a b : ℕ) :
    deltaCore (n := n) a b =
      (2 : ℤ) ^ (n ^ (a + 1) + n ^ (b + 1) - (n - 1)) := by
  classical
  let K : ℤ := (2 : ℤ) ^ (n ^ (b + 1))
  unfold deltaCore
  simp [alphaSignedSum_formula, coeffFromPhi_eq_zero_iff]
  have hsum :
      (∑ φ : PhiSpace (n := n) a,
          if constraint (n := n) a φ = 0 then K else 0)
        =
      (Fintype.card { φ : PhiSpace (n := n) a // constraint (n := n) a φ = 0 } : ℤ) * K := by
    rw [← Finset.sum_filter]
    simpa [Fintype.card_subtype, K]
  have hcardsub :
      Fintype.card { φ : PhiSpace (n := n) a // constraint (n := n) a φ = 0 }
        =
      Fintype.card (LinearMap.ker (constraint (n := n) a)) := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun x => ⟨x.1, show constraint (n := n) a x.1 = 0 from x.2⟩
        invFun := fun x => ⟨x.1, show constraint (n := n) a x.1 = 0 from x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  have hkerInt :
      (Fintype.card { φ : PhiSpace (n := n) a // constraint (n := n) a φ = 0 } : ℤ) =
        (2 : ℤ) ^ (n ^ (a + 1) - (n - 1)) := by
    have hkerNat :
        Fintype.card { φ : PhiSpace (n := n) a // constraint (n := n) a φ = 0 } =
          2 ^ (n ^ (a + 1) - (n - 1)) := by
      rw [hcardsub]
      exact card_constraint_ker (n := n) a
    norm_num [hkerNat]
  rw [hsum, hkerInt]
  have hpow :
      (2 : ℤ) ^ (n ^ (a + 1) - (n - 1)) * (2 : ℤ) ^ (n ^ (b + 1)) =
        (2 : ℤ) ^ ((n ^ (a + 1) - (n - 1)) + n ^ (b + 1)) := by
    simpa using
      (Int.pow_add (2 : ℤ) (n ^ (a + 1) - (n - 1)) (n ^ (b + 1))).symm
  have hexp :
      (n ^ (a + 1) - (n - 1)) + n ^ (b + 1) =
        n ^ (a + 1) + n ^ (b + 1) - (n - 1) := by
    have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
    have hm : n ≤ n ^ (a + 1) := by
      simpa using le_self_pow hn (Nat.succ_ne_zero a)
    have hle : n - 1 ≤ n ^ (a + 1) := by
      exact le_trans (Nat.sub_le _ _) hm
    omega
  simp [K, hpow, hexp]

end Core

theorem card_validAssignments {a b n : ℕ} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    Fintype.card (ValidAssignments a b n) = 2 ^ (n ^ b + n ^ a) := by
  obtain ⟨a0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨b0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  exact card_validAssignments_core (n := n) a0 b0

theorem card_constraint_kernel_user {a n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (LinearMap.ker (constraint (n := n) (a - 1))) =
      2 ^ (n ^ a - (n - 1)) := by
  obtain ⟨a0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  exact card_constraint_ker (n := n) a0

theorem signed_imbalance_user {a b n : ℕ} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    deltaCore (n := n) (a - 1) (b - 1) =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  obtain ⟨a0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨b0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  simpa using deltaCore_formula (n := n) a0 b0

end CombinatorialAssignments
end FormalMathLab
