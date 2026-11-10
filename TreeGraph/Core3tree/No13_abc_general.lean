import Mathlib

open scoped BigOperators

namespace No13Migration

abbrev F₂ := ZMod 2

lemma F2_add_self (x : F₂) : x + x = 0 := by
  fin_cases x <;> decide

abbrev T4 (n : ℕ) := Fin 4 → ZMod n
abbrev T5 (n : ℕ) := Fin 5 → ZMod n

abbrev AField (n : ℕ) := T4 n → F₂
abbrev BField (n : ℕ) := T4 n → F₂
abbrev CField (n : ℕ) := T4 n → F₂

structure No13Assignment (n : ℕ) where
  alpha : T5 n → F₂
  beta : T5 n → F₂
  gamma : T5 n → F₂
  delta : T5 n → F₂
  eta : T5 n → F₂

@[ext] theorem No13Assignment.ext {n : ℕ} {S T : No13Assignment n}
    (hα : S.alpha = T.alpha) (hβ : S.beta = T.beta) (hγ : S.gamma = T.gamma)
    (hδ : S.delta = T.delta) (hη : S.eta = T.eta) : S = T := by
  cases S
  cases T
  simp_all

structure No13Valid {n : ℕ} (S : No13Assignment n) : Prop where
  alpha_e1 : ∀ x, S.alpha (x + Pi.single 0 1) = S.alpha x
  gamma_beta_e2 : ∀ x, S.gamma x = S.beta (x + Pi.single 1 1)
  gamma_beta_e3 : ∀ x, S.gamma x = S.beta (x + Pi.single 2 1)
  eta_delta_e4 : ∀ x, S.eta x = S.delta (x + Pi.single 3 1)
  eta_delta_e5 : ∀ x, S.eta x = S.delta (x + Pi.single 4 1)

abbrev No13ValidAssignments (n : ℕ) := { S : No13Assignment n // No13Valid S }

structure No13NormalForm (n : ℕ) where
  A : AField n
  B : BField n
  C : CField n

def assignmentEquivProd (n : ℕ) :
    No13Assignment n ≃
      (T5 n → F₂) × ((T5 n → F₂) × ((T5 n → F₂) × ((T5 n → F₂) × (T5 n → F₂)))) where
  toFun S := ⟨S.alpha, ⟨S.beta, S.gamma, S.delta, S.eta⟩⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def vec4 {n : ℕ} (a b c d : ZMod n) : T4 n
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d

def vec5 {n : ℕ} (a b c d e : ZMod n) : T5 n
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d
  | ⟨4, _⟩ => e

@[simp] lemma vec4_zero {n : ℕ} (a b c d : ZMod n) : vec4 a b c d 0 = a := rfl
@[simp] lemma vec4_one {n : ℕ} (a b c d : ZMod n) : vec4 a b c d 1 = b := rfl
@[simp] lemma vec4_two {n : ℕ} (a b c d : ZMod n) : vec4 a b c d 2 = c := rfl
@[simp] lemma vec4_three {n : ℕ} (a b c d : ZMod n) : vec4 a b c d 3 = d := rfl
@[simp] lemma vec4_eta {n : ℕ} (u : T4 n) : vec4 (u 0) (u 1) (u 2) (u 3) = u := by
  ext i <;> fin_cases i <;> rfl

@[simp] lemma vec5_zero {n : ℕ} (a b c d e : ZMod n) : vec5 a b c d e 0 = a := rfl
@[simp] lemma vec5_one {n : ℕ} (a b c d e : ZMod n) : vec5 a b c d e 1 = b := rfl
@[simp] lemma vec5_two {n : ℕ} (a b c d e : ZMod n) : vec5 a b c d e 2 = c := rfl
@[simp] lemma vec5_three {n : ℕ} (a b c d e : ZMod n) : vec5 a b c d e 3 = d := rfl
@[simp] lemma vec5_four {n : ℕ} (a b c d e : ZMod n) : vec5 a b c d e 4 = e := rfl

@[simp] lemma vec5_eta {n : ℕ} (x : T5 n) :
    vec5 (x 0) (x 1) (x 2) (x 3) (x 4) = x := by
  ext i <;> fin_cases i <;> simp [vec5]

def projA {n : ℕ} (x : T5 n) : T4 n :=
  vec4 (x 1) (x 2) (x 3) (x 4)

def projB {n : ℕ} (x : T5 n) : T4 n :=
  vec4 (x 0) (x 1 + x 2) (x 3) (x 4)

def projC {n : ℕ} (x : T5 n) : T4 n :=
  vec4 (x 0) (x 1) (x 2) (x 3 + x 4)

@[simp] lemma projA_vec5 {n : ℕ} (a b c d e : ZMod n) :
    projA (vec5 a b c d e) = vec4 b c d e := rfl

@[simp] lemma projB_vec5 {n : ℕ} (a b c d e : ZMod n) :
    projB (vec5 a b c d e) = vec4 a (b + c) d e := rfl

@[simp] lemma projC_vec5 {n : ℕ} (a b c d e : ZMod n) :
    projC (vec5 a b c d e) = vec4 a b c (d + e) := rfl

@[simp] lemma projB_add_e2 {n : ℕ} (x : T5 n) :
    projB (x + Pi.single 1 1) = vec4 (x 0) (x 1 + x 2 + 1) (x 3) (x 4) := by
  ext i <;> fin_cases i <;> simp [projB, vec4, add_assoc, add_left_comm, add_comm]

@[simp] lemma projB_add_e3 {n : ℕ} (x : T5 n) :
    projB (x + Pi.single 2 1) = vec4 (x 0) (x 1 + x 2 + 1) (x 3) (x 4) := by
  ext i <;> fin_cases i <;> simp [projB, vec4, add_assoc, add_left_comm, add_comm]

@[simp] lemma projC_add_e4 {n : ℕ} (x : T5 n) :
    projC (x + Pi.single 3 1) = vec4 (x 0) (x 1) (x 2) (x 3 + x 4 + 1) := by
  ext i <;> fin_cases i <;> simp [projC, vec4, add_assoc, add_left_comm, add_comm]

@[simp] lemma projC_add_e5 {n : ℕ} (x : T5 n) :
    projC (x + Pi.single 4 1) = vec4 (x 0) (x 1) (x 2) (x 3 + x 4 + 1) := by
  ext i <;> fin_cases i <;> simp [projC, vec4, add_assoc, add_left_comm, add_comm]

lemma vec5_add_e1 {n : ℕ} (a b c d e : ZMod n) :
    vec5 a b c d e + Pi.single 0 1 = vec5 (a + 1) b c d e := by
  ext i <;> fin_cases i <;> simp [vec5]

lemma vec5_add_e2_slide23 {n : ℕ} (a b c d e t : ZMod n) :
    vec5 a (b + t) (c - (t + 1)) d e + Pi.single 1 1 =
      vec5 a (b + t + 1) (c - (t + 1)) d e := by
  ext i <;> fin_cases i <;> simp [vec5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma vec5_add_e3_slide23 {n : ℕ} (a b c d e t : ZMod n) :
    vec5 a (b + t) (c - (t + 1)) d e + Pi.single 2 1 =
      vec5 a (b + t) (c - t) d e := by
  ext i <;> fin_cases i <;> simp [vec5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma vec5_add_e4_slide45 {n : ℕ} (a b c d e t : ZMod n) :
    vec5 a b c (d + t) (e - (t + 1)) + Pi.single 3 1 =
      vec5 a b c (d + t + 1) (e - (t + 1)) := by
  ext i <;> fin_cases i <;> simp [vec5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma vec5_add_e5_slide45 {n : ℕ} (a b c d e t : ZMod n) :
    vec5 a b c (d + t) (e - (t + 1)) + Pi.single 4 1 =
      vec5 a b c (d + t) (e - t) := by
  ext i <;> fin_cases i <;> simp [vec5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma zmod_step_const {n : ℕ} [NeZero n] {α : Type*} (g : ZMod n → α)
    (h : ∀ s, g (s + 1) = g s) :
    ∀ s, g s = g 0 := by
  intro s
  have hNat : ∀ m : ℕ, g (m : ZMod n) = g 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
        calc
          g ((m + 1 : ℕ) : ZMod n) = g ((m : ZMod n) + 1) := by simp
          _ = g (m : ZMod n) := h _
          _ = g 0 := hm
  simpa [ZMod.natCast_val] using hNat s.val

def toNo13Assignment {n : ℕ} (nf : No13NormalForm n) : No13Assignment n where
  alpha x := nf.A (projA x)
  beta x := nf.B (projB x)
  gamma x := nf.B (vec4 (x 0) (x 1 + x 2 + 1) (x 3) (x 4))
  delta x := nf.C (projC x)
  eta x := nf.C (vec4 (x 0) (x 1) (x 2) (x 3 + x 4 + 1))

lemma valid_toNo13Assignment {n : ℕ} (nf : No13NormalForm n) :
    No13Valid (toNo13Assignment nf) := by
  constructor
  · intro x
    simp [toNo13Assignment, projA, vec4]
  · intro x
    simp [toNo13Assignment]
  · intro x
    simp [toNo13Assignment]
  · intro x
    simp [toNo13Assignment]
  · intro x
    simp [toNo13Assignment]

def alphaCanonical {n : ℕ} (u : T4 n) : T5 n :=
  vec5 0 (u 0) (u 1) (u 2) (u 3)

def betaCanonical {n : ℕ} (u : T4 n) : T5 n :=
  vec5 (u 0) 0 (u 1) (u 2) (u 3)

def deltaCanonical {n : ℕ} (u : T4 n) : T5 n :=
  vec5 (u 0) (u 1) (u 2) 0 (u 3)

@[simp] lemma projA_alphaCanonical {n : ℕ} (u : T4 n) : projA (alphaCanonical u) = u := by
  ext i <;> fin_cases i <;> simp [alphaCanonical, projA, vec4, vec5]

@[simp] lemma projB_betaCanonical {n : ℕ} (u : T4 n) : projB (betaCanonical u) = u := by
  ext i <;> fin_cases i <;> simp [betaCanonical, projB, vec4, vec5]

@[simp] lemma projC_deltaCanonical {n : ℕ} (u : T4 n) : projC (deltaCanonical u) = u := by
  ext i <;> fin_cases i <;> simp [deltaCanonical, projC, vec4, vec5]

lemma alpha_depends_only_projA {n : ℕ} [NeZero n]
    (S : No13Assignment n) (hS : No13Valid S) (x : T5 n) :
    S.alpha x = S.alpha (alphaCanonical (projA x)) := by
  let g : ZMod n → F₂ := fun t => S.alpha (vec5 (x 0 + t) (x 1) (x 2) (x 3) (x 4))
  have hg : ∀ t, g (t + 1) = g t := by
    intro t
    have := hS.alpha_e1 (vec5 (x 0 + t) (x 1) (x 2) (x 3) (x 4))
    simpa [g, vec5_add_e1, add_assoc] using this
  have hconst := zmod_step_const (n := n) g hg (-x 0)
  dsimp [g] at hconst
  calc
    S.alpha x = g 0 := by simpa [g] using congrArg S.alpha (vec5_eta x).symm
    _ = g (-x 0) := hconst.symm
    _ = S.alpha (alphaCanonical (projA x)) := by
      simp [g, alphaCanonical, projA, vec4, vec5, add_assoc]

lemma beta_depends_only_projB {n : ℕ} [NeZero n]
    (S : No13Assignment n) (hS : No13Valid S) (x : T5 n) :
    S.beta x = S.beta (betaCanonical (projB x)) := by
  let g : ZMod n → F₂ := fun t => S.beta (vec5 (x 0) (x 1 + t) (x 2 - t) (x 3) (x 4))
  have hg : ∀ t, g (t + 1) = g t := by
    intro t
    have h23 := hS.gamma_beta_e2 (vec5 (x 0) (x 1 + t) (x 2 - (t + 1)) (x 3) (x 4))
    have h22 := hS.gamma_beta_e3 (vec5 (x 0) (x 1 + t) (x 2 - (t + 1)) (x 3) (x 4))
    calc
      g (t + 1)
          = S.gamma (vec5 (x 0) (x 1 + t) (x 2 - (t + 1)) (x 3) (x 4)) := by
              rw [h23]
              simpa [g, add_assoc] using
                congrArg S.beta (vec5_add_e2_slide23 (x 0) (x 1) (x 2) (x 3) (x 4) t).symm
      _ = g t := by
              rw [h22]
              simpa [g, add_assoc] using
                congrArg S.beta (vec5_add_e3_slide23 (x 0) (x 1) (x 2) (x 3) (x 4) t)
  have hconst := zmod_step_const (n := n) g hg (-x 1)
  dsimp [g] at hconst
  calc
    S.beta x = g 0 := by simpa [g] using congrArg S.beta (vec5_eta x).symm
    _ = g (-x 1) := hconst.symm
    _ = S.beta (betaCanonical (projB x)) := by
      simp [g, betaCanonical, projB, vec4, vec5, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]

lemma delta_depends_only_projC {n : ℕ} [NeZero n]
    (S : No13Assignment n) (hS : No13Valid S) (x : T5 n) :
    S.delta x = S.delta (deltaCanonical (projC x)) := by
  let g : ZMod n → F₂ := fun t => S.delta (vec5 (x 0) (x 1) (x 2) (x 3 + t) (x 4 - t))
  have hg : ∀ t, g (t + 1) = g t := by
    intro t
    have h45 := hS.eta_delta_e4 (vec5 (x 0) (x 1) (x 2) (x 3 + t) (x 4 - (t + 1)))
    have h44 := hS.eta_delta_e5 (vec5 (x 0) (x 1) (x 2) (x 3 + t) (x 4 - (t + 1)))
    calc
      g (t + 1)
          = S.eta (vec5 (x 0) (x 1) (x 2) (x 3 + t) (x 4 - (t + 1))) := by
              rw [h45]
              simpa [g, add_assoc] using
                congrArg S.delta (vec5_add_e4_slide45 (x 0) (x 1) (x 2) (x 3) (x 4) t).symm
      _ = g t := by
              rw [h44]
              simpa [g, add_assoc] using
                congrArg S.delta (vec5_add_e5_slide45 (x 0) (x 1) (x 2) (x 3) (x 4) t)
  have hconst := zmod_step_const (n := n) g hg (-x 3)
  dsimp [g] at hconst
  calc
    S.delta x = g 0 := by simpa [g] using congrArg S.delta (vec5_eta x).symm
    _ = g (-x 3) := hconst.symm
    _ = S.delta (deltaCanonical (projC x)) := by
      simp [g, deltaCanonical, projC, vec4, vec5, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]

noncomputable def toNo13NormalForm {n : ℕ} (S : No13Assignment n) (_hS : No13Valid S) :
    No13NormalForm n where
  A u := S.alpha (alphaCanonical u)
  B u := S.beta (betaCanonical u)
  C u := S.delta (deltaCanonical u)

lemma toNo13NormalForm_toNo13Assignment {n : ℕ} (nf : No13NormalForm n) :
    toNo13NormalForm (toNo13Assignment nf) (valid_toNo13Assignment nf) = nf := by
  cases nf
  simp [toNo13NormalForm, toNo13Assignment]

lemma toNo13Assignment_toNo13NormalForm {n : ℕ} [NeZero n]
    (S : No13Assignment n) (hS : No13Valid S) :
    toNo13Assignment (toNo13NormalForm S hS) = S := by
  cases S with
  | mk alpha beta gamma delta eta =>
      apply No13Assignment.ext
      · funext x
        simpa [toNo13Assignment, toNo13NormalForm] using
          (alpha_depends_only_projA ⟨alpha, beta, gamma, delta, eta⟩ hS x).symm
      · funext x
        simpa [toNo13Assignment, toNo13NormalForm] using
          (beta_depends_only_projB ⟨alpha, beta, gamma, delta, eta⟩ hS x).symm
      · funext x
        calc
          (toNo13Assignment (toNo13NormalForm ⟨alpha, beta, gamma, delta, eta⟩ hS)).gamma x
              = beta (betaCanonical (projB (x + Pi.single 1 1))) := by
                  simp [toNo13Assignment, toNo13NormalForm]
          _ = beta (x + Pi.single 1 1) := by
                symm
                exact beta_depends_only_projB ⟨alpha, beta, gamma, delta, eta⟩ hS (x + Pi.single 1 1)
          _ = gamma x := (hS.gamma_beta_e2 x).symm
      · funext x
        simpa [toNo13Assignment, toNo13NormalForm] using
          (delta_depends_only_projC ⟨alpha, beta, gamma, delta, eta⟩ hS x).symm
      · funext x
        calc
          (toNo13Assignment (toNo13NormalForm ⟨alpha, beta, gamma, delta, eta⟩ hS)).eta x
              = delta (deltaCanonical (projC (x + Pi.single 3 1))) := by
                  simp [toNo13Assignment, toNo13NormalForm]
          _ = delta (x + Pi.single 3 1) := by
                symm
                exact delta_depends_only_projC ⟨alpha, beta, gamma, delta, eta⟩ hS (x + Pi.single 3 1)
          _ = eta x := (hS.eta_delta_e4 x).symm

noncomputable def no13NormalFormEquiv {n : ℕ} [NeZero n] :
    No13ValidAssignments n ≃ No13NormalForm n where
  toFun S := toNo13NormalForm S.1 S.2
  invFun nf := ⟨toNo13Assignment nf, valid_toNo13Assignment nf⟩
  left_inv S := by
    apply Subtype.ext
    exact toNo13Assignment_toNo13NormalForm S.1 S.2
  right_inv nf := toNo13NormalForm_toNo13Assignment nf

def normalFormEquivProd (n : ℕ) :
    No13NormalForm n ≃ AField n × (BField n × CField n) where
  toFun nf := ⟨nf.A, ⟨nf.B, nf.C⟩⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance t4Fintype (n : ℕ) [NeZero n] : Fintype (T4 n) := inferInstance
noncomputable instance t5Fintype (n : ℕ) [NeZero n] : Fintype (T5 n) := inferInstance
noncomputable instance aFieldFintype (n : ℕ) [NeZero n] : Fintype (AField n) := inferInstance
noncomputable instance bFieldFintype (n : ℕ) [NeZero n] : Fintype (BField n) := inferInstance
noncomputable instance cFieldFintype (n : ℕ) [NeZero n] : Fintype (CField n) := inferInstance
noncomputable instance no13AssignmentFintype (n : ℕ) [NeZero n] : Fintype (No13Assignment n) :=
  Fintype.ofEquiv _ (assignmentEquivProd n).symm
noncomputable instance no13NormalFormFintype (n : ℕ) [NeZero n] : Fintype (No13NormalForm n) :=
  Fintype.ofEquiv _ (normalFormEquivProd n).symm
noncomputable instance no13ValidAssignmentsFintype (n : ℕ) [NeZero n] :
    Fintype (No13ValidAssignments n) := by
  classical
  exact Subtype.fintype _

lemma card_T4 (n : ℕ) [NeZero n] : Fintype.card (T4 n) = n ^ 4 := by
  simpa [T4, ZMod.card] using (Fintype.card_fun (α := Fin 4) (β := ZMod n))

lemma card_AField (n : ℕ) [NeZero n] : Fintype.card (AField n) = 2 ^ (n ^ 4) := by
  rw [Fintype.card_fun, card_T4]
  simp [F₂]

lemma card_BField (n : ℕ) [NeZero n] : Fintype.card (BField n) = 2 ^ (n ^ 4) := by
  rw [Fintype.card_fun, card_T4]
  simp [F₂]

lemma card_CField (n : ℕ) [NeZero n] : Fintype.card (CField n) = 2 ^ (n ^ 4) := by
  rw [Fintype.card_fun, card_T4]
  simp [F₂]

theorem card_validAssignments_no13 {n : ℕ} [NeZero n] :
    Fintype.card (No13ValidAssignments n) = 2 ^ (3 * n ^ 4) := by
  rw [Fintype.card_congr (no13NormalFormEquiv (n := n))]
  rw [Fintype.card_congr (normalFormEquivProd n), Fintype.card_prod, Fintype.card_prod]
  have h : n ^ 4 + (n ^ 4 + n ^ 4) = 3 * n ^ 4 := by ring
  have hcards :
      Fintype.card (AField n) * (Fintype.card (BField n) * Fintype.card (CField n)) =
        2 ^ (n ^ 4) * (2 ^ (n ^ 4) * 2 ^ (n ^ 4)) := by
    simp [card_AField, card_BField, card_CField]
  rw [hcards]
  calc
    2 ^ (n ^ 4) * (2 ^ (n ^ 4) * 2 ^ (n ^ 4))
      = 2 ^ (n ^ 4) * 2 ^ (n ^ 4 + n ^ 4) := by rw [← pow_add]
    _ = 2 ^ (n ^ 4 + (n ^ 4 + n ^ 4)) := by rw [← pow_add]
    _ = 2 ^ (3 * n ^ 4) := by rw [h]

def bitSign (b : F₂) : ℤ := if b = 0 then 1 else -1

def localPhaseBit {n : ℕ} (S : No13Assignment n) (x : T5 n) : F₂ :=
  S.alpha x * (S.beta x + S.gamma x + S.delta x + S.eta x)

noncomputable def W {n : ℕ} [NeZero n] (S : No13Assignment n) : ℤ :=
  ∏ x : T5 n, bitSign (localPhaseBit S x)

noncomputable def basisA {n : ℕ} [NeZero n] : AField n := Pi.single 0 (1 : F₂)

lemma basisA_ne_zero {n : ℕ} [NeZero n] : (basisA : AField n) ≠ 0 := by
  intro h
  have := congrArg (fun f : AField n => f 0) h
  simp [basisA] at this

noncomputable def coeffFromBC {n : ℕ} [NeZero n] (B : BField n) (C : CField n) : AField n :=
  fun u =>
    ∑ x1 : ZMod n,
      (B (vec4 x1 (u 0 + u 1) (u 2) (u 3)) +
        B (vec4 x1 (u 0 + u 1 + 1) (u 2) (u 3)) +
        C (vec4 x1 (u 0) (u 1) (u 2 + u 3)) +
        C (vec4 x1 (u 0) (u 1) (u 2 + u 3 + 1)))

noncomputable def bSlice {n : ℕ} [NeZero n] (B : BField n) (y : ZMod n) : F₂ :=
  ∑ x1 : ZMod n, ∑ u2 : ZMod n, ∑ u3 : ZMod n,
    (B (vec4 x1 y u2 u3) + B (vec4 x1 (y + 1) u2 u3))

noncomputable def cSlice {n : ℕ} [NeZero n] (C : CField n) (z : ZMod n) : F₂ :=
  ∑ x1 : ZMod n, ∑ u0 : ZMod n, ∑ u1 : ZMod n,
    (C (vec4 x1 u0 u1 z) + C (vec4 x1 u0 u1 (z + 1)))

noncomputable def bKernel {n : ℕ} [NeZero n]
    (B : BField n) (y u2 u3 : ZMod n) : F₂ :=
  ∑ x1 : ZMod n, (B (vec4 x1 y u2 u3) + B (vec4 x1 (y + 1) u2 u3))

noncomputable def cKernel {n : ℕ} [NeZero n]
    (C : CField n) (z u0 u1 : ZMod n) : F₂ :=
  ∑ x1 : ZMod n, (C (vec4 x1 u0 u1 z) + C (vec4 x1 u0 u1 (z + 1)))

lemma bKernel_add {n : ℕ} [NeZero n] (B1 B2 : BField n) (y u2 u3 : ZMod n) :
    bKernel (B1 + B2) y u2 u3 = bKernel B1 y u2 u3 + bKernel B2 y u2 u3 := by
  unfold bKernel
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x1 _
  simp [add_assoc, add_left_comm, add_comm]

lemma cKernel_add {n : ℕ} [NeZero n] (C1 C2 : CField n) (z u0 u1 : ZMod n) :
    cKernel (C1 + C2) z u0 u1 = cKernel C1 z u0 u1 + cKernel C2 z u0 u1 := by
  unfold cKernel
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x1 _
  simp [add_assoc, add_left_comm, add_comm]

lemma bKernel_zero {n : ℕ} [NeZero n] (y u2 u3 : ZMod n) : bKernel (0 : BField n) y u2 u3 = 0 := by
  simp [bKernel]

lemma cKernel_zero {n : ℕ} [NeZero n] (z u0 u1 : ZMod n) : cKernel (0 : CField n) z u0 u1 = 0 := by
  simp [cKernel]

lemma F2_add_eq_zero_iff_eq (a b : F₂) : a + b = 0 ↔ a = b := by
  simpa using (add_eq_zero_iff_eq_neg : a + b = 0 ↔ a = -b)

lemma coeffFromBC_eq_kernels {n : ℕ} [NeZero n] (B : BField n) (C : CField n) (u : T4 n) :
    coeffFromBC B C u =
      bKernel B (u 0 + u 1) (u 2) (u 3) + cKernel C (u 2 + u 3) (u 0) (u 1) := by
  unfold coeffFromBC bKernel cKernel
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x1 hx
  simp [add_assoc, add_left_comm, add_comm]

lemma coeffFromBC_eq_zero_iff_kernels_eq {n : ℕ} [NeZero n] (B : BField n) (C : CField n) :
    coeffFromBC B C = 0 ↔
      ∀ u : T4 n,
        bKernel B (u 0 + u 1) (u 2) (u 3) = cKernel C (u 2 + u 3) (u 0) (u 1) := by
  constructor
  · intro h u
    have hu : coeffFromBC B C u = 0 := by simpa [h]
    have hu' : bKernel B (u 0 + u 1) (u 2) (u 3) + cKernel C (u 2 + u 3) (u 0) (u 1) = 0 := by
      simpa [coeffFromBC_eq_kernels] using hu
    exact (F2_add_eq_zero_iff_eq _ _).1 hu'
  · intro h
    ext u
    have hu := h u
    have hu' : bKernel B (u 0 + u 1) (u 2) (u 3) + cKernel C (u 2 + u 3) (u 0) (u 1) = 0 := by
      exact (F2_add_eq_zero_iff_eq _ _).2 hu
    simpa [coeffFromBC_eq_kernels] using hu'

set_option maxHeartbeats 800000 in
-- `rw [← Finset.sum_add_distrib]` on `coeffFromBC` exceeds default heartbeats.
lemma coeffFromBC_add_add {n : ℕ} [NeZero n] (B1 B2 : BField n) (C1 C2 : CField n) :
    coeffFromBC (B1 + B2) (C1 + C2) = coeffFromBC B1 C1 + coeffFromBC B2 C2 := by
  funext u
  unfold coeffFromBC
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x1 hx
  simp [add_assoc, add_left_comm, add_comm]

lemma coeffFromBC_zero_B_zero_C_eq_zero {n : ℕ} [NeZero n] :
    coeffFromBC (0 : BField n) (0 : CField n) = 0 := by
  funext u
  simp [coeffFromBC]

lemma ZMod_two_eq_one_of_ne_zero {r : F₂} (hr : r ≠ 0) : r = 1 := by
  fin_cases r
  · exact (hr rfl).elim
  · rfl

lemma bKernel_smul {n : ℕ} [NeZero n] (r : F₂) (B : BField n) (y u2 u3 : ZMod n) :
    bKernel (r • B) y u2 u3 = r • bKernel B y u2 u3 := by
  rcases eq_or_ne r 0 with hr0 | hr1
  · subst hr0
    simp [Pi.smul_apply, bKernel_zero]
  · rw [ZMod_two_eq_one_of_ne_zero hr1]
    simp [one_smul]

lemma cKernel_smul {n : ℕ} [NeZero n] (r : F₂) (C : CField n) (z u0 u1 : ZMod n) :
    cKernel (r • C) z u0 u1 = r • cKernel C z u0 u1 := by
  rcases eq_or_ne r 0 with hr0 | hr1
  · subst hr0
    simp [Pi.smul_apply, cKernel_zero]
  · rw [ZMod_two_eq_one_of_ne_zero hr1]
    simp [one_smul]

/-! **Kernel-profile codomains.** Three-index `bKernel`/`cKernel` values packaged as dependent functions;
`bProfileLinearMap`/`cProfileLinearMap` are the `F₂`-linear maps sending `B`/`C` to their profiles.
**Admissible** profiles are the kernel of the “slice-sum” constraint map
`(y,u2,u3) ↦ ∑_y f y u2 u3` (and the `c`-analogue); that map is surjective, hence
`finrank admissible = n^3 - n^2`.  Range equality
`range bProfileLinearMap = BProfileAdmSubmodule` (and the `C` analogue) is proved via
`Bfield_of_admissibleProfile` / `Cfield_of_admissibleProfile`.  Rank–nullity on `BField n →ₗ bProfile`
gives `finrank ker(bProfileLinearMap) = n^4 - (n^3 - n^2)` (equivalently `n^4 - n^3 + n^2` for `n ≥ 1`), hence
`|ker(bProfileLinearMap)| = 2^{n^4 - (n^3 - n^2)}` over `F₂` (see `finrank_ker_bProfileLinearMap`). -/

abbrev BProfileRaw (n : ℕ) := ZMod n → ZMod n → ZMod n → F₂

abbrev CProfileRaw (n : ℕ) := ZMod n → ZMod n → ZMod n → F₂

abbrev BProfileSumCodomain (n : ℕ) := ZMod n → ZMod n → F₂

abbrev CProfileSumCodomain (n : ℕ) := ZMod n → ZMod n → F₂

/-- `BProfileRaw ≃ (ZMod n)³ → F₂` (uncurry the three indices). -/
noncomputable def BProfileRaw_equiv_triple (n : ℕ) [NeZero n] :
    BProfileRaw n ≃ₗ[F₂] (ZMod n × ZMod n × ZMod n → F₂) where
  toFun f := fun p => f p.1 p.2.1 p.2.2
  invFun g := fun a b c => g (a, b, c)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `CProfileRaw ≃ (ZMod n)³ → F₂`. -/
noncomputable def CProfileRaw_equiv_triple (n : ℕ) [NeZero n] :
    CProfileRaw n ≃ₗ[F₂] (ZMod n × ZMod n × ZMod n → F₂) :=
  BProfileRaw_equiv_triple n

lemma finrank_BProfileRaw (n : ℕ) [NeZero n] :
    Module.finrank F₂ (BProfileRaw n) = n ^ 3 := by
  rw [(BProfileRaw_equiv_triple (n := n)).finrank_eq, Module.finrank_fintype_fun_eq_card]
  rw [Fintype.card_prod (α := ZMod n), Fintype.card_prod (α := ZMod n) (β := ZMod n)]
  simp [ZMod.card]
  ring

lemma finrank_CProfileRaw (n : ℕ) [NeZero n] :
    Module.finrank F₂ (CProfileRaw n) = n ^ 3 :=
  finrank_BProfileRaw n

/-- Curried `(u2,u3) ↦ …` as a function on `ZMod n × ZMod n`. -/
noncomputable def BProfileSumCodomain_equiv_pair (n : ℕ) [NeZero n] :
    BProfileSumCodomain n ≃ₗ[F₂] (ZMod n × ZMod n → F₂) where
  toFun f := fun p => f p.1 p.2
  invFun g := fun a b => g (a, b)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def CProfileSumCodomain_equiv_pair (n : ℕ) [NeZero n] :
    CProfileSumCodomain n ≃ₗ[F₂] (ZMod n × ZMod n → F₂) :=
  BProfileSumCodomain_equiv_pair n

lemma finrank_BProfileSumCodomain (n : ℕ) [NeZero n] :
    Module.finrank F₂ (BProfileSumCodomain n) = n ^ 2 := by
  rw [(BProfileSumCodomain_equiv_pair (n := n)).finrank_eq, Module.finrank_fintype_fun_eq_card]
  rw [Fintype.card_prod (α := ZMod n) (β := ZMod n)]
  simp [ZMod.card]
  ring

lemma finrank_CProfileSumCodomain (n : ℕ) [NeZero n] :
    Module.finrank F₂ (CProfileSumCodomain n) = n ^ 2 :=
  finrank_BProfileSumCodomain n

/-- For each `(u2,u3)`, the sum over `y` of profile entries must vanish on admissible profiles. -/
noncomputable def bProfileSumConstraintLinearMap {n : ℕ} [NeZero n] :
    BProfileRaw n →ₗ[F₂] BProfileSumCodomain n where
  toFun f := fun u2 u3 => ∑ y : ZMod n, f y u2 u3
  map_add' f g := by
    funext u2 u3
    simp [Finset.sum_add_distrib]
  map_smul' r f := by
    funext u2 u3
    simp_rw [Pi.smul_apply]
    convert (Finset.smul_sum (f := fun y => f y u2 u3) (s := Finset.univ)).symm using 1

/-- For each `(u0,u1)`, the sum over `z` of profile entries must vanish on admissible profiles. -/
noncomputable def cProfileSumConstraintLinearMap {n : ℕ} [NeZero n] :
    CProfileRaw n →ₗ[F₂] CProfileSumCodomain n where
  toFun f := fun u0 u1 => ∑ z : ZMod n, f z u0 u1
  map_add' f g := by
    funext u0 u1
    simp [Finset.sum_add_distrib]
  map_smul' r f := by
    funext u0 u1
    simp_rw [Pi.smul_apply]
    convert (Finset.smul_sum (f := fun z => f z u0 u1) (s := Finset.univ)).symm using 1

lemma bProfileSumConstraintLinearMap_surjective {n : ℕ} [NeZero n] :
    Function.Surjective (bProfileSumConstraintLinearMap (n := n)) := by
  intro g
  refine ⟨fun y u2 u3 => if y = (0 : ZMod n) then g u2 u3 else 0, ?_⟩
  funext u2 u3
  dsimp [bProfileSumConstraintLinearMap]
  rw [Finset.sum_eq_single (0 : ZMod n)]
  · simp
  · intro y _ hy
    dsimp
    rw [if_neg hy]
  · simp

lemma cProfileSumConstraintLinearMap_surjective {n : ℕ} [NeZero n] :
    Function.Surjective (cProfileSumConstraintLinearMap (n := n)) := by
  intro g
  refine ⟨fun z u0 u1 => if z = (0 : ZMod n) then g u0 u1 else 0, ?_⟩
  funext u0 u1
  dsimp [cProfileSumConstraintLinearMap]
  rw [Finset.sum_eq_single (0 : ZMod n)]
  · simp
  · intro z _ hz
    dsimp
    rw [if_neg hz]
  · simp

lemma bProfileSumConstraintLinearMap_range_eq_top {n : ℕ} [NeZero n] :
    LinearMap.range (bProfileSumConstraintLinearMap (n := n)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact LinearMap.mem_range.2 (bProfileSumConstraintLinearMap_surjective x)

lemma cProfileSumConstraintLinearMap_range_eq_top {n : ℕ} [NeZero n] :
    LinearMap.range (cProfileSumConstraintLinearMap (n := n)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact LinearMap.mem_range.2 (cProfileSumConstraintLinearMap_surjective x)

/-- Admissible `B`-profiles: slice sums over `y` vanish for every `(u2,u3)`. -/
noncomputable def BProfileAdmSubmodule (n : ℕ) [NeZero n] : Submodule F₂ (BProfileRaw n) :=
  LinearMap.ker (bProfileSumConstraintLinearMap (n := n))

/-- Admissible `C`-profiles: slice sums over `z` vanish for every `(u0,u1)`. -/
noncomputable def CProfileAdmSubmodule (n : ℕ) [NeZero n] : Submodule F₂ (CProfileRaw n) :=
  LinearMap.ker (cProfileSumConstraintLinearMap (n := n))

lemma mem_BProfileAdmSubmodule_iff {n : ℕ} [NeZero n] (f : BProfileRaw n) :
    f ∈ BProfileAdmSubmodule n ↔ ∀ u2 u3 : ZMod n, (∑ y : ZMod n, f y u2 u3) = 0 := by
  rw [BProfileAdmSubmodule, LinearMap.mem_ker]
  constructor
  · intro hf u2 u3
    simpa [bProfileSumConstraintLinearMap, Pi.zero_apply] using congr_arg (fun g => g u2 u3) hf
  · intro hf
    ext u2 u3
    simpa [bProfileSumConstraintLinearMap, Pi.zero_apply] using hf u2 u3

lemma mem_CProfileAdmSubmodule_iff {n : ℕ} [NeZero n] (f : CProfileRaw n) :
    f ∈ CProfileAdmSubmodule n ↔ ∀ u0 u1 : ZMod n, (∑ z : ZMod n, f z u0 u1) = 0 := by
  rw [CProfileAdmSubmodule, LinearMap.mem_ker]
  constructor
  · intro hf u0 u1
    simpa [cProfileSumConstraintLinearMap, Pi.zero_apply] using congr_arg (fun g => g u0 u1) hf
  · intro hf
    ext u0 u1
    simpa [cProfileSumConstraintLinearMap, Pi.zero_apply] using hf u0 u1

lemma finrank_BProfileAdmSubmodule (n : ℕ) [NeZero n] :
    Module.finrank F₂ (BProfileAdmSubmodule n) = n ^ 3 - n ^ 2 := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (bProfileSumConstraintLinearMap (n := n))
  have hrng : Module.finrank F₂ (LinearMap.range (bProfileSumConstraintLinearMap (n := n))) = n ^ 2 := by
    rw [bProfileSumConstraintLinearMap_range_eq_top, finrank_top, finrank_BProfileSumCodomain]
  have hdom := finrank_BProfileRaw n
  rw [hrng, hdom] at hsum
  have hle : n ^ 2 ≤ n ^ 3 := by
    nlinarith [Nat.one_le_pow 3 n (NeZero.pos n)]
  have hker : Module.finrank F₂ (LinearMap.ker (bProfileSumConstraintLinearMap (n := n))) = n ^ 3 - n ^ 2 := by
    omega
  simpa [BProfileAdmSubmodule] using hker

lemma finrank_CProfileAdmSubmodule (n : ℕ) [NeZero n] :
    Module.finrank F₂ (CProfileAdmSubmodule n) = n ^ 3 - n ^ 2 := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (cProfileSumConstraintLinearMap (n := n))
  have hrng : Module.finrank F₂ (LinearMap.range (cProfileSumConstraintLinearMap (n := n))) = n ^ 2 := by
    rw [cProfileSumConstraintLinearMap_range_eq_top, finrank_top, finrank_CProfileSumCodomain]
  have hdom := finrank_CProfileRaw n
  rw [hrng, hdom] at hsum
  have hle : n ^ 2 ≤ n ^ 3 := by
    nlinarith [Nat.one_le_pow 3 n (NeZero.pos n)]
  have hker : Module.finrank F₂ (LinearMap.ker (cProfileSumConstraintLinearMap (n := n))) = n ^ 3 - n ^ 2 := by
    omega
  simpa [CProfileAdmSubmodule] using hker

/-- `B ↦ (y,u2,u3) ↦ bKernel B y u2 u3`. -/
noncomputable def bProfileLinearMap {n : ℕ} [NeZero n] : BField n →ₗ[F₂] BProfileRaw n where
  toFun B := fun y u2 u3 => bKernel B y u2 u3
  map_add' B1 B2 := by
    funext y u2 u3
    exact bKernel_add B1 B2 y u2 u3
  map_smul' r B := by
    funext y u2 u3
    exact bKernel_smul r B y u2 u3

/-- `C ↦ (z,u0,u1) ↦ cKernel C z u0 u1`. -/
noncomputable def cProfileLinearMap {n : ℕ} [NeZero n] : CField n →ₗ[F₂] CProfileRaw n where
  toFun C := fun z u0 u1 => cKernel C z u0 u1
  map_add' C1 C2 := by
    funext z u0 u1
    exact cKernel_add C1 C2 z u0 u1
  map_smul' r C := by
    funext z u0 u1
    exact cKernel_smul r C z u0 u1

lemma coeffFromBC_smul_pair {n : ℕ} [NeZero n] (r : F₂) (B : BField n) (C : CField n) :
    coeffFromBC (r • B) (r • C) = r • coeffFromBC B C := by
  rcases eq_or_ne r 0 with hr0 | hr1
  · subst hr0
    ext u
    simp [coeffFromBC_zero_B_zero_C_eq_zero, Pi.smul_apply]
  · rw [ZMod_two_eq_one_of_ne_zero hr1]
    simp [one_smul]

set_option maxHeartbeats 800000 in
-- Nested `Finset.sum_add_distrib` on `bSlice` (three sums) exceeds default heartbeats.
lemma bSlice_add {n : ℕ} [NeZero n] (B1 B2 : BField n) (y : ZMod n) :
    bSlice (B1 + B2) y = bSlice B1 y + bSlice B2 y := by
  unfold bSlice
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x1 hx1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro u2 hu2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro u3 hu3
  simp [add_assoc, add_left_comm, add_comm]

lemma bSlice_zero {n : ℕ} [NeZero n] (y : ZMod n) : bSlice (0 : BField n) y = 0 := by
  simp [bSlice]

lemma bSlice_smul {n : ℕ} [NeZero n] (r : F₂) (B : BField n) (y : ZMod n) :
    bSlice (r • B) y = r • bSlice B y := by
  rcases eq_or_ne r 0 with hr0 | hr1
  · subst hr0
    simp [bSlice_zero, Pi.smul_apply]
  · rw [ZMod_two_eq_one_of_ne_zero hr1]
    simp [one_smul]

set_option maxHeartbeats 800000 in
-- Nested `Finset.sum_add_distrib` on `cSlice` (three sums) exceeds default heartbeats.
lemma cSlice_add {n : ℕ} [NeZero n] (C1 C2 : CField n) (z : ZMod n) :
    cSlice (C1 + C2) z = cSlice C1 z + cSlice C2 z := by
  unfold cSlice
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x1 hx1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro u0 hu0
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro u1 hu1
  simp [add_assoc, add_left_comm, add_comm]

lemma cSlice_zero {n : ℕ} [NeZero n] (z : ZMod n) : cSlice (0 : CField n) z = 0 := by
  simp [cSlice]

lemma cSlice_smul {n : ℕ} [NeZero n] (r : F₂) (C : CField n) (z : ZMod n) :
    cSlice (r • C) z = r • cSlice C z := by
  rcases eq_or_ne r 0 with hr0 | hr1
  · subst hr0
    simp [cSlice_zero, Pi.smul_apply]
  · rw [ZMod_two_eq_one_of_ne_zero hr1]
    simp [one_smul]

/-- `t ↦ bSlice B t + cSlice C t` is `F₂`-linear in `(B, C)`; its kernel is the slice/diagonal
matching condition `∀ t, bSlice B t = cSlice C t` (see `mem_ker_sliceDiffLinearMap_iff`). -/
noncomputable def sliceDiffLinearMap {n : ℕ} [NeZero n] :
    (BField n × CField n) →ₗ[F₂] (ZMod n → F₂) where
  toFun bc := fun t => bSlice bc.1 t + cSlice bc.2 t
  map_add' bc1 bc2 := by
    rcases bc1 with ⟨B1, C1⟩
    rcases bc2 with ⟨B2, C2⟩
    ext y
    simp [bSlice_add, cSlice_add, Pi.add_apply, add_assoc, add_left_comm, add_comm]
  map_smul' r bc := by
    rcases bc with ⟨B, C⟩
    ext y
    simp only [Prod.smul_mk, Pi.smul_apply, RingHom.id_apply]
    rw [bSlice_smul, cSlice_smul, ← smul_add]

lemma mem_ker_sliceDiffLinearMap_iff {n : ℕ} [NeZero n] (bc : BField n × CField n) :
    bc ∈ LinearMap.ker (sliceDiffLinearMap (n := n)) ↔ ∀ t : ZMod n, bSlice bc.1 t = cSlice bc.2 t := by
  rw [LinearMap.mem_ker]
  let f : ZMod n → F₂ := fun t => bSlice bc.1 t + cSlice bc.2 t
  change f = 0 ↔ _
  constructor
  · intro hf t
    replace hf := congr_fun hf t
    dsimp [f] at hf
    exact (F2_add_eq_zero_iff_eq _ _).1 hf
  · intro hf
    funext t
    dsimp [f]
    rw [hf t]
    simpa using F2_add_self (cSlice bc.2 t)

/-- `coeffFromBC` is `F₂`-linear on `B × C` (hence `SurvivingBC` is the kernel of this map). -/
noncomputable def coeffFromBCLinearMap {n : ℕ} [NeZero n] :
    (BField n × CField n) →ₗ[F₂] AField n where
  toFun bc := coeffFromBC bc.1 bc.2
  map_add' bc1 bc2 := by
    rcases bc1 with ⟨B1, C1⟩
    rcases bc2 with ⟨B2, C2⟩
    simpa using coeffFromBC_add_add (n := n) B1 B2 C1 C2
  map_smul' r bc := by
    rcases bc with ⟨B, C⟩
    simpa using coeffFromBC_smul_pair (n := n) r B C

abbrev SurvivingBCKernel (n : ℕ) [NeZero n] :=
  { p : BField n × CField n //
      ∀ u : T4 n, bKernel p.1 (u 0 + u 1) (u 2) (u 3) = cKernel p.2 (u 2 + u 3) (u 0) (u 1) }

/-- Kernel condition in explicit four-variable form. -/
abbrev SurvivingBCKernelQuad (n : ℕ) [NeZero n] :=
  { p : BField n × CField n //
      ∀ a b u2 u3 : ZMod n, bKernel p.1 (a + b) u2 u3 = cKernel p.2 (u2 + u3) a b }

noncomputable def survivingBCKernel_equiv_quad {n : ℕ} [NeZero n] :
    SurvivingBCKernel n ≃ SurvivingBCKernelQuad n where
  toFun x := by
    rcases x with ⟨⟨B, C⟩, h⟩
    refine ⟨⟨B, C⟩, ?_⟩
    intro a b u2 u3
    simpa [vec4, add_assoc] using h (vec4 a b u2 u3)
  invFun x := by
    rcases x with ⟨⟨B, C⟩, h⟩
    refine ⟨⟨B, C⟩, ?_⟩
    intro u
    simpa [vec4, add_assoc] using h (u 0) (u 1) (u 2) (u 3)
  left_inv x := by
    rcases x with ⟨⟨B, C⟩, h⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨B, C⟩, h⟩
    rfl

lemma bSlice_eq_sum_bKernel {n : ℕ} [NeZero n] (B : BField n) (y : ZMod n) :
    bSlice B y = ∑ u2 : ZMod n, ∑ u3 : ZMod n, bKernel B y u2 u3 := by
  unfold bSlice bKernel
  calc
    (∑ x1 : ZMod n, ∑ u2 : ZMod n, ∑ u3 : ZMod n,
      (B (vec4 x1 y u2 u3) + B (vec4 x1 (y + 1) u2 u3)))
        = ∑ u2 : ZMod n, ∑ x1 : ZMod n, ∑ u3 : ZMod n,
            (B (vec4 x1 y u2 u3) + B (vec4 x1 (y + 1) u2 u3)) := by
            rw [Finset.sum_comm]
    _ = ∑ u2 : ZMod n, ∑ u3 : ZMod n, ∑ x1 : ZMod n,
          (B (vec4 x1 y u2 u3) + B (vec4 x1 (y + 1) u2 u3)) := by
          refine Finset.sum_congr rfl ?_
          intro u2 hu2
          rw [Finset.sum_comm]

lemma cSlice_eq_sum_cKernel {n : ℕ} [NeZero n] (C : CField n) (z : ZMod n) :
    cSlice C z = ∑ u0 : ZMod n, ∑ u1 : ZMod n, cKernel C z u0 u1 := by
  unfold cSlice cKernel
  calc
    (∑ x1 : ZMod n, ∑ u0 : ZMod n, ∑ u1 : ZMod n,
      (C (vec4 x1 u0 u1 z) + C (vec4 x1 u0 u1 (z + 1))))
        = ∑ u0 : ZMod n, ∑ x1 : ZMod n, ∑ u1 : ZMod n,
            (C (vec4 x1 u0 u1 z) + C (vec4 x1 u0 u1 (z + 1))) := by
            rw [Finset.sum_comm]
    _ = ∑ u0 : ZMod n, ∑ u1 : ZMod n, ∑ x1 : ZMod n,
          (C (vec4 x1 u0 u1 z) + C (vec4 x1 u0 u1 (z + 1))) := by
          refine Finset.sum_congr rfl ?_
          intro u0 hu0
          rw [Finset.sum_comm]

lemma kernel_implies_bSlice_via_cKernel {n : ℕ} [NeZero n]
    (B : BField n) (C : CField n)
    (hker : ∀ u : T4 n, bKernel B (u 0 + u 1) (u 2) (u 3) = cKernel C (u 2 + u 3) (u 0) (u 1)) :
    ∀ a b : ZMod n,
      bSlice B (a + b) = ∑ u2 : ZMod n, ∑ u3 : ZMod n, cKernel C (u2 + u3) a b := by
  intro a b
  calc
    bSlice B (a + b) = ∑ u2 : ZMod n, ∑ u3 : ZMod n, bKernel B (a + b) u2 u3 := by
      simpa using bSlice_eq_sum_bKernel (n := n) B (a + b)
    _ = ∑ u2 : ZMod n, ∑ u3 : ZMod n, cKernel C (u2 + u3) a b := by
      refine Finset.sum_congr rfl ?_
      intro u2 hu2
      refine Finset.sum_congr rfl ?_
      intro u3 hu3
      simpa [vec4, add_assoc] using hker (vec4 a b u2 u3)

lemma kernel_implies_cSlice_via_bKernel {n : ℕ} [NeZero n]
    (B : BField n) (C : CField n)
    (hker : ∀ u : T4 n, bKernel B (u 0 + u 1) (u 2) (u 3) = cKernel C (u 2 + u 3) (u 0) (u 1)) :
    ∀ a b : ZMod n,
      cSlice C (a + b) = ∑ u0 : ZMod n, ∑ u1 : ZMod n, bKernel B (u0 + u1) a b := by
  intro a b
  calc
    cSlice C (a + b) = ∑ u0 : ZMod n, ∑ u1 : ZMod n, cKernel C (a + b) u0 u1 := by
      simpa using cSlice_eq_sum_cKernel (n := n) C (a + b)
    _ = ∑ u0 : ZMod n, ∑ u1 : ZMod n, bKernel B (u0 + u1) a b := by
      refine Finset.sum_congr rfl ?_
      intro u0 hu0
      refine Finset.sum_congr rfl ?_
      intro u1 hu1
      simpa [vec4, add_assoc] using (hker (vec4 u0 u1 a b)).symm

lemma coeffFromBC_zero_implies_bSlice_via_cKernel {n : ℕ} [NeZero n]
    (B : BField n) (C : CField n)
    (hBC : coeffFromBC B C = 0) :
    ∀ a b : ZMod n,
      bSlice B (a + b) = ∑ u2 : ZMod n, ∑ u3 : ZMod n, cKernel C (u2 + u3) a b := by
  have hker := (coeffFromBC_eq_zero_iff_kernels_eq (n := n) B C).1 hBC
  exact kernel_implies_bSlice_via_cKernel (n := n) B C hker

lemma coeffFromBC_zero_implies_cSlice_via_bKernel {n : ℕ} [NeZero n]
    (B : BField n) (C : CField n)
    (hBC : coeffFromBC B C = 0) :
    ∀ a b : ZMod n,
      cSlice C (a + b) = ∑ u0 : ZMod n, ∑ u1 : ZMod n, bKernel B (u0 + u1) a b := by
  have hker := (coeffFromBC_eq_zero_iff_kernels_eq (n := n) B C).1 hBC
  exact kernel_implies_cSlice_via_bKernel (n := n) B C hker

lemma sum_reorder_three {n : ℕ} [NeZero n]
    (f : ZMod n → ZMod n → ZMod n → F₂) :
    (∑ a : ZMod n, ∑ b : ZMod n, ∑ c : ZMod n, f c a b)
      = ∑ c : ZMod n, ∑ a : ZMod n, ∑ b : ZMod n, f c a b := by
  calc
    (∑ a : ZMod n, ∑ b : ZMod n, ∑ c : ZMod n, f c a b)
        = ∑ b : ZMod n, ∑ a : ZMod n, ∑ c : ZMod n, f c a b := by
            rw [Finset.sum_comm]
    _ = ∑ b : ZMod n, ∑ c : ZMod n, ∑ a : ZMod n, f c a b := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          rw [Finset.sum_comm]
    _ = ∑ c : ZMod n, ∑ b : ZMod n, ∑ a : ZMod n, f c a b := by
          rw [Finset.sum_comm]
    _ = ∑ c : ZMod n, ∑ a : ZMod n, ∑ b : ZMod n, f c a b := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          rw [Finset.sum_comm]

noncomputable def deltaNo13Raw (n : ℕ) [NeZero n] : ℤ :=
  ∑ S : No13ValidAssignments n, W S.1

lemma deltaNo13Raw_eq_sum_normalForm {n : ℕ} [NeZero n] :
    deltaNo13Raw n = ∑ nf : No13NormalForm n, W (toNo13Assignment nf) := by
  classical
  unfold deltaNo13Raw
  simpa using
    (((no13NormalFormEquiv (n := n)).symm.sum_comp
      (fun S : No13ValidAssignments n => W S.1)).symm)

lemma localPhaseBit_toNo13Assignment {n : ℕ} (nf : No13NormalForm n) (x : T5 n) :
    localPhaseBit (toNo13Assignment nf) x
      = nf.A (projA x) *
          (nf.B (projB x)
            + nf.B (vec4 (x 0) (x 1 + x 2 + 1) (x 3) (x 4))
            + nf.C (projC x)
            + nf.C (vec4 (x 0) (x 1) (x 2) (x 3 + x 4 + 1))) := by
  simp [localPhaseBit, toNo13Assignment, mul_add, add_assoc, add_left_comm, add_comm]

noncomputable def alphaCoeff {n : ℕ} [NeZero n] (c A : AField n) : F₂ :=
  ∑ u : T4 n, A u * c u

noncomputable def alphaSigned {n : ℕ} [NeZero n] (c A : AField n) : ℤ :=
  bitSign (alphaCoeff c A)

def toggleAtA {n : ℕ} [NeZero n] (u0 : T4 n) (A : AField n) : AField n :=
  fun u => A u + if u = u0 then 1 else 0

noncomputable def toggleEquivA {n : ℕ} [NeZero n] (u0 : T4 n) : AField n ≃ AField n where
  toFun := toggleAtA u0
  invFun := toggleAtA u0
  left_inv A := by
    ext u
    by_cases h : u = u0
    · subst h
      have h11 : (1 : F₂) + 1 = 0 := by decide
      simp [toggleAtA, add_assoc, h11]
    · simp [toggleAtA, h]
  right_inv A := by
    ext u
    by_cases h : u = u0
    · subst h
      have h11 : (1 : F₂) + 1 = 0 := by decide
      simp [toggleAtA, add_assoc, h11]
    · simp [toggleAtA, h]

lemma bitSign_zero : bitSign (0 : F₂) = 1 := by simp [bitSign]

lemma bitSign_add (a b : F₂) : bitSign (a + b) = bitSign a * bitSign b := by
  fin_cases a <;> fin_cases b <;> decide

lemma bitSign_add_one (a : F₂) : bitSign (a + 1) = -bitSign a := by
  fin_cases a <;> decide

lemma prod_bitSign_eq_bitSign_sum {α : Type*} (s : Finset α) (f : α → F₂) :
    s.prod (fun a => bitSign (f a)) = bitSign (s.sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [bitSign_zero]
  | @insert a s ha hs =>
      simp [ha, hs, bitSign_add, mul_comm, mul_left_comm, mul_assoc]

def t5EquivAProd (n : ℕ) : T5 n ≃ ZMod n × T4 n where
  toFun x := (x 0, projA x)
  invFun p := vec5 p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3)
  left_inv x := by
    simp [projA, vec4, vec5, vec5_eta]
  right_inv p := by
    rcases p with ⟨x0, u⟩
    refine Prod.ext rfl ?_
    ext i
    fin_cases i <;> rfl

def bcSummand {n : ℕ} (nf : No13NormalForm n) (x1 : ZMod n) (u : T4 n) : F₂ :=
  nf.B (vec4 x1 (u 0 + u 1) (u 2) (u 3))
    + nf.B (vec4 x1 (u 0 + u 1 + 1) (u 2) (u 3))
    + nf.C (vec4 x1 (u 0) (u 1) (u 2 + u 3))
    + nf.C (vec4 x1 (u 0) (u 1) (u 2 + u 3 + 1))

lemma W_toNo13Assignment_eq_alphaSigned {n : ℕ} [NeZero n]
    (nf : No13NormalForm n) :
    W (toNo13Assignment nf) = alphaSigned (coeffFromBC nf.B nf.C) nf.A := by
  classical
  unfold W alphaSigned alphaCoeff
  calc
    ∏ x : T5 n, bitSign (localPhaseBit (toNo13Assignment nf) x)
        = ∏ p : ZMod n × T4 n, bitSign (localPhaseBit (toNo13Assignment nf) ((t5EquivAProd n).symm p)) := by
            simpa using (t5EquivAProd n).prod_comp
              (fun p : ZMod n × T4 n =>
                bitSign (localPhaseBit (toNo13Assignment nf) ((t5EquivAProd n).symm p)))
    _ = ∏ p : ZMod n × T4 n,
          bitSign (nf.A p.2 * bcSummand nf p.1 p.2) := by
          congr with p
          rcases p with ⟨x1, u⟩
          simp [bcSummand, t5EquivAProd, localPhaseBit_toNo13Assignment, projA, vec4, vec5]
    _ = ∏ u : T4 n, ∏ x1 : ZMod n,
          bitSign (nf.A u * bcSummand nf x1 u) := by
          rw [Fintype.prod_prod_type_right]
    _ = ∏ u : T4 n,
          bitSign (∑ x1 : ZMod n, nf.A u * bcSummand nf x1 u) := by
          congr with u
          simpa using prod_bitSign_eq_bitSign_sum (Finset.univ : Finset (ZMod n))
            (fun x1 : ZMod n => nf.A u * bcSummand nf x1 u)
    _ = ∏ u : T4 n, bitSign (nf.A u * coeffFromBC nf.B nf.C u) := by
          congr with u
          simp [coeffFromBC, bcSummand, Finset.mul_sum]
    _ = bitSign (∑ u : T4 n, nf.A u * coeffFromBC nf.B nf.C u) := by
          simpa using prod_bitSign_eq_bitSign_sum (Finset.univ : Finset (T4 n))
            (fun u : T4 n => nf.A u * coeffFromBC nf.B nf.C u)

lemma alphaCoeff_toggleAtA {n : ℕ} [NeZero n]
    (c A : AField n) (u0 : T4 n) :
    alphaCoeff c (toggleAtA u0 A) = alphaCoeff c A + c u0 := by
  classical
  unfold alphaCoeff toggleAtA
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hs : ∑ u : T4 n, (if u = u0 then 1 else 0) * c u = c u0 := by
    simp
  simpa [hs]

lemma alphaSigned_toggleAtA {n : ℕ} [NeZero n]
    (c A : AField n) (u0 : T4 n) (hc : c u0 = 1) :
    alphaSigned c (toggleAtA u0 A) = -alphaSigned c A := by
  unfold alphaSigned
  rw [alphaCoeff_toggleAtA, hc, bitSign_add_one]

noncomputable def alphaSignedSum {n : ℕ} [NeZero n] (c : AField n) : ℤ :=
  ∑ A : AField n, alphaSigned c A

lemma alphaSignedSum_zero {n : ℕ} [NeZero n] :
    alphaSignedSum (n := n) 0 = (2 : ℤ) ^ (n ^ 4) := by
  unfold alphaSignedSum alphaSigned alphaCoeff
  have hcard : (((Fintype.card (AField n)) : ℕ) : ℤ) = (2 : ℤ) ^ (n ^ 4) := by
    rw [card_AField]
    norm_num
  calc
    ∑ A : AField n, bitSign (∑ u : T4 n, A u * (0 : AField n) u)
        = ∑ A : AField n, (1 : ℤ) := by
            congr with A
            simp [bitSign_zero]
    _ = Fintype.card (AField n) := by simp
    _ = (2 : ℤ) ^ (n ^ 4) := hcard

lemma F2_ne_zero_eq_one (a : F₂) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (ha rfl)
  · rfl

theorem alphaSignedSum_formula {n : ℕ} [NeZero n] (c : AField n) :
    alphaSignedSum c = if c = 0 then (2 : ℤ) ^ (n ^ 4) else 0 := by
  classical
  by_cases hc : c = 0
  · simp [hc, alphaSignedSum_zero]
  · have hne : ∃ u0 : T4 n, c u0 ≠ 0 := by
      by_contra hforall
      push Not at hforall
      apply hc
      ext u
      exact hforall u
    rcases hne with ⟨u0, hu0⟩
    have hcu0 : c u0 = 1 := F2_ne_zero_eq_one _ hu0
    have hs :
        alphaSignedSum c = -alphaSignedSum c := by
      unfold alphaSignedSum
      calc
        ∑ A : AField n, alphaSigned c A
            = ∑ A : AField n, alphaSigned c (toggleAtA u0 A) := by
                simpa using
                  (((toggleEquivA (n := n) u0).sum_comp
                    (fun A : AField n => alphaSigned c A)).symm)
        _ = ∑ A : AField n, -alphaSigned c A := by
              congr with A
              exact alphaSigned_toggleAtA c A u0 hcu0
        _ = -∑ A : AField n, alphaSigned c A := by
              simp
    have hz : alphaSignedSum c = 0 := by linarith
    simp [hc, hz]

abbrev SurvivingBC (n : ℕ) [NeZero n] :=
  { p : BField n × CField n // coeffFromBC p.1 p.2 = 0 }

@[simp] lemma coeffFromBCLinearMap_apply {n : ℕ} [NeZero n] (bc : BField n × CField n) :
    coeffFromBCLinearMap (n := n) bc = coeffFromBC bc.1 bc.2 :=
  rfl

lemma mem_ker_coeffFromBCLinearMap_iff {n : ℕ} [NeZero n] (bc : BField n × CField n) :
    bc ∈ LinearMap.ker (coeffFromBCLinearMap (n := n)) ↔ coeffFromBC bc.1 bc.2 = 0 := by
  simp [LinearMap.mem_ker]

/-- `SurvivingBC` is exactly the kernel of `coeffFromBCLinearMap` (as a subtype of `B × C`). -/
noncomputable def survivingBC_equiv_ker_coeffFromBCLinearMap {n : ℕ} [NeZero n] :
    SurvivingBC n ≃ LinearMap.ker (coeffFromBCLinearMap (n := n)) :=
  Equiv.subtypeEquivRight (by
    intro bc
    simpa [mem_ker_coeffFromBCLinearMap_iff])

noncomputable def survivingBC_equiv_kernel {n : ℕ} [NeZero n] :
    SurvivingBC n ≃ SurvivingBCKernel n where
  toFun := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    exact ⟨⟨B, C⟩, (coeffFromBC_eq_zero_iff_kernels_eq (n := n) B C).1 hBC⟩
  invFun := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    exact ⟨⟨B, C⟩, (coeffFromBC_eq_zero_iff_kernels_eq (n := n) B C).2 hBC⟩
  left_inv := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    rfl

lemma sum_W_over_A {n : ℕ} [NeZero n] (B : BField n) (C : CField n) :
    ∑ A : AField n, W (toNo13Assignment ⟨A, B, C⟩)
      = if coeffFromBC B C = 0 then (2 : ℤ) ^ (n ^ 4) else 0 := by
  calc
    ∑ A : AField n, W (toNo13Assignment ⟨A, B, C⟩)
        = ∑ A : AField n, alphaSigned (coeffFromBC B C) A := by
            congr with A
            simpa using
              (W_toNo13Assignment_eq_alphaSigned (n := n) (nf := ⟨A, B, C⟩))
    _ = if coeffFromBC B C = 0 then (2 : ℤ) ^ (n ^ 4) else 0 := by
          simpa using alphaSignedSum_formula (n := n) (c := coeffFromBC B C)

lemma deltaNo13Raw_eq_sum_survivingIndicator {n : ℕ} [NeZero n] :
    deltaNo13Raw n
      = ∑ q : BField n × CField n,
          if coeffFromBC q.1 q.2 = 0 then (2 : ℤ) ^ (n ^ 4) else 0 := by
  rw [deltaNo13Raw_eq_sum_normalForm]
  calc
    ∑ nf : No13NormalForm n, W (toNo13Assignment nf)
        = ∑ p : AField n × (BField n × CField n),
            W (toNo13Assignment ((normalFormEquivProd n).symm p)) := by
              simpa using
                (((normalFormEquivProd n).symm.sum_comp
                  (fun nf : No13NormalForm n => W (toNo13Assignment nf))).symm)
    _ = ∑ q : BField n × CField n,
          ∑ A : AField n, W (toNo13Assignment ((normalFormEquivProd n).symm (A, q))) := by
            rw [Fintype.sum_prod_type_right]
    _ = ∑ q : BField n × CField n,
          if coeffFromBC q.1 q.2 = 0 then (2 : ℤ) ^ (n ^ 4) else 0 := by
            congr with q
            simpa [normalFormEquivProd] using sum_W_over_A (n := n) q.1 q.2

lemma sum_ite_const_eq_card_filter {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] (a : ℤ) :
    Finset.sum s (fun x => if p x then a else 0) = ((s.filter p).card : ℤ) * a := by
  calc
    Finset.sum s (fun x => if p x then a else 0) = Finset.sum (s.filter p) (fun _ => a) := by
      rw [Finset.sum_filter]
    _ = ((s.filter p).card : ℤ) • a := by simp
    _ = ((s.filter p).card : ℤ) * a := by simp

lemma deltaNo13Raw_eq_survivingBC_card {n : ℕ} [NeZero n] :
    deltaNo13Raw n = (2 : ℤ) ^ (n ^ 4) * Fintype.card (SurvivingBC n) := by
  classical
  let p : BField n × CField n → Prop := fun q => coeffFromBC q.1 q.2 = 0
  let a : ℤ := (2 : ℤ) ^ (n ^ 4)
  rw [deltaNo13Raw_eq_sum_survivingIndicator]
  have hsum :
      (∑ q : BField n × CField n, if p q then a else 0)
        = ((Finset.univ.filter p).card : ℤ) * a := by
    simpa using
      sum_ite_const_eq_card_filter (s := (Finset.univ : Finset (BField n × CField n))) (p := p) (a := a)
  have hcardNat : (Finset.univ.filter p).card = Fintype.card (SurvivingBC n) := by
    simpa [SurvivingBC, p] using (Fintype.card_subtype p).symm
  have hcard : ((Finset.univ.filter p).card : ℤ) = Fintype.card (SurvivingBC n) := by
    exact_mod_cast hcardNat
  calc
    (∑ q : BField n × CField n, if coeffFromBC q.1 q.2 = 0 then (2 : ℤ) ^ (n ^ 4) else 0)
        = ((Finset.univ.filter p).card : ℤ) * a := by simpa [p, a] using hsum
    _ = Fintype.card (SurvivingBC n) * a := by rw [hcard]
    _ = (2 : ℤ) ^ (n ^ 4) * Fintype.card (SurvivingBC n) := by
          simp [a, mul_comm]

abbrev T2 (n : ℕ) := Fin 2 → ZMod n
abbrev HRaw (n : ℕ) := T2 n → F₂

def vec2 {n : ℕ} (a b : ZMod n) : T2 n
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

@[simp] lemma vec2_zero {n : ℕ} (a b : ZMod n) : vec2 a b 0 = a := rfl
@[simp] lemma vec2_one {n : ℕ} (a b : ZMod n) : vec2 a b 1 = b := rfl
@[simp] lemma vec2_eta {n : ℕ} (p : T2 n) : vec2 (p 0) (p 1) = p := by
  ext i <;> fin_cases i <;> rfl

def rowSum {n : ℕ} [NeZero n] (h : HRaw n) (t : ZMod n) : F₂ :=
  ∑ s : ZMod n, h (vec2 s t)

def colSum {n : ℕ} [NeZero n] (h : HRaw n) (s : ZMod n) : F₂ :=
  ∑ t : ZMod n, h (vec2 s t)

abbrev HAdmissible (n : ℕ) [NeZero n] :=
  { h : HRaw n // (∀ t : ZMod n, rowSum h t = 0) ∧ (∀ s : ZMod n, colSum h s = 0) }

abbrev CoreIdx (n : ℕ) [NeZero n] := {x : ZMod n // x ≠ 0}

def zmodEquivUnitSumCore {n : ℕ} [NeZero n] :
    ZMod n ≃ (Unit ⊕ CoreIdx n) where
  toFun x := by
    by_cases hx : x = 0
    · exact Sum.inl ()
    · exact Sum.inr ⟨x, hx⟩
  invFun y := by
    rcases y with _ | a
    · exact 0
    · exact a.1
  left_inv x := by
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx]
  right_inv y := by
    rcases y with _ | a
    · simp
    · simp [a.2]

lemma sum_zmod_eq_zero_add_core {n : ℕ} [NeZero n] (f : ZMod n → F₂) :
    (∑ x : ZMod n, f x) = f 0 + ∑ a : CoreIdx n, f a.1 := by
  let g : Unit ⊕ CoreIdx n → F₂ := fun y =>
    match y with
    | Sum.inl _ => f 0
    | Sum.inr a => f a.1
  have hsum :
      (∑ x : ZMod n, f x) = ∑ y : Unit ⊕ CoreIdx n, g y := by
    simpa [g] using
      (Fintype.sum_equiv
        (zmodEquivUnitSumCore (n := n))
        (fun x : ZMod n => f x)
        (fun y : Unit ⊕ CoreIdx n => g y)
        (by
          intro x
          by_cases hx : x = 0
          · simp [zmodEquivUnitSumCore, g, hx]
          · simp [zmodEquivUnitSumCore, g, hx]))
  calc
    (∑ x : ZMod n, f x) = ∑ y : Unit ⊕ CoreIdx n, g y := hsum
    _ = f 0 + ∑ a : CoreIdx n, f a.1 := by
      simp [g]

def coreRowSum {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) (t : CoreIdx n) : F₂ :=
  ∑ s : CoreIdx n, g s t

def coreColSum {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) (s : CoreIdx n) : F₂ :=
  ∑ t : CoreIdx n, g s t

def coreAllSum {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) : F₂ :=
  ∑ s : CoreIdx n, ∑ t : CoreIdx n, g s t

def hOfCore {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) : HRaw n := fun p =>
  if hs : p 0 = 0 then
    if ht : p 1 = 0 then
      coreAllSum g
    else
      coreRowSum g ⟨p 1, ht⟩
  else
    if ht : p 1 = 0 then
      coreColSum g ⟨p 0, hs⟩
    else
      g ⟨p 0, hs⟩ ⟨p 1, ht⟩

lemma hOfCore_at_00 {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) :
    hOfCore g (vec2 0 0) = coreAllSum g := by
  simp [hOfCore]

lemma hOfCore_at_0t {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) (t : CoreIdx n) :
    hOfCore g (vec2 0 t.1) = coreRowSum g t := by
  simp [hOfCore, t.2]

lemma hOfCore_at_s0 {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) (s : CoreIdx n) :
    hOfCore g (vec2 s.1 0) = coreColSum g s := by
  simp [hOfCore, s.2]

lemma hOfCore_at_st {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) (s t : CoreIdx n) :
    hOfCore g (vec2 s.1 t.1) = g s t := by
  simp [hOfCore, s.2, t.2]

lemma sum_coreCol_eq_coreAll {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) :
    (∑ s : CoreIdx n, coreColSum g s) = coreAllSum g := by
  unfold coreColSum coreAllSum
  rw [Finset.sum_comm]

lemma sum_coreRow_eq_coreAll {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) :
    (∑ t : CoreIdx n, coreRowSum g t) = coreAllSum g := by
  unfold coreRowSum coreAllSum
  rw [Finset.sum_comm]

lemma rowSum_split_zero_core {n : ℕ} [NeZero n]
    (h : HRaw n) (t : ZMod n) :
    rowSum h t = h (vec2 0 t) + ∑ s : CoreIdx n, h (vec2 s.1 t) := by
  unfold rowSum
  simpa [vec2] using
    (sum_zmod_eq_zero_add_core (n := n) (f := fun s : ZMod n => h (vec2 s t)))

lemma colSum_split_zero_core {n : ℕ} [NeZero n]
    (h : HRaw n) (s : ZMod n) :
    colSum h s = h (vec2 s 0) + ∑ t : CoreIdx n, h (vec2 s t.1) := by
  unfold colSum
  simpa [vec2] using
    (sum_zmod_eq_zero_add_core (n := n) (f := fun t : ZMod n => h (vec2 s t)))

lemma hOfCore_row_zero {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) :
    rowSum (hOfCore g) 0 = 0 := by
  rw [rowSum_split_zero_core]
  rw [hOfCore_at_00]
  have hs :
      (∑ s : CoreIdx n, hOfCore g (vec2 s.1 0))
        = ∑ s : CoreIdx n, coreColSum g s := by
    refine Finset.sum_congr rfl ?_
    intro s _
    simpa [hOfCore_at_s0]
  rw [hs, sum_coreCol_eq_coreAll]
  simpa using F2_add_self (coreAllSum g)

lemma hOfCore_row_nonzero {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) (t : CoreIdx n) :
    rowSum (hOfCore g) t.1 = 0 := by
  rw [rowSum_split_zero_core]
  rw [hOfCore_at_0t]
  have hs :
      (∑ s : CoreIdx n, hOfCore g (vec2 s.1 t.1))
        = ∑ s : CoreIdx n, g s t := by
    refine Finset.sum_congr rfl ?_
    intro s _
    simpa [hOfCore_at_st]
  rw [hs, coreRowSum]
  simpa using F2_add_self (coreRowSum g t)

lemma hOfCore_col_zero {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) :
    colSum (hOfCore g) 0 = 0 := by
  rw [colSum_split_zero_core]
  rw [hOfCore_at_00]
  have ht :
      (∑ t : CoreIdx n, hOfCore g (vec2 0 t.1))
        = ∑ t : CoreIdx n, coreRowSum g t := by
    refine Finset.sum_congr rfl ?_
    intro t _
    simpa [hOfCore_at_0t]
  rw [ht, sum_coreRow_eq_coreAll]
  simpa using F2_add_self (coreAllSum g)

lemma hOfCore_col_nonzero {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) (s : CoreIdx n) :
    colSum (hOfCore g) s.1 = 0 := by
  rw [colSum_split_zero_core]
  rw [hOfCore_at_s0]
  have ht :
      (∑ t : CoreIdx n, hOfCore g (vec2 s.1 t.1))
        = ∑ t : CoreIdx n, g s t := by
    refine Finset.sum_congr rfl ?_
    intro t _
    simpa [hOfCore_at_st]
  rw [ht, coreColSum]
  simpa using F2_add_self (coreColSum g s)

lemma hOfCore_admissible {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) :
    (∀ t : ZMod n, rowSum (hOfCore g) t = 0) ∧
    (∀ s : ZMod n, colSum (hOfCore g) s = 0) := by
  constructor
  · intro t
    by_cases ht : t = 0
    · simpa [ht] using hOfCore_row_zero (n := n) g
    · exact hOfCore_row_nonzero (n := n) g ⟨t, ht⟩
  · intro s
    by_cases hs : s = 0
    · simpa [hs] using hOfCore_col_zero (n := n) g
    · exact hOfCore_col_nonzero (n := n) g ⟨s, hs⟩

def coreOfH {n : ℕ} [NeZero n] (h : HAdmissible n) :
    CoreIdx n → CoreIdx n → F₂ := fun s t => (h : HRaw n) (vec2 s.1 t.1)

lemma coreOfH_hOfCore {n : ℕ} [NeZero n] (g : CoreIdx n → CoreIdx n → F₂) :
    coreOfH (n := n) ⟨hOfCore g, hOfCore_admissible (n := n) g⟩ = g := by
  funext s t
  simp [coreOfH, hOfCore, s.2, t.2]

lemma hAdmissible_h0t_eq_coreRow {n : ℕ} [NeZero n]
    (h : HAdmissible n) (t : CoreIdx n) :
    ((h : HRaw n) (vec2 0 t.1)) = coreRowSum (coreOfH h) t := by
  have hrow := (h.2.1 t.1)
  rw [rowSum_split_zero_core] at hrow
  have hmain :
      (h : HRaw n) (vec2 0 t.1)
        = ∑ s : CoreIdx n, (h : HRaw n) (vec2 s.1 t.1) :=
    (F2_add_eq_zero_iff_eq _ _).1 hrow
  simpa [coreRowSum, coreOfH] using hmain

lemma hAdmissible_hs0_eq_coreCol {n : ℕ} [NeZero n]
    (h : HAdmissible n) (s : CoreIdx n) :
    ((h : HRaw n) (vec2 s.1 0)) = coreColSum (coreOfH h) s := by
  have hcol := (h.2.2 s.1)
  rw [colSum_split_zero_core] at hcol
  have hmain :
      (h : HRaw n) (vec2 s.1 0)
        = ∑ t : CoreIdx n, (h : HRaw n) (vec2 s.1 t.1) :=
    (F2_add_eq_zero_iff_eq _ _).1 hcol
  simpa [coreColSum, coreOfH] using hmain

lemma hAdmissible_h00_eq_coreAll {n : ℕ} [NeZero n]
    (h : HAdmissible n) :
    ((h : HRaw n) (vec2 0 0)) = coreAllSum (coreOfH h) := by
  have hrow := (h.2.1 (0 : ZMod n))
  rw [rowSum_split_zero_core] at hrow
  have h00 :
      (h : HRaw n) (vec2 0 0)
        = ∑ s : CoreIdx n, (h : HRaw n) (vec2 s.1 0) :=
    (F2_add_eq_zero_iff_eq _ _).1 hrow
  rw [h00]
  have hs :
      (∑ s : CoreIdx n, (h : HRaw n) (vec2 s.1 0))
        = ∑ s : CoreIdx n, ∑ t : CoreIdx n, (h : HRaw n) (vec2 s.1 t.1) := by
    refine Finset.sum_congr rfl ?_
    intro s _
    exact hAdmissible_hs0_eq_coreCol (n := n) h s
  rw [hs]
  rfl

lemma hOfCore_coreOfH {n : ℕ} [NeZero n] (h : HAdmissible n) :
    hOfCore (coreOfH h) = (h : HRaw n) := by
  ext p
  by_cases hs : p 0 = 0
  · by_cases ht : p 1 = 0
    · rw [← vec2_eta p]
      simp [hOfCore, hs, ht, hAdmissible_h00_eq_coreAll]
    · rw [← vec2_eta p]
      let t : CoreIdx n := ⟨p 1, ht⟩
      have htEq := hAdmissible_h0t_eq_coreRow (n := n) h t
      simpa [hOfCore, hs, ht, t, coreOfH] using htEq.symm
  · by_cases ht : p 1 = 0
    · rw [← vec2_eta p]
      let s : CoreIdx n := ⟨p 0, hs⟩
      have hsEq := hAdmissible_hs0_eq_coreCol (n := n) h s
      simpa [hOfCore, hs, ht, s, coreOfH] using hsEq.symm
    · rw [← vec2_eta p]
      simp [hOfCore, hs, ht, coreOfH]

def hAdmissibleEquivCore {n : ℕ} [NeZero n] :
    HAdmissible n ≃ (CoreIdx n → CoreIdx n → F₂) where
  toFun := coreOfH
  invFun g := ⟨hOfCore g, hOfCore_admissible (n := n) g⟩
  left_inv h := by
    ext p
    exact congrArg (fun f : HRaw n => f p) (hOfCore_coreOfH (n := n) h)
  right_inv g := coreOfH_hOfCore (n := n) g

@[simp] lemma hAdmissibleEquivCore_apply {n : ℕ} [NeZero n]
    (h : HAdmissible n) :
    hAdmissibleEquivCore (n := n) h = coreOfH h := rfl

@[simp] lemma hAdmissibleEquivCore_symm_apply {n : ℕ} [NeZero n]
    (g : CoreIdx n → CoreIdx n → F₂) :
    (hAdmissibleEquivCore (n := n)).symm g = ⟨hOfCore g, hOfCore_admissible (n := n) g⟩ := rfl

lemma card_CoreIdx {n : ℕ} [NeZero n] :
    Fintype.card (CoreIdx n) = n - 1 := by
  simpa [CoreIdx, ZMod.card] using
    (Fintype.card_subtype_neq (a := (0 : ZMod n)))

lemma sum_zmod_add_right {n : ℕ} [NeZero n] (f : ZMod n → F₂) (a : ZMod n) :
    (∑ x : ZMod n, f (x + a)) = ∑ x : ZMod n, f x := by
  simpa using
    (Fintype.sum_equiv (Equiv.addRight a) (fun x : ZMod n => f (x + a)) (fun x : ZMod n => f x)
      (by intro x; rfl))

lemma sum_zmod_add_diag {n : ℕ} [NeZero n] (f : ZMod n → F₂) :
    (∑ u2 : ZMod n, ∑ u3 : ZMod n, f (u2 + u3)) = (n : F₂) * (∑ z : ZMod n, f z) := by
  have hshift : ∀ u2 : ZMod n, (∑ u3 : ZMod n, f (u2 + u3)) = ∑ z : ZMod n, f z := by
    intro u2
    simpa [add_comm] using sum_zmod_add_right f u2
  calc
    (∑ u2 : ZMod n, ∑ u3 : ZMod n, f (u2 + u3))
        = ∑ u2 : ZMod n, (∑ z : ZMod n, f z) := by
            refine Finset.sum_congr rfl ?_
            intro u2 hu2
            exact hshift u2
    _ = (Fintype.card (ZMod n) : F₂) * (∑ z : ZMod n, f z) := by
          simp [Finset.card_univ]
    _ = (n : F₂) * (∑ z : ZMod n, f z) := by
          simp [ZMod.card]

lemma sum_cKernel_over_addDiag {n : ℕ} [NeZero n] (C : CField n) (a b : ZMod n) :
    (∑ u2 : ZMod n, ∑ u3 : ZMod n, cKernel C (u2 + u3) a b)
      = (n : F₂) * (∑ z : ZMod n, cKernel C z a b) := by
  simpa using (sum_zmod_add_diag (n := n) (f := fun z => cKernel C z a b))

lemma sum_cKernel_over_z_zero {n : ℕ} [NeZero n] (C : CField n) (a b : ZMod n) :
    (∑ z : ZMod n, cKernel C z a b) = 0 := by
  let g : ZMod n → F₂ := fun z => ∑ x1 : ZMod n, C (vec4 x1 a b z)
  have hshift : (∑ z : ZMod n, g (z + 1)) = ∑ z : ZMod n, g z := by
    simpa using sum_zmod_add_right g (1 : ZMod n)
  calc
    (∑ z : ZMod n, cKernel C z a b)
        = (∑ z : ZMod n, g z) + (∑ z : ZMod n, g (z + 1)) := by
            simp [cKernel, g, Finset.sum_add_distrib]
    _ = (∑ z : ZMod n, g z) + (∑ z : ZMod n, g z) := by rw [hshift]
    _ = 0 := by simpa using F2_add_self (∑ z : ZMod n, g z)

lemma sum_cKernel_over_addDiag_zero {n : ℕ} [NeZero n] (C : CField n) (a b : ZMod n) :
    (∑ u2 : ZMod n, ∑ u3 : ZMod n, cKernel C (u2 + u3) a b) = 0 := by
  rw [sum_cKernel_over_addDiag (n := n) C a b, sum_cKernel_over_z_zero (n := n) C a b]
  simp

lemma sum_bKernel_over_z_zero {n : ℕ} [NeZero n] (B : BField n) (u2 u3 : ZMod n) :
    (∑ z : ZMod n, bKernel B z u2 u3) = 0 := by
  let g : ZMod n → F₂ := fun z => ∑ x1 : ZMod n, B (vec4 x1 z u2 u3)
  have hshift : (∑ z : ZMod n, g (z + 1)) = ∑ z : ZMod n, g z := by
    simpa using sum_zmod_add_right g (1 : ZMod n)
  calc
    (∑ z : ZMod n, bKernel B z u2 u3)
        = (∑ z : ZMod n, g z) + (∑ z : ZMod n, g (z + 1)) := by
            simp [bKernel, g, Finset.sum_add_distrib]
    _ = (∑ z : ZMod n, g z) + (∑ z : ZMod n, g z) := by rw [hshift]
    _ = 0 := by simpa using F2_add_self (∑ z : ZMod n, g z)

lemma sum_bKernel_over_addDiag {n : ℕ} [NeZero n] (B : BField n) (u2 u3 : ZMod n) :
    (∑ u0 : ZMod n, ∑ u1 : ZMod n, bKernel B (u0 + u1) u2 u3)
      = (n : F₂) * (∑ z : ZMod n, bKernel B z u2 u3) := by
  simpa using (sum_zmod_add_diag (n := n) (f := fun z => bKernel B z u2 u3))

lemma sum_bKernel_over_addDiag_zero {n : ℕ} [NeZero n] (B : BField n) (u2 u3 : ZMod n) :
    (∑ u0 : ZMod n, ∑ u1 : ZMod n, bKernel B (u0 + u1) u2 u3) = 0 := by
  rw [sum_bKernel_over_addDiag (n := n) B u2 u3, sum_bKernel_over_z_zero (n := n) B u2 u3]
  simp

/-- `bProfileSumConstraint ∘ bProfileLinearMap = 0` from slice-sum cancellation on `bKernel`. -/
lemma bProfileSumConstraint_comp_bProfileLinearMap_eq_zero {n : ℕ} [NeZero n] :
    bProfileSumConstraintLinearMap (n := n) ∘ₗ bProfileLinearMap (n := n) = 0 := by
  refine LinearMap.ext ?_
  intro B
  ext u2 u3
  simpa [LinearMap.comp_apply, bProfileSumConstraintLinearMap, bProfileLinearMap] using
    sum_bKernel_over_z_zero (n := n) B u2 u3

/-- `cProfileSumConstraint ∘ cProfileLinearMap = 0` from slice-sum cancellation on `cKernel`. -/
lemma cProfileSumConstraint_comp_cProfileLinearMap_eq_zero {n : ℕ} [NeZero n] :
    cProfileSumConstraintLinearMap (n := n) ∘ₗ cProfileLinearMap (n := n) = 0 := by
  refine LinearMap.ext ?_
  intro C
  ext u0 u1
  simpa [LinearMap.comp_apply, cProfileSumConstraintLinearMap, cProfileLinearMap] using
    sum_cKernel_over_z_zero (n := n) C u0 u1

lemma range_bProfileLinearMap_le_BProfileAdmSubmodule {n : ℕ} [NeZero n] :
    LinearMap.range (bProfileLinearMap (n := n)) ≤ BProfileAdmSubmodule n :=
  LinearMap.range_le_ker_iff.2 bProfileSumConstraint_comp_bProfileLinearMap_eq_zero

lemma range_cProfileLinearMap_le_CProfileAdmSubmodule {n : ℕ} [NeZero n] :
    LinearMap.range (cProfileLinearMap (n := n)) ≤ CProfileAdmSubmodule n :=
  LinearMap.range_le_ker_iff.2 cProfileSumConstraint_comp_cProfileLinearMap_eq_zero

/-! **Prefix sums on `Fin n` (F₂).** Used to lift admissible profiles to `BField` supported on `x1 = 0`. -/

lemma Fin_sum_Iio_add_sum_Iio_succ {n : ℕ} [NeZero n] (f : Fin n → F₂) (k : Fin n)
    (hf : ∑ i : Fin n, f i = 0) :
    (∑ i ∈ Finset.Iio k, f i) + (∑ i ∈ Finset.Iio (k + 1 : Fin n), f i) = f k := by
  classical
  by_cases h : (k : ℕ) + 1 < n
  · rw [Fin.Iio_add_one_eq_Iic h]
    have hIic : ∑ i ∈ Finset.Iic k, f i = ∑ i ∈ Finset.Iio k, f i + f k := by
      rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons, add_comm]
    rw [hIic, ← add_assoc]
    rw [F2_add_self (∑ i ∈ Finset.Iio k, f i)]
    simp
  · have hkval : k.val = n - 1 := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    have hkval' : k.val = m := by
      simpa [hkval]
    have hk : k = Fin.last m := by
      apply Fin.ext
      simpa [Fin.val_last, hkval']
    have hk1 : k + 1 = (0 : Fin (m + 1)) := by
      rw [hk]
      simp
    rw [hk1]
    have hIio0 : Finset.Iio (0 : Fin (m + 1)) = ∅ := by
      rw [← Fin.bot_eq_zero]
      exact Finset.Iio_bot (α := Fin (m + 1))
    rw [hIio0, Finset.sum_empty, add_zero]
    have hsplit : ∑ i : Fin (m + 1), f i = ∑ i ∈ Finset.Iio k, f i + f k := by
      have hIic : ∑ i ∈ Finset.Iic k, f i = ∑ i ∈ Finset.Iio k, f i + f k := by
        rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons, add_comm]
      have hu : Finset.Iic k = Finset.univ := by
        rw [hk]
        ext i
        simp [Finset.mem_Iic, Finset.mem_univ, Fin.le_last]
      calc
        ∑ i : Fin (m + 1), f i = ∑ i ∈ Finset.univ, f i := by simp
        _ = ∑ i ∈ Finset.Iic k, f i := by rw [← hu]
        _ = ∑ i ∈ Finset.Iio k, f i + f k := hIic
    have hs : ∑ i ∈ Finset.Iio k, f i + f k = 0 := by simpa [hsplit] using hf
    exact (F2_add_eq_zero_iff_eq _ _).1 hs

/-- Lift an admissible `B`-profile to a `BField` supported on `x1 = 0`, using prefix sums in `y`. -/
noncomputable def Bfield_of_admissibleProfile {n : ℕ} [NeZero n] (f : BProfileRaw n)
    (_hf : f ∈ BProfileAdmSubmodule n) : BField n :=
  fun u =>
    if _ : u 0 ≠ 0 then 0 else
      ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm (u 1)), f ((ZMod.finEquiv n) i) (u 2) (u 3)

lemma bKernel_Bfield_of_admissibleProfile {n : ℕ} [NeZero n] (f : BProfileRaw n)
    (hf : f ∈ BProfileAdmSubmodule n) (y u2 u3 : ZMod n) :
    bKernel (Bfield_of_admissibleProfile f hf) y u2 u3 = f y u2 u3 := by
  classical
  unfold bKernel
  rw [Fintype.sum_eq_single (0 : ZMod n) (fun x1 hx => by
    unfold Bfield_of_admissibleProfile
    simp [vec4_zero, vec4_one, vec4_two, vec4_three, hx, add_assoc, add_left_comm, add_comm])]
  have hB0 : Bfield_of_admissibleProfile f hf (vec4 0 y u2 u3) =
      ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm y), f ((ZMod.finEquiv n) i) u2 u3 := by
    unfold Bfield_of_admissibleProfile
    simp [vec4_zero, vec4_one, vec4_two, vec4_three]
  have hB1 : Bfield_of_admissibleProfile f hf (vec4 0 (y + 1) u2 u3) =
      ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm (y + 1)), f ((ZMod.finEquiv n) i) u2 u3 := by
    unfold Bfield_of_admissibleProfile
    simp [vec4_zero, vec4_one, vec4_two, vec4_three]
  rw [hB0, hB1]
  have hfslice : ∑ y' : ZMod n, f y' u2 u3 = 0 :=
    (mem_BProfileAdmSubmodule_iff (n := n) f).1 hf u2 u3
  have hfFin : ∑ i : Fin n, f ((ZMod.finEquiv n) i) u2 u3 = 0 := by
    simpa [← Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun y => f y u2 u3)] using hfslice
  have hsymm : (ZMod.finEquiv n).symm (y + 1) = (ZMod.finEquiv n).symm y + 1 := by
    rcases n with - | n
    · cases NeZero.ne 0 rfl
    simp [ZMod.finEquiv, RingEquiv.map_add, RingEquiv.map_one]
  rw [hsymm]
  simpa [Equiv.apply_symm_apply (ZMod.finEquiv n).toEquiv] using
    Fin_sum_Iio_add_sum_Iio_succ (n := n) (fun i : Fin n => f ((ZMod.finEquiv n) i) u2 u3)
      ((ZMod.finEquiv n).symm y) hfFin

lemma BProfileAdmSubmodule_le_range_bProfileLinearMap {n : ℕ} [NeZero n] :
    BProfileAdmSubmodule n ≤ LinearMap.range (bProfileLinearMap (n := n)) := by
  rintro f hf
  refine ⟨Bfield_of_admissibleProfile f hf, ?_⟩
  ext y u2 u3
  simpa [bProfileLinearMap, Bfield_of_admissibleProfile] using
    bKernel_Bfield_of_admissibleProfile (n := n) f hf y u2 u3

lemma range_bProfileLinearMap_eq_BProfileAdmSubmodule {n : ℕ} [NeZero n] :
    LinearMap.range (bProfileLinearMap (n := n)) = BProfileAdmSubmodule n :=
  le_antisymm range_bProfileLinearMap_le_BProfileAdmSubmodule
    BProfileAdmSubmodule_le_range_bProfileLinearMap

lemma finrank_range_bProfileLinearMap {n : ℕ} [NeZero n] :
    Module.finrank F₂ (LinearMap.range (bProfileLinearMap (n := n))) = n ^ 3 - n ^ 2 := by
  rw [range_bProfileLinearMap_eq_BProfileAdmSubmodule, finrank_BProfileAdmSubmodule]

/-- Same construction for `C` (supported on `x1 = 0`, prefix sums along `z`). -/
noncomputable def Cfield_of_admissibleProfile {n : ℕ} [NeZero n] (f : CProfileRaw n)
    (_hf : f ∈ CProfileAdmSubmodule n) : CField n :=
  fun u =>
    if _ : u 0 ≠ 0 then 0 else
      ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm (u 3)), f ((ZMod.finEquiv n) i) (u 1) (u 2)

lemma cKernel_Cfield_of_admissibleProfile {n : ℕ} [NeZero n] (f : CProfileRaw n)
    (hf : f ∈ CProfileAdmSubmodule n) (z u0 u1 : ZMod n) :
    cKernel (Cfield_of_admissibleProfile f hf) z u0 u1 = f z u0 u1 := by
  classical
  unfold cKernel
  rw [Fintype.sum_eq_single (0 : ZMod n) (fun x1 hx => by
    unfold Cfield_of_admissibleProfile
    simp [vec4_zero, vec4_one, vec4_two, vec4_three, hx, add_assoc, add_left_comm, add_comm])]
  have hC0 : Cfield_of_admissibleProfile f hf (vec4 0 u0 u1 z) =
      ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm z), f ((ZMod.finEquiv n) i) u0 u1 := by
    unfold Cfield_of_admissibleProfile
    simp [vec4_zero, vec4_one, vec4_two, vec4_three]
  have hC1 : Cfield_of_admissibleProfile f hf (vec4 0 u0 u1 (z + 1)) =
      ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm (z + 1)), f ((ZMod.finEquiv n) i) u0 u1 := by
    unfold Cfield_of_admissibleProfile
    simp [vec4_zero, vec4_one, vec4_two, vec4_three]
  rw [hC0, hC1]
  have hfslice : ∑ z' : ZMod n, f z' u0 u1 = 0 :=
    (mem_CProfileAdmSubmodule_iff (n := n) f).1 hf u0 u1
  have hfFin : ∑ i : Fin n, f ((ZMod.finEquiv n) i) u0 u1 = 0 := by
    simpa [← Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun z' => f z' u0 u1)] using hfslice
  have hsymm : (ZMod.finEquiv n).symm (z + 1) = (ZMod.finEquiv n).symm z + 1 := by
    rcases n with - | n
    · cases NeZero.ne 0 rfl
    simp [ZMod.finEquiv, RingEquiv.map_add, RingEquiv.map_one]
  rw [hsymm]
  simpa [Equiv.apply_symm_apply (ZMod.finEquiv n).toEquiv] using
    Fin_sum_Iio_add_sum_Iio_succ (n := n) (fun i : Fin n => f ((ZMod.finEquiv n) i) u0 u1)
      ((ZMod.finEquiv n).symm z) hfFin

lemma CProfileAdmSubmodule_le_range_cProfileLinearMap {n : ℕ} [NeZero n] :
    CProfileAdmSubmodule n ≤ LinearMap.range (cProfileLinearMap (n := n)) := by
  rintro f hf
  refine ⟨Cfield_of_admissibleProfile f hf, ?_⟩
  ext z u0 u1
  simpa [cProfileLinearMap, Cfield_of_admissibleProfile] using
    cKernel_Cfield_of_admissibleProfile (n := n) f hf z u0 u1

lemma range_cProfileLinearMap_eq_CProfileAdmSubmodule {n : ℕ} [NeZero n] :
    LinearMap.range (cProfileLinearMap (n := n)) = CProfileAdmSubmodule n :=
  le_antisymm range_cProfileLinearMap_le_CProfileAdmSubmodule
    CProfileAdmSubmodule_le_range_cProfileLinearMap

lemma finrank_range_cProfileLinearMap {n : ℕ} [NeZero n] :
    Module.finrank F₂ (LinearMap.range (cProfileLinearMap (n := n))) = n ^ 3 - n ^ 2 := by
  rw [range_cProfileLinearMap_eq_CProfileAdmSubmodule, finrank_CProfileAdmSubmodule]

lemma finrank_ker_bProfileLinearMap {n : ℕ} [NeZero n] :
    Module.finrank F₂ (LinearMap.ker (bProfileLinearMap (n := n))) =
      n ^ 4 - (n ^ 3 - n ^ 2) := by
  classical
  let L := bProfileLinearMap (n := n)
  have hsum := LinearMap.finrank_range_add_finrank_ker (V₂ := BProfileRaw n) L
  have hdom : Module.finrank F₂ (BField n) = n ^ 4 := by
    simpa [BField, Module.finrank_pi, Fintype.card_fun]
  have hrng : Module.finrank F₂ (LinearMap.range L) = n ^ 3 - n ^ 2 :=
    finrank_range_bProfileLinearMap (n := n)
  rw [hdom, hrng] at hsum
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hle : n ^ 3 - n ^ 2 ≤ n ^ 4 :=
    le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right hn (by decide : 3 ≤ 4))
  have hker : Module.finrank F₂ (LinearMap.ker L) = n ^ 4 - (n ^ 3 - n ^ 2) := by
    omega
  exact hker

lemma finrank_ker_cProfileLinearMap {n : ℕ} [NeZero n] :
    Module.finrank F₂ (LinearMap.ker (cProfileLinearMap (n := n))) =
      n ^ 4 - (n ^ 3 - n ^ 2) := by
  classical
  let L := cProfileLinearMap (n := n)
  have hsum := LinearMap.finrank_range_add_finrank_ker (V₂ := CProfileRaw n) L
  have hdom : Module.finrank F₂ (CField n) = n ^ 4 := by
    simpa [CField, Module.finrank_pi, Fintype.card_fun]
  have hrng : Module.finrank F₂ (LinearMap.range L) = n ^ 3 - n ^ 2 :=
    finrank_range_cProfileLinearMap (n := n)
  rw [hdom, hrng] at hsum
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hle : n ^ 3 - n ^ 2 ≤ n ^ 4 :=
    le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right hn (by decide : 3 ≤ 4))
  have hker : Module.finrank F₂ (LinearMap.ker L) = n ^ 4 - (n ^ 3 - n ^ 2) := by
    omega
  exact hker

/-- Same as `finrank_ker_bProfileLinearMap`, after expanding `n^4 - (n^3 - n^2)` to `n^4 - n^3 + n^2`. -/
lemma Nat.card_ker_bProfileLinearMap_eq_two_pow {n : ℕ} [NeZero n] :
    Nat.card (↥(LinearMap.ker (bProfileLinearMap (n := n)))) =
      (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) := by
  classical
  calc
    Nat.card (↥(LinearMap.ker (bProfileLinearMap (n := n)))) =
        Nat.card F₂ ^ Module.finrank F₂ (LinearMap.ker (bProfileLinearMap (n := n))) :=
      (Module.natCard_eq_pow_finrank (K := F₂)
        (V := ↥(LinearMap.ker (bProfileLinearMap (n := n)))))
    _ = (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) := by
      rw [finrank_ker_bProfileLinearMap (n := n)]
      simp [F₂]

lemma Nat.card_ker_cProfileLinearMap_eq_two_pow {n : ℕ} [NeZero n] :
    Nat.card (↥(LinearMap.ker (cProfileLinearMap (n := n)))) =
      (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) := by
  classical
  calc
    Nat.card (↥(LinearMap.ker (cProfileLinearMap (n := n)))) =
        Nat.card F₂ ^ Module.finrank F₂ (LinearMap.ker (cProfileLinearMap (n := n))) :=
      (Module.natCard_eq_pow_finrank (K := F₂)
        (V := ↥(LinearMap.ker (cProfileLinearMap (n := n)))))
    _ = (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) := by
      rw [finrank_ker_cProfileLinearMap (n := n)]
      simp [F₂]

lemma Fintype.card_ker_bProfileLinearMap_eq_two_pow {n : ℕ} [NeZero n]
    [Fintype (↥(LinearMap.ker (bProfileLinearMap (n := n))))] :
    Fintype.card (↥(LinearMap.ker (bProfileLinearMap (n := n)))) =
      (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) := by
  classical
  simpa [Nat.card_eq_fintype_card] using Nat.card_ker_bProfileLinearMap_eq_two_pow (n := n)

lemma Fintype.card_ker_cProfileLinearMap_eq_two_pow {n : ℕ} [NeZero n]
    [Fintype (↥(LinearMap.ker (cProfileLinearMap (n := n))))] :
    Fintype.card (↥(LinearMap.ker (cProfileLinearMap (n := n)))) =
      (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) := by
  classical
  simpa [Nat.card_eq_fintype_card] using Nat.card_ker_cProfileLinearMap_eq_two_pow (n := n)

abbrev BProfileFiber {n : ℕ} [NeZero n] (f : BProfileRaw n) :=
  { B : BField n // bProfileLinearMap (n := n) B = f }

abbrev CProfileFiber {n : ℕ} [NeZero n] (f : CProfileRaw n) :=
  { C : CField n // cProfileLinearMap (n := n) C = f }

/-- Final-route alias for the `bProfileLinearMap` fiber. -/
abbrev BProfileFiberStrong {n : ℕ} [NeZero n] (f : BProfileRaw n) := BProfileFiber (n := n) f

/-- Final-route alias for the `cProfileLinearMap` fiber. -/
abbrev CProfileFiberStrong {n : ℕ} [NeZero n] (f : CProfileRaw n) := CProfileFiber (n := n) f

lemma exists_B_of_admissibleBProfile {n : ℕ} [NeZero n] (f : BProfileRaw n)
    (hf : f ∈ BProfileAdmSubmodule n) :
    ∃ B : BField n, bProfileLinearMap (n := n) B = f := by
  exact (BProfileAdmSubmodule_le_range_bProfileLinearMap (n := n)) hf

lemma exists_C_of_admissibleCProfile {n : ℕ} [NeZero n] (f : CProfileRaw n)
    (hf : f ∈ CProfileAdmSubmodule n) :
    ∃ C : CField n, cProfileLinearMap (n := n) C = f := by
  exact (CProfileAdmSubmodule_le_range_cProfileLinearMap (n := n)) hf

lemma BProfileFiber_nonempty_of_admissible {n : ℕ} [NeZero n] (f : BProfileRaw n)
    (hf : f ∈ BProfileAdmSubmodule n) :
    Nonempty (BProfileFiber (n := n) f) := by
  rcases exists_B_of_admissibleBProfile (n := n) f hf with ⟨B, hB⟩
  exact ⟨⟨B, hB⟩⟩

lemma CProfileFiber_nonempty_of_admissible {n : ℕ} [NeZero n] (f : CProfileRaw n)
    (hf : f ∈ CProfileAdmSubmodule n) :
    Nonempty (CProfileFiber (n := n) f) := by
  rcases exists_C_of_admissibleCProfile (n := n) f hf with ⟨C, hC⟩
  exact ⟨⟨C, hC⟩⟩

noncomputable def fiberEquivKer_bProfile {n : ℕ} [NeZero n] (B₀ : BField n) :
    { B : BField n // bProfileLinearMap (n := n) B = bProfileLinearMap B₀ }
      ≃ ↥(LinearMap.ker (bProfileLinearMap (n := n))) where
  toFun := fun ⟨B, hB⟩ =>
    ⟨B + B₀, LinearMap.mem_ker.mpr (by
      rw [LinearMap.map_add, hB]
      ext p1 p2 p3
      simp [Pi.add_apply, F2_add_self])⟩
  invFun := fun ⟨K, hK⟩ =>
    ⟨K + B₀, by
      rw [LinearMap.map_add, LinearMap.mem_ker.mp hK, zero_add]⟩
  left_inv := fun ⟨B, hB⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (B₀ u)]
    simp
  right_inv := fun ⟨K, hK⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (B₀ u)]
    simp

noncomputable def fiberEquivKer_cProfile {n : ℕ} [NeZero n] (C₀ : CField n) :
    { C : CField n // cProfileLinearMap (n := n) C = cProfileLinearMap C₀ }
      ≃ ↥(LinearMap.ker (cProfileLinearMap (n := n))) where
  toFun := fun ⟨C, hC⟩ =>
    ⟨C + C₀, LinearMap.mem_ker.mpr (by
      rw [LinearMap.map_add, hC]
      ext p1 p2 p3
      simp [Pi.add_apply, F2_add_self])⟩
  invFun := fun ⟨K, hK⟩ =>
    ⟨K + C₀, by
      rw [LinearMap.map_add, LinearMap.mem_ker.mp hK, zero_add]⟩
  left_inv := fun ⟨C, hC⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (C₀ u)]
    simp
  right_inv := fun ⟨K, hK⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (C₀ u)]
    simp

lemma Nat.card_BProfileFiber_eq_two_pow_ker {n : ℕ} [NeZero n] (f : BProfileRaw n)
    (hf : f ∈ BProfileAdmSubmodule n) :
    Nat.card (BProfileFiber (n := n) f) =
      (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) := by
  rcases exists_B_of_admissibleBProfile (n := n) f hf with ⟨B₀, hB₀⟩
  calc
    Nat.card (BProfileFiber (n := n) f)
        = Nat.card { B : BField n // bProfileLinearMap (n := n) B = bProfileLinearMap B₀ } := by
          refine Nat.card_congr ?e
          refine
            { toFun := fun x => ⟨x.1, by simpa [hB₀] using x.2⟩
              invFun := fun x => ⟨x.1, by simpa [hB₀] using x.2⟩
              left_inv := by intro x; rfl
              right_inv := by intro x; rfl }
    _ = Nat.card (↥(LinearMap.ker (bProfileLinearMap (n := n)))) := by
          exact Nat.card_congr (fiberEquivKer_bProfile (n := n) B₀)
    _ = (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) :=
          Nat.card_ker_bProfileLinearMap_eq_two_pow (n := n)

lemma Nat.card_CProfileFiber_eq_two_pow_ker {n : ℕ} [NeZero n] (f : CProfileRaw n)
    (hf : f ∈ CProfileAdmSubmodule n) :
    Nat.card (CProfileFiber (n := n) f) =
      (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) := by
  rcases exists_C_of_admissibleCProfile (n := n) f hf with ⟨C₀, hC₀⟩
  calc
    Nat.card (CProfileFiber (n := n) f)
        = Nat.card { C : CField n // cProfileLinearMap (n := n) C = cProfileLinearMap C₀ } := by
          refine Nat.card_congr ?e
          refine
            { toFun := fun x => ⟨x.1, by simpa [hC₀] using x.2⟩
              invFun := fun x => ⟨x.1, by simpa [hC₀] using x.2⟩
              left_inv := by intro x; rfl
              right_inv := by intro x; rfl }
    _ = Nat.card (↥(LinearMap.ker (cProfileLinearMap (n := n)))) := by
          exact Nat.card_congr (fiberEquivKer_cProfile (n := n) C₀)
    _ = (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) :=
          Nat.card_ker_cProfileLinearMap_eq_two_pow (n := n)

theorem Nat.card_BProfileFiberStrong {n : ℕ} [NeZero n] (f : BProfileRaw n)
    (hf : f ∈ BProfileAdmSubmodule n) :
    Nat.card (BProfileFiberStrong (n := n) f) = (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) :=
  Nat.card_BProfileFiber_eq_two_pow_ker (n := n) f hf

theorem Nat.card_CProfileFiberStrong {n : ℕ} [NeZero n] (f : CProfileRaw n)
    (hf : f ∈ CProfileAdmSubmodule n) :
    Nat.card (CProfileFiberStrong (n := n) f) = (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) :=
  Nat.card_CProfileFiber_eq_two_pow_ker (n := n) f hf

abbrev ProfileCompatQuad (n : ℕ) [NeZero n] :=
  { fg : BProfileRaw n × CProfileRaw n //
      fg.1 ∈ BProfileAdmSubmodule n ∧
      fg.2 ∈ CProfileAdmSubmodule n ∧
      ∀ a b u2 u3 : ZMod n, fg.1 (a + b) u2 u3 = fg.2 (u2 + u3) a b }

/-- Final name for the admissible compatible profile pairs. -/
abbrev CompatibleProfiles (n : ℕ) [NeZero n] := ProfileCompatQuad n

abbrev CompatibleProfiles.bPart {n : ℕ} [NeZero n] (fg : CompatibleProfiles n) : BProfileRaw n := fg.1.1
abbrev CompatibleProfiles.cPart {n : ℕ} [NeZero n] (fg : CompatibleProfiles n) : CProfileRaw n := fg.1.2

noncomputable instance instFintypeProfileCompatQuad (n : ℕ) [NeZero n] :
    Fintype (ProfileCompatQuad n) := Fintype.ofFinite _

abbrev ProfileQuadConstraintCodomain (n : ℕ) := ZMod n → ZMod n → ZMod n → ZMod n → F₂

noncomputable def profileCompatToH {n : ℕ} [NeZero n] (fg : ProfileCompatQuad n) : HRaw n :=
  fun p => fg.1.1 (p 0) 0 (p 1)

lemma profileCompat_f_eq_toH_sum {n : ℕ} [NeZero n] (fg : ProfileCompatQuad n)
    (y u2 u3 : ZMod n) :
    fg.1.1 y u2 u3 = profileCompatToH (n := n) fg (vec2 y (u2 + u3)) := by
  have hq := fg.2.2.2
  have h1 : fg.1.1 y u2 u3 = fg.1.2 (u2 + u3) 0 y := by
    simpa using hq 0 y u2 u3
  have h2 : fg.1.1 y 0 (u2 + u3) = fg.1.2 (u2 + u3) 0 y := by
    simpa [add_assoc] using hq 0 y 0 (u2 + u3)
  calc
    fg.1.1 y u2 u3 = fg.1.2 (u2 + u3) 0 y := h1
    _ = fg.1.1 y 0 (u2 + u3) := h2.symm
    _ = profileCompatToH (n := n) fg (vec2 y (u2 + u3)) := by simp [profileCompatToH]

lemma profileCompat_g_eq_toH_sum {n : ℕ} [NeZero n] (fg : ProfileCompatQuad n)
    (z a b : ZMod n) :
    fg.1.2 z a b = profileCompatToH (n := n) fg (vec2 (a + b) z) := by
  have hq := fg.2.2.2
  have h : fg.1.1 (a + b) 0 z = fg.1.2 z a b := by
    simpa [add_assoc, add_comm, add_left_comm] using hq a b 0 z
  calc
    fg.1.2 z a b = fg.1.1 (a + b) 0 z := h.symm
    _ = profileCompatToH (n := n) fg (vec2 (a + b) z) := by simp [profileCompatToH]

lemma profileCompatToH_admissible {n : ℕ} [NeZero n] (fg : ProfileCompatQuad n) :
    (∀ t : ZMod n, rowSum (profileCompatToH (n := n) fg) t = 0) ∧
      (∀ s : ZMod n, colSum (profileCompatToH (n := n) fg) s = 0) := by
  constructor
  · intro t
    have hf := (mem_BProfileAdmSubmodule_iff (n := n) fg.1.1).1 fg.2.1 0 t
    simpa [rowSum, profileCompatToH, vec2] using hf
  · intro s
    have hg := (mem_CProfileAdmSubmodule_iff (n := n) fg.1.2).1 fg.2.2.1 0 s
    have hconvert : (∑ z : ZMod n, fg.1.2 z 0 s) = colSum (profileCompatToH (n := n) fg) s := by
      calc
        (∑ z : ZMod n, fg.1.2 z 0 s)
            = ∑ z : ZMod n, profileCompatToH (n := n) fg (vec2 s z) := by
                refine Finset.sum_congr rfl ?_
                intro z hz
                simpa [profileCompatToH, vec2, add_assoc, add_comm, add_left_comm]
                  using (profileCompat_g_eq_toH_sum (n := n) fg z 0 s)
        _ = colSum (profileCompatToH (n := n) fg) s := by simp [colSum]
    rw [← hconvert]
    exact hg

noncomputable def hToProfileCompat {n : ℕ} [NeZero n] (h : HAdmissible n) : ProfileCompatQuad n := by
  refine ⟨(fun y u2 u3 => (h : HRaw n) (vec2 y (u2 + u3)),
    fun z a b => (h : HRaw n) (vec2 (a + b) z)), ?_, ?_, ?_⟩
  · rw [mem_BProfileAdmSubmodule_iff]
    intro u2 u3
    have hs := h.2.1 (u2 + u3)
    simpa [rowSum, vec2] using hs
  · rw [mem_CProfileAdmSubmodule_iff]
    intro u0 u1
    have hs := h.2.2 (u0 + u1)
    simpa [colSum, vec2, add_assoc, add_left_comm, add_comm] using hs
  · intro a b u2 u3
    rfl

noncomputable def profileCompatQuad_equiv_HAdmissible {n : ℕ} [NeZero n] :
    ProfileCompatQuad n ≃ HAdmissible n where
  toFun fg := ⟨profileCompatToH (n := n) fg, profileCompatToH_admissible (n := n) fg⟩
  invFun h := hToProfileCompat (n := n) h
  left_inv fg := by
    apply Subtype.ext
    apply Prod.ext
    · funext y u2 u3
      simpa [hToProfileCompat] using (profileCompat_f_eq_toH_sum (n := n) fg y u2 u3).symm
    · funext z a b
      simpa [hToProfileCompat] using (profileCompat_g_eq_toH_sum (n := n) fg z a b).symm
  right_inv h := by
    apply Subtype.ext
    funext p
    simpa [profileCompatToH, hToProfileCompat, vec2]

noncomputable def profileCompatConstraintLinearMap {n : ℕ} [NeZero n] :
    (BProfileAdmSubmodule n × CProfileAdmSubmodule n) →ₗ[F₂] ProfileQuadConstraintCodomain n where
  toFun p := fun a b u2 u3 => p.1.1 (a + b) u2 u3 + p.2.1 (u2 + u3) a b
  map_add' p q := by
    ext a b u2 u3
    simp [add_assoc, add_left_comm, add_comm]
  map_smul' r p := by
    ext a b u2 u3
    simp [mul_add]

lemma mem_ker_profileCompatConstraintLinearMap_iff {n : ℕ} [NeZero n]
    (p : BProfileAdmSubmodule n × CProfileAdmSubmodule n) :
    p ∈ LinearMap.ker (profileCompatConstraintLinearMap (n := n)) ↔
      ∀ a b u2 u3 : ZMod n, p.1.1 (a + b) u2 u3 = p.2.1 (u2 + u3) a b := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hp a b u2 u3
    have h := congrArg (fun F => F a b u2 u3) hp
    exact (F2_add_eq_zero_iff_eq _ _).1 h
  · intro hp
    ext a b u2 u3
    exact (F2_add_eq_zero_iff_eq _ _).2 (hp a b u2 u3)

noncomputable def profileCompatQuad_equiv_kernel {n : ℕ} [NeZero n] :
    ProfileCompatQuad n ≃ ↥(LinearMap.ker (profileCompatConstraintLinearMap (n := n))) where
  toFun x := by
    rcases x with ⟨⟨f, g⟩, hfadm, hcadm, hq⟩
    refine ⟨⟨⟨f, hfadm⟩, ⟨g, hcadm⟩⟩, ?_⟩
    exact (mem_ker_profileCompatConstraintLinearMap_iff (n := n) ⟨⟨f, hfadm⟩, ⟨g, hcadm⟩⟩).2 hq
  invFun x := by
    rcases x with ⟨⟨f, g⟩, hk⟩
    refine ⟨⟨f.1, g.1⟩, f.2, g.2, ?_⟩
    exact (mem_ker_profileCompatConstraintLinearMap_iff (n := n) ⟨f, g⟩).1 hk
  left_inv x := by
    rcases x with ⟨⟨f, g⟩, hfadm, hcadm, hq⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨f, g⟩, hk⟩
    rfl

lemma Nat.card_profileCompatQuad_eq_card_ker_profileCompatConstraintLinearMap
    {n : ℕ} [NeZero n] :
    Nat.card (ProfileCompatQuad n) =
      Nat.card (↥(LinearMap.ker (profileCompatConstraintLinearMap (n := n)))) :=
  Nat.card_congr (profileCompatQuad_equiv_kernel (n := n))

set_option synthInstance.maxHeartbeats 200000 in
-- `Module.natCard_eq_pow_finrank` over this kernel triggers expensive instance search in this file.
lemma Nat.card_profileCompatQuad_eq_two_pow_finrank_ker {n : ℕ} [NeZero n] :
    Nat.card (ProfileCompatQuad n) =
      (2 : ℕ) ^ Module.finrank F₂ (LinearMap.ker (profileCompatConstraintLinearMap (n := n))) := by
  rw [Nat.card_profileCompatQuad_eq_card_ker_profileCompatConstraintLinearMap (n := n)]
  simpa [F₂] using
    (Module.natCard_eq_pow_finrank (K := F₂)
      (V := ↥(LinearMap.ker (profileCompatConstraintLinearMap (n := n)))))

abbrev SurvivingProfileFibers (n : ℕ) [NeZero n] :=
  Σ fg : ProfileCompatQuad n, BProfileFiber (n := n) fg.1.1 × CProfileFiber (n := n) fg.1.2

/-- Final sigma-object used in the assumption-free counting route. -/
abbrev SurvivingSigmaStrong (n : ℕ) [NeZero n] :=
  Σ fg : CompatibleProfiles n,
    BProfileFiberStrong (n := n) fg.bPart × CProfileFiberStrong (n := n) fg.cPart

noncomputable def survivingBCKernelQuad_equiv_profileFibers {n : ℕ} [NeZero n] :
    SurvivingBCKernelQuad n ≃ SurvivingProfileFibers n where
  toFun := by
    intro p
    rcases p with ⟨⟨B, C⟩, hp⟩
    have hbadm : bProfileLinearMap (n := n) B ∈ BProfileAdmSubmodule n := by
      exact range_bProfileLinearMap_le_BProfileAdmSubmodule
        (LinearMap.mem_range.2 ⟨B, rfl⟩)
    have hcadm : cProfileLinearMap (n := n) C ∈ CProfileAdmSubmodule n := by
      exact range_cProfileLinearMap_le_CProfileAdmSubmodule
        (LinearMap.mem_range.2 ⟨C, rfl⟩)
    refine ⟨⟨(bProfileLinearMap (n := n) B, cProfileLinearMap (n := n) C), hbadm, hcadm, ?_⟩,
      ⟨⟨B, rfl⟩, ⟨C, rfl⟩⟩⟩
    intro a b u2 u3
    simpa [bProfileLinearMap, cProfileLinearMap] using hp a b u2 u3
  invFun := by
    intro x
    rcases x with ⟨⟨⟨f, g⟩, hfadm, hcadm, hq⟩, ⟨B, hB⟩, ⟨C, hC⟩⟩
    refine ⟨⟨B, C⟩, ?_⟩
    intro a b u2 u3
    calc
      bKernel B (a + b) u2 u3 = bProfileLinearMap (n := n) B (a + b) u2 u3 := rfl
      _ = f (a + b) u2 u3 := by simpa [hB]
      _ = g (u2 + u3) a b := hq a b u2 u3
      _ = cProfileLinearMap (n := n) C (u2 + u3) a b := by simpa [hC]
      _ = cKernel C (u2 + u3) a b := rfl
  left_inv := by
    intro p
    rcases p with ⟨⟨B, C⟩, hp⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨⟨f, g⟩, hfadm, hcadm, hq⟩, ⟨B, hB⟩, ⟨C, hC⟩⟩
    have hB' : f = bProfileLinearMap (n := n) B := hB.symm
    have hC' : g = cProfileLinearMap (n := n) C := hC.symm
    subst f
    subst g
    simp

noncomputable def survivingBC_equiv_sigmaStrong {n : ℕ} [NeZero n] :
    SurvivingBC n ≃ SurvivingSigmaStrong n :=
  (survivingBC_equiv_kernel (n := n)).trans
    ((survivingBCKernel_equiv_quad (n := n)).trans
      (survivingBCKernelQuad_equiv_profileFibers (n := n)))

lemma Nat.card_survivingBC_eq_card_sigmaStrong {n : ℕ} [NeZero n] :
    Nat.card (SurvivingBC n) = Nat.card (SurvivingSigmaStrong n) :=
  Nat.card_congr (survivingBC_equiv_sigmaStrong (n := n))

lemma Fintype.card_survivingBC_eq_card_sigmaStrong {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingSigmaStrong n) :=
  Fintype.card_congr (survivingBC_equiv_sigmaStrong (n := n))

lemma Nat.card_survivingBCKernelQuad_eq_profileFibers {n : ℕ} [NeZero n] :
    Nat.card (SurvivingBCKernelQuad n) = Nat.card (SurvivingProfileFibers n) :=
  Nat.card_congr (survivingBCKernelQuad_equiv_profileFibers (n := n))

lemma Nat.card_survivingProfileFibers_eq_sum_profileFiberProducts {n : ℕ} [NeZero n] :
    Nat.card (SurvivingProfileFibers n)
      = ∑ fg : ProfileCompatQuad n,
          Nat.card (BProfileFiber (n := n) fg.1.1) * Nat.card (CProfileFiber (n := n) fg.1.2) := by
  simpa [SurvivingProfileFibers, Nat.card_prod] using
    (Nat.card_sigma
      (β := fun fg : ProfileCompatQuad n =>
        BProfileFiber (n := n) fg.1.1 × CProfileFiber (n := n) fg.1.2))

lemma Nat.card_survivingSigmaStrong_eq_sum_profileFiberStrongProducts {n : ℕ} [NeZero n] :
    Nat.card (SurvivingSigmaStrong n)
      = ∑ fg : CompatibleProfiles n,
          Nat.card (BProfileFiberStrong (n := n) fg.bPart) *
            Nat.card (CProfileFiberStrong (n := n) fg.cPart) := by
  simpa [SurvivingSigmaStrong, CompatibleProfiles.bPart, CompatibleProfiles.cPart, Nat.card_prod] using
    (Nat.card_sigma
      (β := fun fg : CompatibleProfiles n =>
        BProfileFiberStrong (n := n) fg.bPart × CProfileFiberStrong (n := n) fg.cPart))

lemma Nat.card_profileFiber_product_eq_pow_const {n : ℕ} [NeZero n] (fg : ProfileCompatQuad n) :
    Nat.card (BProfileFiber (n := n) fg.1.1) * Nat.card (CProfileFiber (n := n) fg.1.2)
      = (2 : ℕ) ^ (2 * (n ^ 4 - (n ^ 3 - n ^ 2))) := by
  have hB :
      Nat.card (BProfileFiber (n := n) fg.1.1) = (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) :=
    Nat.card_BProfileFiber_eq_two_pow_ker (n := n) fg.1.1 fg.2.1
  have hC :
      Nat.card (CProfileFiber (n := n) fg.1.2) = (2 : ℕ) ^ (n ^ 4 - (n ^ 3 - n ^ 2)) :=
    Nat.card_CProfileFiber_eq_two_pow_ker (n := n) fg.1.2 fg.2.2.1
  rw [hB, hC, ← Nat.pow_add]
  congr 1
  omega

lemma Nat.card_profileFiberStrong_product_constant {n : ℕ} [NeZero n] (fg : CompatibleProfiles n) :
    Nat.card (BProfileFiberStrong (n := n) fg.bPart) *
        Nat.card (CProfileFiberStrong (n := n) fg.cPart)
      = (2 : ℕ) ^ (2 * (n ^ 4 - (n ^ 3 - n ^ 2))) := by
  simpa [CompatibleProfiles.bPart, CompatibleProfiles.cPart] using
    Nat.card_profileFiber_product_eq_pow_const (n := n) fg

lemma Nat.card_survivingProfileFibers_eq_card_profileCompat_mul_pow {n : ℕ} [NeZero n] :
    Nat.card (SurvivingProfileFibers n)
      = Nat.card (ProfileCompatQuad n) * (2 : ℕ) ^ (2 * (n ^ 4 - (n ^ 3 - n ^ 2))) := by
  rw [Nat.card_survivingProfileFibers_eq_sum_profileFiberProducts (n := n)]
  simp_rw [Nat.card_profileFiber_product_eq_pow_const (n := n)]
  rw [Finset.sum_const_nat (s := Finset.univ)
    (f := fun _ : ProfileCompatQuad n => (2 : ℕ) ^ (2 * (n ^ 4 - (n ^ 3 - n ^ 2))))
    (m := (2 : ℕ) ^ (2 * (n ^ 4 - (n ^ 3 - n ^ 2))))
    (by intro _ _; rfl),
    Finset.card_univ]
  simp [Nat.card_eq_fintype_card]

lemma Nat.card_survivingSigmaStrong_eq_card_CompatibleProfiles_mul_pow {n : ℕ} [NeZero n] :
    Nat.card (SurvivingSigmaStrong n)
      = Nat.card (CompatibleProfiles n) * (2 : ℕ) ^ (2 * (n ^ 4 - (n ^ 3 - n ^ 2))) := by
  rw [Nat.card_survivingSigmaStrong_eq_sum_profileFiberStrongProducts (n := n)]
  simp_rw [Nat.card_profileFiberStrong_product_constant (n := n)]
  rw [Finset.sum_const_nat (s := Finset.univ)
    (f := fun _ : CompatibleProfiles n => (2 : ℕ) ^ (2 * (n ^ 4 - (n ^ 3 - n ^ 2))))
    (m := (2 : ℕ) ^ (2 * (n ^ 4 - (n ^ 3 - n ^ 2))))
    (by intro _ _; rfl),
    Finset.card_univ]
  simp [Nat.card_eq_fintype_card]

lemma Nat.card_survivingBCKernelQuad_eq_card_profileCompat_mul_pow {n : ℕ} [NeZero n] :
    Nat.card (SurvivingBCKernelQuad n)
      = Nat.card (ProfileCompatQuad n) * (2 : ℕ) ^ (2 * (n ^ 4 - (n ^ 3 - n ^ 2))) := by
  rw [Nat.card_survivingBCKernelQuad_eq_profileFibers (n := n),
    Nat.card_survivingProfileFibers_eq_card_profileCompat_mul_pow (n := n)]

lemma Nat.card_survivingBCKernelQuad_eq_two_pow_finrank_profileCompatKer {n : ℕ} [NeZero n] :
    Nat.card (SurvivingBCKernelQuad n) =
      (2 : ℕ) ^
        (Module.finrank F₂ (LinearMap.ker (profileCompatConstraintLinearMap (n := n))) +
          2 * (n ^ 4 - (n ^ 3 - n ^ 2))) := by
  rw [Nat.card_survivingBCKernelQuad_eq_card_profileCompat_mul_pow (n := n),
    Nat.card_profileCompatQuad_eq_two_pow_finrank_ker (n := n), ← Nat.pow_add]

lemma Nat.card_survivingBCKernel_eq_two_pow_finrank_profileCompatKer {n : ℕ} [NeZero n] :
    Nat.card (SurvivingBCKernel n) =
      (2 : ℕ) ^
        (Module.finrank F₂ (LinearMap.ker (profileCompatConstraintLinearMap (n := n))) +
          2 * (n ^ 4 - (n ^ 3 - n ^ 2))) := by
  calc
    Nat.card (SurvivingBCKernel n) = Nat.card (SurvivingBCKernelQuad n) := by
      exact Nat.card_congr (survivingBCKernel_equiv_quad (n := n))
    _ = (2 : ℕ) ^
        (Module.finrank F₂ (LinearMap.ker (profileCompatConstraintLinearMap (n := n))) +
          2 * (n ^ 4 - (n ^ 3 - n ^ 2))) :=
      Nat.card_survivingBCKernelQuad_eq_two_pow_finrank_profileCompatKer (n := n)

lemma Nat.card_survivingBC_eq_two_pow_finrank_profileCompatKer {n : ℕ} [NeZero n] :
    Nat.card (SurvivingBC n) =
      (2 : ℕ) ^
        (Module.finrank F₂ (LinearMap.ker (profileCompatConstraintLinearMap (n := n))) +
          2 * (n ^ 4 - (n ^ 3 - n ^ 2))) := by
  calc
    Nat.card (SurvivingBC n) = Nat.card (SurvivingBCKernel n) := by
      exact Nat.card_congr (survivingBC_equiv_kernel (n := n))
    _ = (2 : ℕ) ^
        (Module.finrank F₂ (LinearMap.ker (profileCompatConstraintLinearMap (n := n))) +
          2 * (n ^ 4 - (n ^ 3 - n ^ 2))) :=
      Nat.card_survivingBCKernel_eq_two_pow_finrank_profileCompatKer (n := n)

set_option synthInstance.maxHeartbeats 200000 in
-- The same kernel-finrank expression reappears here and needs the larger instance-search budget.
theorem deltaNo13Raw_eq_two_pow_profileCompatKer {n : ℕ} [NeZero n] :
    deltaNo13Raw n =
      (2 : ℤ) ^
        (n ^ 4 + (Module.finrank F₂ (LinearMap.ker (profileCompatConstraintLinearMap (n := n))) +
          2 * (n ^ 4 - (n ^ 3 - n ^ 2)))) := by
  rw [deltaNo13Raw_eq_survivingBC_card]
  have hcardNat := Nat.card_survivingBC_eq_two_pow_finrank_profileCompatKer (n := n)
  have hcardFin :
      Fintype.card (SurvivingBC n) =
        (2 : ℕ) ^
          (Module.finrank F₂ (LinearMap.ker (profileCompatConstraintLinearMap (n := n))) +
            2 * (n ^ 4 - (n ^ 3 - n ^ 2))) := by
    simpa [Nat.card_eq_fintype_card] using hcardNat
  have hcardInt :
      (Fintype.card (SurvivingBC n) : ℤ) =
        (2 : ℤ) ^
          (Module.finrank F₂ (LinearMap.ker (profileCompatConstraintLinearMap (n := n))) +
            2 * (n ^ 4 - (n ^ 3 - n ^ 2))) := by
    exact_mod_cast hcardFin
  rw [hcardInt, ← pow_add]

/-- Coefficient vanishing (`coeffFromBC = 0`) forces slice agreement: its linear kernel embeds in
the slice-difference kernel (`bSlice = cSlice` entrywise). -/
lemma ker_coeffFromBC_le_ker_sliceDiff {n : ℕ} [NeZero n] :
    LinearMap.ker (coeffFromBCLinearMap (n := n)) ≤
      LinearMap.ker (sliceDiffLinearMap (n := n)) := by
  rintro ⟨B, C⟩ hbc
  rw [mem_ker_coeffFromBCLinearMap_iff] at hbc
  rw [mem_ker_sliceDiffLinearMap_iff]
  intro t
  have hker := (coeffFromBC_eq_zero_iff_kernels_eq (n := n) B C).1 hbc
  have hz : bSlice B t = 0 := by
    rw [← zero_add t, kernel_implies_bSlice_via_cKernel (n := n) B C hker 0 t,
      sum_cKernel_over_addDiag_zero (n := n) C 0 t]
  have hz' : cSlice C t = 0 := by
    rw [← zero_add t, kernel_implies_cSlice_via_bKernel (n := n) B C hker 0 t,
      sum_bKernel_over_addDiag_zero (n := n) B 0 t]
  rw [hz, hz']

/-! ## `n = 1` (`ZMod 1` trivial): maps vanish; `Ker coeff = Ker slice = ⊤`

For general `n`, the Quad/Slice cardinality bridge is the explicit hypothesis `QuadSliceCardHyp n`
(see Phase 1 later in this file). -/

lemma zmod_one_eq_zero (a : ZMod 1) : a = 0 :=
  Subsingleton.elim a 0

lemma zmod_one_add_one_eq_zero : (1 : ZMod 1) = 0 :=
  zmod_one_eq_zero 1

lemma zmod_one_add_eq_self (a : ZMod 1) : a + 1 = a := by
  rw [zmod_one_add_one_eq_zero, add_zero]

lemma vec4_bSlice_pair_zmod1 (x1 y u2 u3 : ZMod 1) :
    vec4 x1 (y + 1) u2 u3 = vec4 x1 y u2 u3 := by
  simpa using congrArg (fun t : ZMod 1 => vec4 x1 t u2 u3) (zmod_one_add_eq_self y)

lemma vec4_cSlice_pair_zmod1 (x1 u0 u1 z : ZMod 1) :
    vec4 x1 u0 u1 (z + 1) = vec4 x1 u0 u1 z := by
  simpa using congrArg (fun t : ZMod 1 => vec4 x1 u0 u1 t) (zmod_one_add_eq_self z)

lemma bKernel_zmod_one_zero (B : BField 1) (y u2 u3 : ZMod 1) : bKernel B y u2 u3 = 0 := by
  unfold bKernel
  refine Finset.sum_eq_zero ?_
  intro x1 _
  rw [vec4_bSlice_pair_zmod1 x1 y u2 u3, F2_add_self]

lemma cKernel_zmod_one_zero (C : CField 1) (z u0 u1 : ZMod 1) : cKernel C z u0 u1 = 0 := by
  unfold cKernel
  refine Finset.sum_eq_zero ?_
  intro x1 _
  rw [vec4_cSlice_pair_zmod1 x1 u0 u1 z, F2_add_self]

lemma coeffFromBC_zmod_one_zero (B : BField 1) (C : CField 1) (u : T4 1) :
    coeffFromBC B C u = 0 := by
  rw [coeffFromBC_eq_kernels (n := (1 : ℕ)) B C u]
  rw [bKernel_zmod_one_zero B (u 0 + u 1) (u 2) (u 3)]
  rw [cKernel_zmod_one_zero C (u 2 + u 3) (u 0) (u 1)]
  simp

lemma bSlice_zmod_one_zero (B : BField 1) (y : ZMod 1) : bSlice B y = 0 := by
  unfold bSlice
  refine Finset.sum_eq_zero ?_
  intro x1 _
  refine Finset.sum_eq_zero ?_
  intro u2 _
  refine Finset.sum_eq_zero ?_
  intro u3 _
  rw [vec4_bSlice_pair_zmod1 x1 y u2 u3, F2_add_self]

lemma cSlice_zmod_one_zero (C : CField 1) (z : ZMod 1) : cSlice C z = 0 := by
  unfold cSlice
  refine Finset.sum_eq_zero ?_
  intro x1 _
  refine Finset.sum_eq_zero ?_
  intro u0 _
  refine Finset.sum_eq_zero ?_
  intro u1 _
  rw [vec4_cSlice_pair_zmod1 x1 u0 u1 z, F2_add_self]

lemma coeffFromBCLinearMap_eq_zero_one (bc : BField 1 × CField 1) :
    coeffFromBCLinearMap (n := (1 : ℕ)) bc = 0 := by
  rcases bc with ⟨B, C⟩
  funext u
  simpa [coeffFromBCLinearMap] using coeffFromBC_zmod_one_zero B C u

lemma sliceDiffLinearMap_eq_zero_one (bc : BField 1 × CField 1) :
    sliceDiffLinearMap (n := (1 : ℕ)) bc = 0 := by
  rcases bc with ⟨B, C⟩
  funext t
  simp [sliceDiffLinearMap, bSlice_zmod_one_zero, cSlice_zmod_one_zero]

lemma LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_one :
    LinearMap.ker (coeffFromBCLinearMap (n := (1 : ℕ))) =
      LinearMap.ker (sliceDiffLinearMap (n := (1 : ℕ))) := by
  refine le_antisymm (ker_coeffFromBC_le_ker_sliceDiff (n := (1 : ℕ))) ?_
  intro bc _
  exact LinearMap.mem_ker.mpr (coeffFromBCLinearMap_eq_zero_one bc)

noncomputable def BtoU {n : ℕ} [NeZero n] (B : BField n) : HRaw n :=
  fun p =>
    ∑ u2 : ZMod n, ∑ u3 : ZMod n, ∑ x1 : ZMod n,
      (B (vec4 x1 (p 0 + p 1) u2 u3) + B (vec4 x1 (p 0 + p 1 + 1) u2 u3))

noncomputable def CtoV {n : ℕ} [NeZero n] (C : CField n) : HRaw n :=
  fun p =>
    ∑ u0 : ZMod n, ∑ u1 : ZMod n, ∑ x1 : ZMod n,
      (C (vec4 x1 u0 u1 (p 0 + p 1)) + C (vec4 x1 u0 u1 (p 0 + p 1 + 1)))

lemma BtoU_eq_bSlice {n : ℕ} [NeZero n] (B : BField n) (p : T2 n) :
    BtoU B p = bSlice B (p 0 + p 1) := by
  unfold BtoU bSlice
  simpa using
    (sum_reorder_three (n := n)
      (f := fun x1 u2 u3 =>
        B (vec4 x1 (p 0 + p 1) u2 u3) + B (vec4 x1 (p 0 + p 1 + 1) u2 u3)))

lemma CtoV_eq_cSlice {n : ℕ} [NeZero n] (C : CField n) (p : T2 n) :
    CtoV C p = cSlice C (p 0 + p 1) := by
  unfold CtoV cSlice
  simpa using
    (sum_reorder_three (n := n)
      (f := fun x1 u0 u1 =>
        C (vec4 x1 u0 u1 (p 0 + p 1)) + C (vec4 x1 u0 u1 (p 0 + p 1 + 1))))

lemma BtoU_add {n : ℕ} [NeZero n] (B1 B2 : BField n) : BtoU (B1 + B2) = BtoU B1 + BtoU B2 := by
  funext p
  simpa [BtoU_eq_bSlice (n := n)] using (bSlice_add (n := n) B1 B2 ((p 0) + (p 1)))

lemma CtoV_add {n : ℕ} [NeZero n] (C1 C2 : CField n) : CtoV (C1 + C2) = CtoV C1 + CtoV C2 := by
  funext p
  simpa [CtoV_eq_cSlice (n := n)] using (cSlice_add (n := n) C1 C2 ((p 0) + (p 1)))

lemma BtoU_zero {n : ℕ} [NeZero n] : BtoU (0 : BField n) = 0 := by
  funext p
  simpa [BtoU_eq_bSlice] using (bSlice_zero (n := n) (y := (p 0) + (p 1)))

lemma CtoV_zero {n : ℕ} [NeZero n] : CtoV (0 : CField n) = 0 := by
  funext p
  simpa [CtoV_eq_cSlice] using (cSlice_zero (n := n) (z := (p 0) + (p 1)))

lemma BtoU_smul {n : ℕ} [NeZero n] (r : F₂) (B : BField n) : BtoU (r • B) = r • BtoU B := by
  funext p
  simpa [BtoU_eq_bSlice, Pi.smul_apply] using (bSlice_smul (n := n) r B ((p 0) + (p 1)))

lemma CtoV_smul {n : ℕ} [NeZero n] (r : F₂) (C : CField n) : CtoV (r • C) = r • CtoV C := by
  funext p
  simpa [CtoV_eq_cSlice, Pi.smul_apply] using (cSlice_smul (n := n) r C ((p 0) + (p 1)))

/-- `B ↦ BtoU B` is `F₂`-linear (fiber cardinality = `|ker|` when nonempty). -/
noncomputable def bToULinearMap {n : ℕ} [NeZero n] : BField n →ₗ[F₂] HRaw n where
  toFun := BtoU
  map_add' := BtoU_add
  map_smul' := BtoU_smul

/-- `C ↦ CtoV C` is `F₂`-linear. -/
noncomputable def cToVLinearMap {n : ℕ} [NeZero n] : CField n →ₗ[F₂] HRaw n where
  toFun := CtoV
  map_add' := CtoV_add
  map_smul' := CtoV_smul

lemma bToULinearMap_apply {n : ℕ} [NeZero n] (B : BField n) : bToULinearMap (n := n) B = BtoU B :=
  rfl

lemma cToVLinearMap_apply {n : ℕ} [NeZero n] (C : CField n) : cToVLinearMap (n := n) C = CtoV C :=
  rfl

lemma BtoU_eq_CtoV_iff_slices {n : ℕ} [NeZero n] (B : BField n) (C : CField n) :
    BtoU B = CtoV C ↔
      ∀ p : T2 n, bSlice B (p 0 + p 1) = cSlice C (p 0 + p 1) := by
  constructor
  · intro h p
    have hp := congrArg (fun hraw : HRaw n => hraw p) h
    simpa [BtoU_eq_bSlice, CtoV_eq_cSlice] using hp
  · intro h
    ext p
    simpa [BtoU_eq_bSlice, CtoV_eq_cSlice] using h p

/-- Slice-form structural surviving set. -/
abbrev SurvivingBCSlice (n : ℕ) [NeZero n] :=
  { p : BField n × CField n //
      ∀ q : T2 n, bSlice p.1 (q 0 + q 1) = cSlice p.2 (q 0 + q 1) }

/-- Explicit RHS used in older drafts: `∑_{u2,u3} cKernel (u2+u3) a b` scalarizes and sums to `0`,
so it is **not** equivalent to matching `cSlice` unless one revises the bridge. -/
lemma sliceViaCKernel_eq_scalarized {n : ℕ} [NeZero n] (B : BField n) (C : CField n) :
    (∀ a b : ZMod n,
      bSlice B (a + b) = ∑ u2 : ZMod n, ∑ u3 : ZMod n, cKernel C (u2 + u3) a b) ↔
    (∀ a b : ZMod n,
      bSlice B (a + b) = (n : F₂) * (∑ z : ZMod n, cKernel C z a b)) := by
  constructor
  · intro h a b
    rw [h a b, sum_cKernel_over_addDiag (n := n) C a b]
  · intro h a b
    rw [sum_cKernel_over_addDiag (n := n) C a b, h a b]

lemma sliceViaCKernel_iff_bSlice_zero {n : ℕ} [NeZero n] (B : BField n) (C : CField n) :
    (∀ a b : ZMod n,
      bSlice B (a + b) = ∑ u2 : ZMod n, ∑ u3 : ZMod n, cKernel C (u2 + u3) a b) ↔
    (∀ a b : ZMod n, bSlice B (a + b) = 0) := by
  constructor
  · intro h a b
    rw [h a b, sum_cKernel_over_addDiag_zero (n := n) C a b]
  · intro h a b
    rw [h a b, sum_cKernel_over_addDiag_zero (n := n) C a b]

lemma bSlice_zero_field {n : ℕ} [NeZero n] (a b : ZMod n) :
    bSlice (0 : BField n) (a + b) = 0 := by
  simp [bSlice]

lemma card_survivingBCKernelQuad_le_card_prod {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCKernelQuad n) ≤ Fintype.card (BField n × CField n) := by
  let f : SurvivingBCKernelQuad n → BField n × CField n := fun p => p.val
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext hxy
  exact Fintype.card_le_of_injective f hf

lemma card_survivingBC_le_card_prod {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBC n) ≤ Fintype.card (BField n × CField n) := by
  let f : SurvivingBC n → BField n × CField n := fun p => p.val
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext hxy
  exact Fintype.card_le_of_injective f hf

lemma card_survivingBCKernel_le_card_prod {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCKernel n) ≤ Fintype.card (BField n × CField n) := by
  calc
    Fintype.card (SurvivingBCKernel n) = Fintype.card (SurvivingBCKernelQuad n) := by
      exact Fintype.card_congr (survivingBCKernel_equiv_quad (n := n))
    _ ≤ Fintype.card (BField n × CField n) := card_survivingBCKernelQuad_le_card_prod (n := n)

lemma card_survivingBCKernel_eq_card_survivingBC {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCKernel n) = Fintype.card (SurvivingBC n) := by
  symm
  exact Fintype.card_congr (survivingBC_equiv_kernel (n := n))

lemma slices_eq_on_pairs_iff_all {n : ℕ} [NeZero n] (B : BField n) (C : CField n) :
    (∀ q : T2 n, bSlice B (q 0 + q 1) = cSlice C (q 0 + q 1)) ↔
      (∀ t : ZMod n, bSlice B t = cSlice C t) := by
  constructor
  · intro h t
    simpa using h (vec2 t 0)
  · intro h q
    exact h (q 0 + q 1)

abbrev SurvivingBCDiag (n : ℕ) [NeZero n] :=
  { p : BField n × CField n // ∀ t : ZMod n, bSlice p.1 t = cSlice p.2 t }

/-- Diagonal slice matching: the `F₂`-linear kernel of per-coordinate `bSlice + cSlice`. -/
noncomputable def survivingBCDiag_equiv_ker_sliceDiffLinearMap {n : ℕ} [NeZero n] :
    SurvivingBCDiag n ≃ LinearMap.ker (sliceDiffLinearMap (n := n)) where
  toFun p := by
    rcases p with ⟨⟨B, C⟩, h⟩
    refine ⟨(B, C), ?_⟩
    rw [LinearMap.mem_ker]
    funext t
    simp [sliceDiffLinearMap, Pi.add_apply]
    rw [h t]
    simpa using F2_add_self (cSlice C t)
  invFun p := by
    rcases p with ⟨⟨B, C⟩, hbc⟩
    refine ⟨⟨B, C⟩, ?_⟩
    intro t
    have ht : bSlice B t + cSlice C t = 0 := by
      simpa [sliceDiffLinearMap, Pi.add_apply] using congr_fun hbc t
    exact (F2_add_eq_zero_iff_eq _ _).1 ht
  left_inv p := by
    rcases p with ⟨⟨B, C⟩, _⟩
    rfl
  right_inv p := by
    rcases p with ⟨⟨B, C⟩, _⟩
    rfl

/-- Quad kernel conditions force both `bSlice` and `cSlice` to vanish, hence slice matching. -/
lemma survivingBCKernelQuad_bSlice_eq_cSlice {n : ℕ} [NeZero n] (p : SurvivingBCKernelQuad n) :
    ∀ t : ZMod n, bSlice p.val.1 t = cSlice p.val.2 t := by
  rcases p with ⟨⟨B, C⟩, hquad⟩
  have hker :
      ∀ u : T4 n, bKernel B (u 0 + u 1) (u 2) (u 3) = cKernel C (u 2 + u 3) (u 0) (u 1) := by
    intro u
    simpa using hquad (u 0) (u 1) (u 2) (u 3)
  intro t
  have hB := kernel_implies_bSlice_via_cKernel (n := n) B C hker
  have hC := kernel_implies_cSlice_via_bKernel (n := n) B C hker
  have hz : bSlice B t = 0 := by
    rw [← zero_add t, hB 0 t, sum_cKernel_over_addDiag_zero (n := n) C 0 t]
  have hz' : cSlice C t = 0 := by
    rw [← zero_add t, hC 0 t, sum_bKernel_over_addDiag_zero (n := n) B 0 t]
  rw [hz, hz']

/-- Natural inclusion `SurvivingBCKernelQuad ↪ SurvivingBCDiag`. -/
noncomputable def survivingBCKernelQuadEmbeddingDiag {n : ℕ} [NeZero n]
    (p : SurvivingBCKernelQuad n) : SurvivingBCDiag n :=
  ⟨⟨p.val.1, p.val.2⟩, survivingBCKernelQuad_bSlice_eq_cSlice p⟩

lemma survivingBCKernelQuadEmbeddingDiag_injective {n : ℕ} [NeZero n] :
    Function.Injective (survivingBCKernelQuadEmbeddingDiag (n := n)) := by
  intro p q h
  refine Subtype.ext ?_
  exact congr_arg (fun x : SurvivingBCDiag n => x.val) h

lemma card_survivingBCKernelQuad_le_card_survivingBCDiag {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCKernelQuad n) ≤ Fintype.card (SurvivingBCDiag n) := by
  refine Fintype.card_le_of_injective ?_ ?_
  · exact survivingBCKernelQuadEmbeddingDiag (n := n)
  · exact survivingBCKernelQuadEmbeddingDiag_injective (n := n)

lemma rowSum_BtoU_expand {n : ℕ} [NeZero n] (B : BField n) (t : ZMod n) :
    rowSum (BtoU B) t
      = ∑ s : ZMod n,
          ((∑ u2 : ZMod n, ∑ u3 : ZMod n, ∑ x1 : ZMod n, B (vec4 x1 (s + t) u2 u3)) +
           (∑ u2 : ZMod n, ∑ u3 : ZMod n, ∑ x1 : ZMod n, B (vec4 x1 (s + t + 1) u2 u3))) := by
  simp [rowSum, BtoU, Finset.sum_add_distrib]

lemma colSum_BtoU_expand {n : ℕ} [NeZero n] (B : BField n) (s : ZMod n) :
    colSum (BtoU B) s
      = ∑ t : ZMod n,
          ((∑ u2 : ZMod n, ∑ u3 : ZMod n, ∑ x1 : ZMod n, B (vec4 x1 (s + t) u2 u3)) +
           (∑ u2 : ZMod n, ∑ u3 : ZMod n, ∑ x1 : ZMod n, B (vec4 x1 (s + t + 1) u2 u3))) := by
  simp [colSum, BtoU, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma rowSum_CtoV_expand {n : ℕ} [NeZero n] (C : CField n) (t : ZMod n) :
    rowSum (CtoV C) t
      = ∑ s : ZMod n,
          ((∑ u0 : ZMod n, ∑ u1 : ZMod n, ∑ x1 : ZMod n, C (vec4 x1 u0 u1 (s + t))) +
           (∑ u0 : ZMod n, ∑ u1 : ZMod n, ∑ x1 : ZMod n, C (vec4 x1 u0 u1 (s + t + 1)))) := by
  simp [rowSum, CtoV, Finset.sum_add_distrib]

lemma colSum_CtoV_expand {n : ℕ} [NeZero n] (C : CField n) (s : ZMod n) :
    colSum (CtoV C) s
      = ∑ t : ZMod n,
          ((∑ u0 : ZMod n, ∑ u1 : ZMod n, ∑ x1 : ZMod n, C (vec4 x1 u0 u1 (s + t))) +
           (∑ u0 : ZMod n, ∑ u1 : ZMod n, ∑ x1 : ZMod n, C (vec4 x1 u0 u1 (s + t + 1)))) := by
  simp [colSum, CtoV, Finset.sum_add_distrib]

abbrev BFiberReal {n : ℕ} [NeZero n] (h : HRaw n) :=
  { B : BField n // BtoU B = h }

abbrev CFiberReal {n : ℕ} [NeZero n] (h : HRaw n) :=
  { C : CField n // CtoV C = h }

lemma nonempty_BFiberReal_iff {n : ℕ} [NeZero n] (h : HRaw n) :
    Nonempty (BFiberReal (n := n) h) ↔ ∃ B : BField n, BtoU B = h := by
  simp [BFiberReal, nonempty_subtype]

lemma nonempty_CFiberReal_iff {n : ℕ} [NeZero n] (h : HRaw n) :
    Nonempty (CFiberReal (n := n) h) ↔ ∃ C : CField n, CtoV C = h := by
  simp [CFiberReal, nonempty_subtype]

abbrev SurvivingSigmaReal (n : ℕ) [NeZero n] :=
  Σ h : HAdmissible n, BFiberReal (n := n) (h : HRaw n) × CFiberReal (n := n) (h : HRaw n)

lemma BField_add_self {n : ℕ} [NeZero n] (B : BField n) : B + B = 0 := by
  funext u
  simpa [Pi.add_apply] using F2_add_self (B u)

lemma CField_add_self {n : ℕ} [NeZero n] (C : CField n) : C + C = 0 := by
  funext u
  simpa [Pi.add_apply] using F2_add_self (C u)

instance LinearMap.ker_bToU_finite {n : ℕ} [NeZero n] :
    Finite (↥(LinearMap.ker (bToULinearMap (n := n)))) :=
  Finite.of_injective (Subtype.val : ↥(LinearMap.ker (bToULinearMap (n := n))) → BField n)
    Subtype.coe_injective

noncomputable instance LinearMap.ker_bToU_fintype {n : ℕ} [NeZero n] :
    Fintype (↥(LinearMap.ker (bToULinearMap (n := n)))) :=
  Fintype.ofFinite _

instance LinearMap.ker_cToV_finite {n : ℕ} [NeZero n] :
    Finite (↥(LinearMap.ker (cToVLinearMap (n := n)))) :=
  Finite.of_injective (Subtype.val : ↥(LinearMap.ker (cToVLinearMap (n := n))) → CField n)
    Subtype.coe_injective

noncomputable instance LinearMap.ker_cToV_fintype {n : ℕ} [NeZero n] :
    Fintype (↥(LinearMap.ker (cToVLinearMap (n := n)))) :=
  Fintype.ofFinite _

/-- Affine fiber `{B | L B = L B₀}` ↔ `ker L` over `F₂` (translation by `B₀`). -/
noncomputable def fiberEquivKer_bToU {n : ℕ} [NeZero n] (B₀ : BField n) :
    { B : BField n // bToULinearMap (n := n) B = bToULinearMap B₀ }
      ≃ ↥(LinearMap.ker (bToULinearMap (n := n))) where
  toFun := fun ⟨B, hB⟩ =>
    ⟨B + B₀, LinearMap.mem_ker.mpr (by
      rw [LinearMap.map_add, hB]
      ext p
      simpa [Pi.add_apply, F2_add_self])⟩
  invFun := fun ⟨K, hK⟩ =>
    ⟨K + B₀, by
      rw [LinearMap.map_add, LinearMap.mem_ker.mp hK, zero_add]⟩
  left_inv := fun ⟨B, hB⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (B₀ u)]
    simp
  right_inv := fun ⟨K, hK⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (B₀ u)]
    simp

noncomputable def fiberEquivKer_cToV {n : ℕ} [NeZero n] (C₀ : CField n) :
    { C : CField n // cToVLinearMap (n := n) C = cToVLinearMap C₀ }
      ≃ ↥(LinearMap.ker (cToVLinearMap (n := n))) where
  toFun := fun ⟨C, hC⟩ =>
    ⟨C + C₀, LinearMap.mem_ker.mpr (by
      rw [LinearMap.map_add, hC]
      ext p
      simpa [Pi.add_apply, F2_add_self])⟩
  invFun := fun ⟨K, hK⟩ =>
    ⟨K + C₀, by
      rw [LinearMap.map_add, LinearMap.mem_ker.mp hK, zero_add]⟩
  left_inv := fun ⟨C, hC⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (C₀ u)]
    simp
  right_inv := fun ⟨K, hK⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (C₀ u)]
    simp

lemma Fintype.card_fiber_bToU_eq_card_ker {n : ℕ} [NeZero n] (B₀ : BField n) :
    Fintype.card { B : BField n // bToULinearMap (n := n) B = bToULinearMap B₀ } =
      Fintype.card (↥(LinearMap.ker (bToULinearMap (n := n)))) :=
  Fintype.card_congr (fiberEquivKer_bToU (n := n) B₀)

lemma Fintype.card_fiber_cToV_eq_card_ker {n : ℕ} [NeZero n] (C₀ : CField n) :
    Fintype.card { C : CField n // cToVLinearMap (n := n) C = cToVLinearMap C₀ } =
      Fintype.card (↥(LinearMap.ker (cToVLinearMap (n := n)))) :=
  Fintype.card_congr (fiberEquivKer_cToV (n := n) C₀)

noncomputable def BFiberReal_equiv_preimage_bToU {n : ℕ} [NeZero n] (h : HRaw n) (B₀ : BField n)
    (hB₀ : BtoU B₀ = h) :
    BFiberReal h ≃ { B : BField n // bToULinearMap (n := n) B = bToULinearMap B₀ } where
  toFun := fun ⟨B, hB⟩ =>
    ⟨B, by simpa [bToULinearMap_apply, hB₀] using hB⟩
  invFun := fun ⟨B, hB⟩ =>
    ⟨B, by
      have h' : BtoU B = BtoU B₀ := by simpa [bToULinearMap_apply] using hB
      simpa [hB₀] using h'⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

noncomputable def CFiberReal_equiv_preimage_cToV {n : ℕ} [NeZero n] (h : HRaw n) (C₀ : CField n)
    (hC₀ : CtoV C₀ = h) :
    CFiberReal h ≃ { C : CField n // cToVLinearMap (n := n) C = cToVLinearMap C₀ } where
  toFun := fun ⟨C, hC⟩ =>
    ⟨C, by simpa [cToVLinearMap_apply, hC₀] using hC⟩
  invFun := fun ⟨C, hC⟩ =>
    ⟨C, by
      have h' : CtoV C = CtoV C₀ := by simpa [cToVLinearMap_apply] using hC
      simpa [hC₀] using h'⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

lemma Fintype.card_BFiberReal_eq_card_ker_bToU {n : ℕ} [NeZero n] (h : HRaw n) (B₀ : BField n)
    (hB₀ : BtoU B₀ = h) :
    Fintype.card (BFiberReal (n := n) h) =
      Fintype.card (↥(LinearMap.ker (bToULinearMap (n := n)))) := by
  calc
    Fintype.card (BFiberReal h)
        = Fintype.card { B : BField n // bToULinearMap B = bToULinearMap B₀ } := by
          exact Fintype.card_congr (BFiberReal_equiv_preimage_bToU (n := n) h B₀ hB₀)
    _ = Fintype.card (↥(LinearMap.ker (bToULinearMap (n := n)))) :=
          Fintype.card_fiber_bToU_eq_card_ker B₀

lemma Fintype.card_CFiberReal_eq_card_ker_cToV {n : ℕ} [NeZero n] (h : HRaw n) (C₀ : CField n)
    (hC₀ : CtoV C₀ = h) :
    Fintype.card (CFiberReal (n := n) h) =
      Fintype.card (↥(LinearMap.ker (cToVLinearMap (n := n)))) := by
  calc
    Fintype.card (CFiberReal h)
        = Fintype.card { C : CField n // cToVLinearMap C = cToVLinearMap C₀ } := by
          exact Fintype.card_congr (CFiberReal_equiv_preimage_cToV (n := n) h C₀ hC₀)
    _ = Fintype.card (↥(LinearMap.ker (cToVLinearMap (n := n)))) :=
          Fintype.card_fiber_cToV_eq_card_ker C₀

/-! ### Rank–nullity bounds on `ker bToU` / `ker cToV` and `2`-power cardinality

Over `F₂`, `BField n = (T4 n → F₂)` has `finrank = n^4` and `HRaw n = (T2 n → F₂)` has
`finrank = n^2`. Hence for `L : BField n →ₗ[F₂] HRaw n`, one always has
`finrank (range L) ≤ n^2`, so `finrank (ker L) ≥ n^4 - n^2`.

Any statement of the form `|ker L| = 2^(n^4 - n^3 + n^2)` is therefore **incompatible**
with this bound as soon as `2 < n`, because then `n^4 - n^3 + n^2 < n^4 - n^2` as natural
numbers. The former project assumption `card_BFiber_axiom` uses exactly this exponent; it cannot be
proved from the linear map model for general `n` without revising either the map’s codomain,
the intended exponent, or the counting scheme.
(Indeed, for `2 < n` one has `n^4 - n^3 + n^2 < n^4 - n^2` as natural numbers, so the postulated
exponent is **smaller** than even the dimension forced by `rank ≤ n^2`.) -/

lemma finrank_BField_eq {n : ℕ} [NeZero n] : Module.finrank F₂ (BField n) = n ^ 4 := by
  classical
  simpa [BField, Module.finrank_pi, Fintype.card_fun]

lemma finrank_CField_eq {n : ℕ} [NeZero n] : Module.finrank F₂ (CField n) = n ^ 4 := by
  classical
  simpa [CField, Module.finrank_pi, Fintype.card_fun]

lemma finrank_HRaw_eq {n : ℕ} [NeZero n] : Module.finrank F₂ (HRaw n) = n ^ 2 := by
  classical
  simpa [HRaw, Module.finrank_pi, Fintype.card_fun]

lemma finrank_range_bToULinearMap_le {n : ℕ} [NeZero n] :
    Module.finrank F₂ (LinearMap.range (bToULinearMap (n := n))) ≤ n ^ 2 := by
  classical
  have hres :
      Module.finrank F₂ (LinearMap.range (bToULinearMap (n := n))) ≤
        Module.finrank F₂ (HRaw n) :=
    Submodule.finrank_le (LinearMap.range (bToULinearMap (n := n)))
  simpa [finrank_HRaw_eq (n := n)] using hres

lemma finrank_range_cToVLinearMap_le {n : ℕ} [NeZero n] :
    Module.finrank F₂ (LinearMap.range (cToVLinearMap (n := n))) ≤ n ^ 2 := by
  classical
  have hres :
      Module.finrank F₂ (LinearMap.range (cToVLinearMap (n := n))) ≤
        Module.finrank F₂ (HRaw n) :=
    Submodule.finrank_le (LinearMap.range (cToVLinearMap (n := n)))
  simpa [finrank_HRaw_eq (n := n)] using hres

lemma finrank_ker_bToULinearMap_ge {n : ℕ} [NeZero n] :
    n ^ 4 - n ^ 2 ≤ Module.finrank F₂ (LinearMap.ker (bToULinearMap (n := n))) := by
  classical
  let L := bToULinearMap (n := n)
  let R := Module.finrank F₂ (LinearMap.range L)
  let K := Module.finrank F₂ (LinearMap.ker L)
  have hsum : R + K = n ^ 4 := by
    simpa [finrank_BField_eq (n := n), add_comm] using
      (LinearMap.finrank_range_add_finrank_ker (V₂ := HRaw n) L)
  have hr : R ≤ n ^ 2 := finrank_range_bToULinearMap_le (n := n)
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hRle : R ≤ n ^ 4 :=
    le_trans hr (Nat.pow_le_pow_right hn0 (by omega : 2 ≤ 4))
  have hK : K = n ^ 4 - R :=
    Nat.add_right_cancel
      (calc
        K + R = n ^ 4 := by simpa [add_comm] using hsum
        _ = (n ^ 4 - R) + R := (Nat.sub_add_cancel hRle).symm)
  have hle : n ^ 4 - n ^ 2 ≤ n ^ 4 - R := Nat.sub_le_sub_left hr (n ^ 4)
  simpa [← hK] using hle

lemma finrank_ker_cToVLinearMap_ge {n : ℕ} [NeZero n] :
    n ^ 4 - n ^ 2 ≤ Module.finrank F₂ (LinearMap.ker (cToVLinearMap (n := n))) := by
  classical
  let L := cToVLinearMap (n := n)
  let R := Module.finrank F₂ (LinearMap.range L)
  let K := Module.finrank F₂ (LinearMap.ker L)
  have hsum : R + K = n ^ 4 := by
    simpa [finrank_CField_eq (n := n), add_comm] using
      (LinearMap.finrank_range_add_finrank_ker (V₂ := HRaw n) L)
  have hr : R ≤ n ^ 2 := finrank_range_cToVLinearMap_le (n := n)
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hRle : R ≤ n ^ 4 :=
    le_trans hr (Nat.pow_le_pow_right hn0 (by omega : 2 ≤ 4))
  have hK : K = n ^ 4 - R :=
    Nat.add_right_cancel
      (calc
        K + R = n ^ 4 := by simpa [add_comm] using hsum
        _ = (n ^ 4 - R) + R := (Nat.sub_add_cancel hRle).symm)
  have hle : n ^ 4 - n ^ 2 ≤ n ^ 4 - R := Nat.sub_le_sub_left hr (n ^ 4)
  simpa [← hK] using hle

lemma Fintype.card_ker_bToULinearMap_eq_two_pow_finrank {n : ℕ} [NeZero n] :
    Fintype.card (↥(LinearMap.ker (bToULinearMap (n := n)))) =
      2 ^ Module.finrank F₂ (LinearMap.ker (bToULinearMap (n := n))) := by
  classical
  simpa [F₂] using
    (Module.card_eq_pow_finrank (K := F₂)
      (V := ↥(LinearMap.ker (bToULinearMap (n := n)))))

lemma Fintype.card_ker_cToVLinearMap_eq_two_pow_finrank {n : ℕ} [NeZero n] :
    Fintype.card (↥(LinearMap.ker (cToVLinearMap (n := n)))) =
      2 ^ Module.finrank F₂ (LinearMap.ker (cToVLinearMap (n := n))) := by
  classical
  simpa [F₂] using
    (Module.card_eq_pow_finrank (K := F₂)
      (V := ↥(LinearMap.ker (cToVLinearMap (n := n)))))

/-- Nonempty `BtoU`-fiber has cardinality `2^{finrank ker bToU}`. -/
lemma Fintype.card_BFiberReal_eq_two_pow_finrank_ker {n : ℕ} [NeZero n] (h : HRaw n) (B₀ : BField n)
    (hB₀ : BtoU B₀ = h) :
    Fintype.card (BFiberReal (n := n) h) =
      (2 : ℕ) ^ Module.finrank F₂ (LinearMap.ker (bToULinearMap (n := n))) := by
  rw [Fintype.card_BFiberReal_eq_card_ker_bToU (n := n) h B₀ hB₀,
    Fintype.card_ker_bToULinearMap_eq_two_pow_finrank]

/-- Same for `CtoV` fibers versus `ker cToV`. -/
lemma Fintype.card_CFiberReal_eq_two_pow_finrank_ker {n : ℕ} [NeZero n] (h : HRaw n) (C₀ : CField n)
    (hC₀ : CtoV C₀ = h) :
    Fintype.card (CFiberReal (n := n) h) =
      (2 : ℕ) ^ Module.finrank F₂ (LinearMap.ker (cToVLinearMap (n := n))) := by
  rw [Fintype.card_CFiberReal_eq_card_ker_cToV (n := n) h C₀ hC₀,
    Fintype.card_ker_cToVLinearMap_eq_two_pow_finrank]

/-- Closed `2^e` cardinality for the `B` fiber ↔ `e = finrank ker bToU`. -/
lemma Fintype.card_BFiberReal_eq_pow_iff_finrank_ker_eq
    {n : ℕ} [NeZero n] (h : HRaw n) (B₀ : BField n)
    (hB₀ : BtoU B₀ = h) (e : ℕ) :
    Fintype.card (BFiberReal (n := n) h) = (2 : ℕ) ^ e ↔
      Module.finrank F₂ (LinearMap.ker (bToULinearMap (n := n))) = e := by
  rw [Fintype.card_BFiberReal_eq_two_pow_finrank_ker (n := n) h B₀ hB₀]
  constructor
  · intro he
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) he
  · rintro rfl; rfl

lemma Fintype.card_CFiberReal_eq_pow_iff_finrank_ker_eq
    {n : ℕ} [NeZero n] (h : HRaw n) (C₀ : CField n)
    (hC₀ : CtoV C₀ = h) (e : ℕ) :
    Fintype.card (CFiberReal (n := n) h) = (2 : ℕ) ^ e ↔
      Module.finrank F₂ (LinearMap.ker (cToVLinearMap (n := n))) = e := by
  rw [Fintype.card_CFiberReal_eq_two_pow_finrank_ker (n := n) h C₀ hC₀]
  constructor
  · intro he
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) he
  · rintro rfl; rfl

/-- Rank–nullity lower bound on nonempty `BtoU`-fibers:
`finrank ker ≥ n^4 - n^2`, hence `(2 : ℕ)^(n^4 - n^2) ≤ |BFiberReal h|`. -/
lemma Fintype.card_BFiberReal_ge_pow_dimLowerBound {n : ℕ} [NeZero n] (h : HRaw n) (B₀ : BField n)
    (hB₀ : BtoU B₀ = h) :
    (2 : ℕ) ^ (n ^ 4 - n ^ 2) ≤ Fintype.card (BFiberReal (n := n) h) := by
  rw [Fintype.card_BFiberReal_eq_card_ker_bToU (n := n) h B₀ hB₀]
  rw [Fintype.card_ker_bToULinearMap_eq_two_pow_finrank]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (finrank_ker_bToULinearMap_ge (n := n))

/-- Same for `CtoV` fibers versus `ker cToV`. -/
lemma Fintype.card_CFiberReal_ge_pow_dimLowerBound {n : ℕ} [NeZero n] (h : HRaw n) (C₀ : CField n)
    (hC₀ : CtoV C₀ = h) :
    (2 : ℕ) ^ (n ^ 4 - n ^ 2) ≤ Fintype.card (CFiberReal (n := n) h) := by
  rw [Fintype.card_CFiberReal_eq_card_ker_cToV (n := n) h C₀ hC₀]
  rw [Fintype.card_ker_cToVLinearMap_eq_two_pow_finrank]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (finrank_ker_cToVLinearMap_ge (n := n))

lemma BtoU_mem_HAdmissible {n : ℕ} [NeZero n] (B : BField n) :
  (BtoU B : HRaw n) ∈ (Set.range (fun h : HAdmissible n => (h : HRaw n))) := by
  change ∃ h : HAdmissible n, (h : HRaw n) = BtoU B
  refine ⟨⟨BtoU B, ?_⟩, rfl⟩
  constructor
  · intro t
    let g : ZMod n → F₂ :=
      fun y => ∑ u2 : ZMod n, ∑ u3 : ZMod n, ∑ x1 : ZMod n, B (vec4 x1 y u2 u3)
    have h1 : (∑ s : ZMod n, g (s + t)) = ∑ s : ZMod n, g s := sum_zmod_add_right g t
    have h2 : (∑ s : ZMod n, g (s + t + 1)) = ∑ s : ZMod n, g s := by
      simpa [add_assoc] using (sum_zmod_add_right g (t + 1))
    calc
      rowSum (BtoU B) t
          = (∑ s : ZMod n, g (s + t)) + (∑ s : ZMod n, g (s + t + 1)) := by
              simp [rowSum_BtoU_expand, g, Finset.sum_add_distrib]
      _ = (∑ s : ZMod n, g s) + (∑ s : ZMod n, g s) := by rw [h1, h2]
      _ = 0 := by simpa using F2_add_self (∑ s : ZMod n, g s)
  · intro s
    let g : ZMod n → F₂ :=
      fun y => ∑ u2 : ZMod n, ∑ u3 : ZMod n, ∑ x1 : ZMod n, B (vec4 x1 y u2 u3)
    have h1 : (∑ t : ZMod n, g (s + t)) = ∑ t : ZMod n, g t := by
      calc
        (∑ t : ZMod n, g (s + t)) = ∑ t : ZMod n, g (t + s) := by simp [add_comm]
        _ = ∑ t : ZMod n, g t := sum_zmod_add_right g s
    have h2 : (∑ t : ZMod n, g (s + t + 1)) = ∑ t : ZMod n, g t := by
      calc
        (∑ t : ZMod n, g (s + t + 1)) = ∑ t : ZMod n, g (t + (s + 1)) := by
            simp [add_assoc, add_comm, add_left_comm]
        _ = ∑ t : ZMod n, g t := sum_zmod_add_right g (s + 1)
    calc
      colSum (BtoU B) s
          = (∑ t : ZMod n, g (s + t)) + (∑ t : ZMod n, g (s + t + 1)) := by
              simp [colSum_BtoU_expand, g, Finset.sum_add_distrib]
      _ = (∑ t : ZMod n, g t) + (∑ t : ZMod n, g t) := by rw [h1, h2]
      _ = 0 := by simpa using F2_add_self (∑ t : ZMod n, g t)

lemma CtoV_mem_HAdmissible {n : ℕ} [NeZero n] (C : CField n) :
  (CtoV C : HRaw n) ∈ (Set.range (fun h : HAdmissible n => (h : HRaw n))) := by
  change ∃ h : HAdmissible n, (h : HRaw n) = CtoV C
  refine ⟨⟨CtoV C, ?_⟩, rfl⟩
  constructor
  · intro t
    let g : ZMod n → F₂ :=
      fun y => ∑ u0 : ZMod n, ∑ u1 : ZMod n, ∑ x1 : ZMod n, C (vec4 x1 u0 u1 y)
    have h1 : (∑ s : ZMod n, g (s + t)) = ∑ s : ZMod n, g s := sum_zmod_add_right g t
    have h2 : (∑ s : ZMod n, g (s + t + 1)) = ∑ s : ZMod n, g s := by
      simpa [add_assoc] using (sum_zmod_add_right g (t + 1))
    calc
      rowSum (CtoV C) t
          = (∑ s : ZMod n, g (s + t)) + (∑ s : ZMod n, g (s + t + 1)) := by
              simp [rowSum_CtoV_expand, g, Finset.sum_add_distrib]
      _ = (∑ s : ZMod n, g s) + (∑ s : ZMod n, g s) := by rw [h1, h2]
      _ = 0 := by simpa using F2_add_self (∑ s : ZMod n, g s)
  · intro s
    let g : ZMod n → F₂ :=
      fun y => ∑ u0 : ZMod n, ∑ u1 : ZMod n, ∑ x1 : ZMod n, C (vec4 x1 u0 u1 y)
    have h1 : (∑ t : ZMod n, g (s + t)) = ∑ t : ZMod n, g t := by
      calc
        (∑ t : ZMod n, g (s + t)) = ∑ t : ZMod n, g (t + s) := by simp [add_comm]
        _ = ∑ t : ZMod n, g t := sum_zmod_add_right g s
    have h2 : (∑ t : ZMod n, g (s + t + 1)) = ∑ t : ZMod n, g t := by
      calc
        (∑ t : ZMod n, g (s + t + 1)) = ∑ t : ZMod n, g (t + (s + 1)) := by
            simp [add_assoc, add_comm, add_left_comm]
        _ = ∑ t : ZMod n, g t := sum_zmod_add_right g (s + 1)
    calc
      colSum (CtoV C) s
          = (∑ t : ZMod n, g (s + t)) + (∑ t : ZMod n, g (s + t + 1)) := by
              simp [colSum_CtoV_expand, g, Finset.sum_add_distrib]
      _ = (∑ t : ZMod n, g t) + (∑ t : ZMod n, g t) := by rw [h1, h2]
      _ = 0 := by simpa using F2_add_self (∑ t : ZMod n, g t)

/-- Structural surviving set: B/C pairings with matched projected profiles. -/
abbrev SurvivingBCReal (n : ℕ) [NeZero n] :=
  { p : BField n × CField n // BtoU p.1 = CtoV p.2 }

/-- Canonical point in `SurvivingBCReal`: zero `B` and `C`, so `BtoU 0 = 0 = CtoV 0`. -/
def SurvivingBCReal_zero {n : ℕ} [NeZero n] : SurvivingBCReal n :=
  ⟨⟨(0 : BField n), (0 : CField n)⟩, by rw [BtoU_zero (n := n), CtoV_zero (n := n)]⟩

lemma SurvivingBCReal_nonempty {n : ℕ} [NeZero n] : Nonempty (SurvivingBCReal n) :=
  ⟨SurvivingBCReal_zero⟩

noncomputable def survivingBCReal_equiv_slice {n : ℕ} [NeZero n] :
    SurvivingBCReal n ≃ SurvivingBCSlice n where
  toFun := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    exact ⟨⟨B, C⟩, (BtoU_eq_CtoV_iff_slices (n := n) B C).1 hBC⟩
  invFun := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    exact ⟨⟨B, C⟩, (BtoU_eq_CtoV_iff_slices (n := n) B C).2 hBC⟩
  left_inv := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    rfl

noncomputable def survivingBCSlice_equiv_diag {n : ℕ} [NeZero n] :
    SurvivingBCSlice n ≃ SurvivingBCDiag n where
  toFun := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    exact ⟨⟨B, C⟩, (slices_eq_on_pairs_iff_all (n := n) B C).1 hBC⟩
  invFun := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    exact ⟨⟨B, C⟩, (slices_eq_on_pairs_iff_all (n := n) B C).2 hBC⟩
  left_inv := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    rfl

noncomputable def chooseHB {n : ℕ} [NeZero n] (B : BField n) : HAdmissible n :=
  ⟨BtoU B, by
    simpa [Set.mem_range] using (BtoU_mem_HAdmissible (n := n) B)⟩

lemma chooseHB_spec {n : ℕ} [NeZero n] (B : BField n) :
    (chooseHB (n := n) B : HRaw n) = BtoU B :=
  rfl

lemma BtoU_depends_on_sum {n : ℕ} [NeZero n] (B : BField n) (a b : ZMod n) :
    BtoU B (vec2 a b) = BtoU B (vec2 0 (a + b)) := by
  rw [BtoU_eq_bSlice (n := n) B (vec2 a b), BtoU_eq_bSlice (n := n) B (vec2 0 (a + b))]
  simp

lemma BtoU_witness_implies_sumDependent {n : ℕ} [NeZero n] (h : HAdmissible n)
    (B : BField n) (hB : BtoU B = (h : HRaw n)) :
    ∀ a b : ZMod n, (h : HRaw n) (vec2 a b) = (h : HRaw n) (vec2 0 (a + b)) := by
  intro a b
  calc
    (h : HRaw n) (vec2 a b) = BtoU B (vec2 a b) := by simpa [hB]
    _ = BtoU B (vec2 0 (a + b)) := BtoU_depends_on_sum (n := n) B a b
    _ = (h : HRaw n) (vec2 0 (a + b)) := by simpa [hB]

theorem exists_HAdmissible_not_sumDependent_of_two_lt {n : ℕ} [NeZero n] (hn : 2 < n) :
    ∃ h : HAdmissible n,
      ¬ (∀ a b : ZMod n, (h : HRaw n) (vec2 a b) = (h : HRaw n) (vec2 0 (a + b))) := by
  have h1lt : 1 < n := lt_trans (by decide : 1 < 2) hn
  have h1nz : (1 : ZMod n) ≠ 0 := by
    intro h10
    have hval1 : ((1 : ZMod n)).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (n := n) (a := 1) h1lt)
    have hval0 : (0 : ZMod n).val = 0 := ZMod.val_zero
    rw [h10, hval0] at hval1
    omega
  have h2nz : (2 : ZMod n) ≠ 0 := by
    intro h20
    have hval2 : ((2 : ZMod n)).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (n := n) (a := 2) hn)
    have hval0 : (0 : ZMod n).val = 0 := ZMod.val_zero
    rw [h20, hval0] at hval2
    omega
  have h2ne1 : (2 : ZMod n) ≠ 1 := by
    intro h21
    have hval2 : ((2 : ZMod n)).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (n := n) (a := 2) hn)
    have hval1 : ((1 : ZMod n)).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (n := n) (a := 1) h1lt)
    rw [h21, hval1] at hval2
    omega
  let oneCore : CoreIdx n := ⟨1, h1nz⟩
  let twoCore : CoreIdx n := ⟨2, h2nz⟩
  let g : CoreIdx n → CoreIdx n → F₂ := fun s t =>
    if s = oneCore ∧ t = oneCore then 1 else 0
  let h : HAdmissible n := ⟨hOfCore g, hOfCore_admissible (n := n) g⟩
  refine ⟨h, ?_⟩
  intro hdep
  have h11 : (h : HRaw n) (vec2 1 1) = 1 := by
    have hcore := hOfCore_at_st (n := n) g oneCore oneCore
    simpa [h, g] using hcore
  have h02 : (h : HRaw n) (vec2 0 2) = 0 := by
    have hcore := hOfCore_at_0t (n := n) g twoCore
    have ht : twoCore ≠ oneCore := by
      intro hEq
      exact h2ne1 (congrArg Subtype.val hEq)
    simpa [h, g, coreRowSum, ht]
      using hcore
  have hsum := hdep 1 1
  have hone : (1 : ZMod n) + 1 = (2 : ZMod n) := by norm_num
  have hsum' : (h : HRaw n) (vec2 1 1) = (h : HRaw n) (vec2 0 2) := by
    simpa [hone] using hsum
  rw [h11, h02] at hsum'
  exact one_ne_zero hsum'

theorem not_forall_HAdmissible_exists_BtoU_witness_of_two_lt {n : ℕ} [NeZero n] (hn : 2 < n) :
    ¬ (∀ h : HAdmissible n, ∃ B : BField n, BtoU B = (h : HRaw n)) := by
  intro hall
  rcases exists_HAdmissible_not_sumDependent_of_two_lt (n := n) hn with ⟨h, hnot⟩
  rcases hall h with ⟨B, hB⟩
  exact hnot (BtoU_witness_implies_sumDependent (n := n) h B hB)

noncomputable def survivingBCReal_equiv_sigmaReal {n : ℕ} [NeZero n] :
    SurvivingBCReal n ≃
      SurvivingSigmaReal n where
  toFun := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    let h : HAdmissible n := chooseHB (n := n) B
    refine ⟨h, ⟨⟨B, ?_⟩, ⟨C, ?_⟩⟩⟩
    · simpa [h] using (chooseHB_spec (n := n) B).symm
    · calc
        CtoV C = BtoU B := hBC.symm
        _ = (h : HRaw n) := by simpa [h] using (chooseHB_spec (n := n) B).symm
  invFun := by
    intro x
    rcases x with ⟨h, ⟨⟨B, hB⟩, ⟨C, hC⟩⟩⟩
    refine ⟨⟨B, C⟩, ?_⟩
    calc
      BtoU B = (h : HRaw n) := hB
      _ = CtoV C := by simpa [hC]
  left_inv := by
    intro p
    rcases p with ⟨⟨B, C⟩, hBC⟩
    simp [chooseHB_spec, hBC]
  right_inv := by
    intro x
    rcases x with ⟨h, ⟨⟨B, hB⟩, ⟨C, hC⟩⟩⟩
    have hh : chooseHB (n := n) B = h := by
      ext u
      calc
        (chooseHB (n := n) B : HRaw n) u = (BtoU B) u := by simp [chooseHB_spec]
        _ = (h : HRaw n) u := by simpa using congrArg (fun f : HRaw n => f u) hB
    subst hh
    simp [chooseHB_spec, hB, hC]

lemma card_survivingBCKernelQuad_eq_card_survivingBCSlice_iff_card_BC_eq_BCReal {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCSlice n) ↔
      Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCReal n) := by
  have hcardBC :
      Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCKernelQuad n) := by
    exact
      Fintype.card_congr
        ((survivingBC_equiv_kernel (n := n)).trans (survivingBCKernel_equiv_quad (n := n)))
  have hcardReal :
      Fintype.card (SurvivingBCReal n) = Fintype.card (SurvivingBCSlice n) := by
    exact Fintype.card_congr (survivingBCReal_equiv_slice (n := n))
  constructor
  · intro h
    calc
      Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCKernelQuad n) := hcardBC
      _ = Fintype.card (SurvivingBCSlice n) := h
      _ = Fintype.card (SurvivingBCReal n) := hcardReal.symm
  · intro h
    calc
      Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBC n) := hcardBC.symm
      _ = Fintype.card (SurvivingBCReal n) := h
      _ = Fintype.card (SurvivingBCSlice n) := hcardReal

/-- Bridge equality iff `card (SurvivingBCDiag n) ≤ card (SurvivingBCKernelQuad n)` (use prior `≤`). -/
lemma card_survivingBCKernelQuad_eq_card_survivingBCSlice_iff_diag_le_quad {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCSlice n) ↔
      Fintype.card (SurvivingBCDiag n) ≤ Fintype.card (SurvivingBCKernelQuad n) := by
  have hQuadLeDiag := card_survivingBCKernelQuad_le_card_survivingBCDiag (n := n)
  have hSliceDiag :
      Fintype.card (SurvivingBCSlice n) = Fintype.card (SurvivingBCDiag n) := by
    exact Fintype.card_congr (survivingBCSlice_equiv_diag (n := n))
  constructor
  · intro heq
    have heq' : Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCDiag n) :=
      heq.trans hSliceDiag
    exact heq'.symm.le
  · intro hle'
    have heq' : Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCDiag n) :=
      le_antisymm hQuadLeDiag hle'
    calc
      Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCDiag n) := heq'
      _ = Fintype.card (SurvivingBCSlice n) := hSliceDiag.symm

lemma card_survivingBCKernelQuad_eq_card_survivingBCSlice_of_diag_le_quad {n : ℕ} [NeZero n]
    (hle' : Fintype.card (SurvivingBCDiag n) ≤ Fintype.card (SurvivingBCKernelQuad n)) :
    Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCSlice n) :=
  (card_survivingBCKernelQuad_eq_card_survivingBCSlice_iff_diag_le_quad (n := n)).2 hle'

lemma fintypeCard_coe_submodule_eq_of_eq {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {S T : Submodule R M} [Fintype (↥S)] [Fintype (↥T)] (h : S = T) :
    Fintype.card (↥S) = Fintype.card (↥T) := by
  cases h
  simp only [Fintype.card_eq_nat_card]

/-- Two nested submodules of equal finite cardinality are equal (inclusion is injective). -/
lemma submodule_eq_of_le_ofFintypeCard_eq {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {S T : Submodule R M} [Fintype (↥S)] [Fintype (↥T)] (hle : S ≤ T)
    (hc : Fintype.card (↥S) = Fintype.card (↥T)) : S = T := by
  refine le_antisymm hle ?_
  refine (SetLike.coe_subset_coe (S := T) (T := S)).mpr ?_
  intro x hx
  have hbij :
      Function.Bijective (Submodule.inclusion hle) :=
    (Fintype.bijective_iff_injective_and_card (Submodule.inclusion hle)).2
      ⟨Submodule.inclusion_injective hle, hc⟩
  rcases hbij.surjective ⟨x, hx⟩ with ⟨z, hz⟩
  have hvx : (z : M) = x := by
    simpa [Submodule.coe_inclusion] using congr_arg (fun u : ↥T => (u : M)) hz
  rw [← hvx]
  exact z.property

lemma card_survivingBC_eq_card_survivingBCDiag_of_ker_eq {n : ℕ} [NeZero n]
    (hker :
      LinearMap.ker (coeffFromBCLinearMap (n := n)) =
        LinearMap.ker (sliceDiffLinearMap (n := n))) :
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCDiag n) := by
  haveI : Fintype (↥(LinearMap.ker (coeffFromBCLinearMap (n := n)))) :=
    Fintype.ofEquiv (SurvivingBC n) (survivingBC_equiv_ker_coeffFromBCLinearMap (n := n))
  haveI : Fintype (↥(LinearMap.ker (sliceDiffLinearMap (n := n)))) :=
    Fintype.ofEquiv (SurvivingBCDiag n) (survivingBCDiag_equiv_ker_sliceDiffLinearMap (n := n))
  calc
    Fintype.card (SurvivingBC n)
        = Fintype.card (↥(LinearMap.ker (coeffFromBCLinearMap (n := n)))) := by
          symm
          exact Fintype.card_congr (survivingBC_equiv_ker_coeffFromBCLinearMap (n := n))
    _ = Fintype.card (↥(LinearMap.ker (sliceDiffLinearMap (n := n)))) := by
          exact fintypeCard_coe_submodule_eq_of_eq hker
    _ = Fintype.card (SurvivingBCDiag n) := by
          symm
          exact Fintype.card_congr (survivingBCDiag_equiv_ker_sliceDiffLinearMap (n := n))

lemma card_survivingBCKernelQuad_eq_card_survivingBCSlice_of_ker_eq {n : ℕ} [NeZero n]
    (hker :
      LinearMap.ker (coeffFromBCLinearMap (n := n)) =
        LinearMap.ker (sliceDiffLinearMap (n := n))) :
    Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCSlice n) := by
  calc
    Fintype.card (SurvivingBCKernelQuad n)
        = Fintype.card (SurvivingBCKernel n) := by
          exact Fintype.card_congr (survivingBCKernel_equiv_quad (n := n)).symm
    _ = Fintype.card (SurvivingBC n) := by
          symm
          exact Fintype.card_congr (survivingBC_equiv_kernel (n := n))
    _ = Fintype.card (SurvivingBCDiag n) := card_survivingBC_eq_card_survivingBCDiag_of_ker_eq (n := n) hker
    _ = Fintype.card (SurvivingBCSlice n) := by
          exact Fintype.card_congr (survivingBCSlice_equiv_diag (n := n)).symm

lemma card_survivingBCKernelQuad_eq_card_survivingBCSlice_one :
    Fintype.card (SurvivingBCKernelQuad (1 : ℕ)) =
      Fintype.card (SurvivingBCSlice (1 : ℕ)) :=
  card_survivingBCKernelQuad_eq_card_survivingBCSlice_of_ker_eq (n := (1 : ℕ))
    LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_one

lemma LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_card_bridge {n : ℕ} [NeZero n] :
    LinearMap.ker (coeffFromBCLinearMap (n := n)) =
        LinearMap.ker (sliceDiffLinearMap (n := n)) ↔
      Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCSlice n) := by
  constructor
  · intro hker
    exact card_survivingBCKernelQuad_eq_card_survivingBCSlice_of_ker_eq (n := n) hker
  · intro hcard
    let Kc := LinearMap.ker (coeffFromBCLinearMap (n := n))
    let Ks := LinearMap.ker (sliceDiffLinearMap (n := n))
    haveI : Fintype (↥Kc) :=
      Fintype.ofEquiv (SurvivingBC n) (survivingBC_equiv_ker_coeffFromBCLinearMap (n := n))
    haveI : Fintype (↥Ks) :=
      Fintype.ofEquiv (SurvivingBCDiag n) (survivingBCDiag_equiv_ker_sliceDiffLinearMap (n := n))
    have hcard' : Fintype.card (↥Kc) = Fintype.card (↥Ks) := by
      have hbc : Fintype.card (SurvivingBC n) = Fintype.card (↥Kc) := by
        symm
        exact Fintype.card_congr (survivingBC_equiv_ker_coeffFromBCLinearMap (n := n))
      have hdiag : Fintype.card (SurvivingBCDiag n) = Fintype.card (↥Ks) := by
        exact Fintype.card_congr (survivingBCDiag_equiv_ker_sliceDiffLinearMap (n := n))
      have h3 : Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCDiag n) := by
        calc
          Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCKernelQuad n) := by
            exact
              Fintype.card_congr
                ((survivingBC_equiv_kernel (n := n)).trans (survivingBCKernel_equiv_quad (n := n)))
          _ = Fintype.card (SurvivingBCSlice n) := hcard
          _ = Fintype.card (SurvivingBCDiag n) := by
            exact Fintype.card_congr (survivingBCSlice_equiv_diag (n := n))
      exact hbc.symm.trans (h3.trans hdiag)
    exact submodule_eq_of_le_ofFintypeCard_eq (ker_coeffFromBC_le_ker_sliceDiff (n := n)) hcard'

/-- `ker coeffFromBC = ker sliceDiff` iff `|SurvivingBC| = |SurvivingBCReal|`. -/
lemma LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_card_BC_eq_BCReal {n : ℕ} [NeZero n] :
    LinearMap.ker (coeffFromBCLinearMap (n := n)) =
        LinearMap.ker (sliceDiffLinearMap (n := n)) ↔
      Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCReal n) :=
  Iff.trans (LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_card_bridge (n := n))
    (card_survivingBCKernelQuad_eq_card_survivingBCSlice_iff_card_BC_eq_BCReal (n := n))

/-- Kernel equality iff `Diag` cardinality ≤ `Quad` (pairs with known `≥`). -/
lemma LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_diag_le_quad {n : ℕ} [NeZero n] :
    LinearMap.ker (coeffFromBCLinearMap (n := n)) =
        LinearMap.ker (sliceDiffLinearMap (n := n)) ↔
      Fintype.card (SurvivingBCDiag n) ≤ Fintype.card (SurvivingBCKernelQuad n) :=
  Iff.trans (LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_card_bridge (n := n))
    (card_survivingBCKernelQuad_eq_card_survivingBCSlice_iff_diag_le_quad (n := n))

/-- **Phase 1 (assumption-free entry).** If `|SurvivingBCDiag| ≤ |SurvivingBCKernelQuad|`, then together with
the proved embedding `Quad ↪ Diag` one gets `|Quad| = |Diag|`, hence `Quad = Slice` and bridge to
kernels—packaged as `QuadSliceCardHyp.of_diag_le_quad`. -/
lemma LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_of_card_diag_le_quad {n : ℕ} [NeZero n]
    (hle : Fintype.card (SurvivingBCDiag n) ≤ Fintype.card (SurvivingBCKernelQuad n)) :
    LinearMap.ker (coeffFromBCLinearMap (n := n)) =
      LinearMap.ker (sliceDiffLinearMap (n := n)) :=
  (LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_diag_le_quad (n := n)).2 hle

/-! **Phase 1.** `n = 1`: `LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_one` and `quadSliceCardHyp_one`.
For general `n`, the bridge is the explicit hypothesis `QuadSliceCardHyp n`; equivalence with
`ker coeffFromBC = ker sliceDiff` is `LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_card_bridge` and
`LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_diag_le_quad`. Construct `QuadSliceCardHyp n` via
`QuadSliceCardHyp.of_diag_le_quad` from `|SurvivingBCDiag| ≤ |SurvivingBCKernelQuad|`,
`QuadSliceCardHyp.of_card_survivingBC_eq_card_survivingBCReal` from `|SurvivingBC| = |SurvivingBCReal|`,
`QuadSliceCardHyp.of_ker_eq` from proved kernel equality, or
`QuadSliceCardHyp.of_card_kernelQuad_eq_card_slice` from the defining bridge equality. -/

/-- **Phase 1 (explicit hypothesis).** Cardinality bridge `|SurvivingBCKernelQuad| = |SurvivingBCSlice|`.
`n = 1` is unconditional (`quadSliceCardHyp_one`); for general `n` assume this proposition, or derive it
via `QuadSliceCardHyp.of_diag_le_quad` / `QuadSliceCardHyp.of_card_survivingBC_eq_card_survivingBCReal` /
`QuadSliceCardHyp.of_ker_eq`. Replaces the former counting
assumption. -/
abbrev QuadSliceCardHyp (n : ℕ) [NeZero n] : Prop :=
  Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCSlice n)

/-- Definitional unfolding of Phase 1 (`abbrev QuadSliceCardHyp`). -/
lemma QuadSliceCardHyp_iff_card_kernelQuad_eq_card_slice {n : ℕ} [NeZero n] :
    QuadSliceCardHyp n ↔
      Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCSlice n) :=
  Iff.rfl

/-- From the raw cardinality identity (definitional for `QuadSliceCardHyp`). -/
lemma QuadSliceCardHyp.of_card_kernelQuad_eq_card_slice {n : ℕ} [NeZero n]
    (h : Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCSlice n)) :
    QuadSliceCardHyp n :=
  h

lemma quadSliceCardHyp_one : QuadSliceCardHyp (1 : ℕ) :=
  card_survivingBCKernelQuad_eq_card_survivingBCSlice_one

lemma QuadSliceCardHyp.of_diag_le_quad {n : ℕ} [NeZero n]
    (hle : Fintype.card (SurvivingBCDiag n) ≤ Fintype.card (SurvivingBCKernelQuad n)) :
    QuadSliceCardHyp n :=
  card_survivingBCKernelQuad_eq_card_survivingBCSlice_of_diag_le_quad hle

lemma QuadSliceCardHyp.of_ker_eq {n : ℕ} [NeZero n]
    (hker :
      LinearMap.ker (coeffFromBCLinearMap (n := n)) =
        LinearMap.ker (sliceDiffLinearMap (n := n))) :
    QuadSliceCardHyp n :=
  card_survivingBCKernelQuad_eq_card_survivingBCSlice_of_ker_eq hker

/-- `QuadSliceCardHyp` is equivalent to `ker coeffFromBC = ker sliceDiff`
(`LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_card_bridge`). -/
lemma QuadSliceCardHyp_iff_ker_coeffFromBC_eq_ker_sliceDiff {n : ℕ} [NeZero n] :
    QuadSliceCardHyp n ↔
      LinearMap.ker (coeffFromBCLinearMap (n := n)) =
        LinearMap.ker (sliceDiffLinearMap (n := n)) :=
  (LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_card_bridge (n := n)).symm

/-- `QuadSliceCardHyp` iff `|SurvivingBCDiag| ≤ |SurvivingBCKernelQuad|` (reverse inequality is proved). -/
lemma QuadSliceCardHyp_iff_diag_le_quad {n : ℕ} [NeZero n] :
    QuadSliceCardHyp n ↔
      Fintype.card (SurvivingBCDiag n) ≤ Fintype.card (SurvivingBCKernelQuad n) :=
  card_survivingBCKernelQuad_eq_card_survivingBCSlice_iff_diag_le_quad (n := n)

/-- `QuadSliceCardHyp` iff `|SurvivingBC| = |SurvivingBCReal|`. -/
lemma QuadSliceCardHyp_iff_card_survivingBC_eq_card_survivingBCReal {n : ℕ} [NeZero n] :
    QuadSliceCardHyp n ↔ Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCReal n) :=
  card_survivingBCKernelQuad_eq_card_survivingBCSlice_iff_card_BC_eq_BCReal (n := n)

lemma QuadSliceCardHyp.of_card_survivingBC_eq_card_survivingBCReal {n : ℕ} [NeZero n]
    (h : Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCReal n)) :
    QuadSliceCardHyp n :=
  (QuadSliceCardHyp_iff_card_survivingBC_eq_card_survivingBCReal (n := n)).2 h

lemma card_survivingBCKernelQuad_eq_card_survivingBCSlice {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n) :
    Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCSlice n) :=
  quad

lemma LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_of_card_quad_eq_slice {n : ℕ} [NeZero n]
    (h :
      Fintype.card (SurvivingBCKernelQuad n) = Fintype.card (SurvivingBCSlice n)) :
    LinearMap.ker (coeffFromBCLinearMap (n := n)) =
      LinearMap.ker (sliceDiffLinearMap (n := n)) :=
  (LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_iff_card_bridge (n := n)).2 h

/-- Unified Quad/Slice count implies kernel equality (from `QuadSliceCardHyp`). -/
lemma LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_of_counting {n : ℕ} [NeZero n]
    (quad : QuadSliceCardHyp n) :
    LinearMap.ker (coeffFromBCLinearMap (n := n)) =
      LinearMap.ker (sliceDiffLinearMap (n := n)) :=
  LinearMap.ker_coeffFromBC_eq_ker_sliceDiff_of_card_quad_eq_slice (n := n) quad

noncomputable def survivingBCReal_equiv_diag {n : ℕ} [NeZero n] :
    SurvivingBCReal n ≃ SurvivingBCDiag n :=
  (survivingBCReal_equiv_slice (n := n)).trans (survivingBCSlice_equiv_diag (n := n))

lemma card_survivingBC_eq_card_survivingBCReal {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n) :
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCReal n) := by
  calc
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCKernel n) := by
      exact Fintype.card_congr (survivingBC_equiv_kernel (n := n))
    _ = Fintype.card (SurvivingBCKernelQuad n) := by
      exact Fintype.card_congr (survivingBCKernel_equiv_quad (n := n))
    _ = Fintype.card (SurvivingBCSlice n) :=
      card_survivingBCKernelQuad_eq_card_survivingBCSlice quad
    _ = Fintype.card (SurvivingBCDiag n) :=
      Fintype.card_congr (survivingBCSlice_equiv_diag (n := n))
    _ = Fintype.card (SurvivingBCReal n) := by
      symm
      exact Fintype.card_congr (survivingBCReal_equiv_diag (n := n))

lemma card_survivingBC_eq_card_kernel {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCKernel n) := by
  exact Fintype.card_congr (survivingBC_equiv_kernel (n := n))

lemma card_survivingBCKernel_eq_card_quad {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCKernel n) = Fintype.card (SurvivingBCKernelQuad n) := by
  exact Fintype.card_congr (survivingBCKernel_equiv_quad (n := n))

lemma card_survivingBCKernel_eq_card_slice_of_quadSlice {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n) :
    Fintype.card (SurvivingBCKernel n) = Fintype.card (SurvivingBCSlice n) := by
  calc
    Fintype.card (SurvivingBCKernel n) = Fintype.card (SurvivingBCKernelQuad n) :=
      card_survivingBCKernel_eq_card_quad (n := n)
    _ = Fintype.card (SurvivingBCSlice n) :=
      card_survivingBCKernelQuad_eq_card_survivingBCSlice quad

lemma card_survivingBC_eq_card_slice {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n) :
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCSlice n) := by
  calc
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCKernel n) :=
      card_survivingBC_eq_card_kernel (n := n)
    _ = Fintype.card (SurvivingBCSlice n) := card_survivingBCKernel_eq_card_slice_of_quadSlice quad

lemma card_survivingBCKernel_eq_card_diag {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n) :
    Fintype.card (SurvivingBCKernel n) = Fintype.card (SurvivingBCDiag n) := by
  calc
    Fintype.card (SurvivingBCKernel n) = Fintype.card (SurvivingBCSlice n) :=
      card_survivingBCKernel_eq_card_slice_of_quadSlice quad
    _ = Fintype.card (SurvivingBCDiag n) := Fintype.card_congr (survivingBCSlice_equiv_diag (n := n))

lemma card_survivingBC_eq_card_diag {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n) :
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCDiag n) := by
  calc
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCSlice n) :=
      card_survivingBC_eq_card_slice quad
    _ = Fintype.card (SurvivingBCDiag n) := Fintype.card_congr (survivingBCSlice_equiv_diag (n := n))

lemma card_survivingBCReal_eq_card_sigmaReal {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCReal n) = Fintype.card (SurvivingSigmaReal n) := by
  exact Fintype.card_congr (survivingBCReal_equiv_sigmaReal (n := n))

lemma card_survivingBC_eq_card_sigmaReal {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n) :
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingSigmaReal n) := by
  calc
    Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCReal n) :=
      card_survivingBC_eq_card_survivingBCReal quad
    _ = Fintype.card (SurvivingSigmaReal n) := card_survivingBCReal_eq_card_sigmaReal (n := n)

lemma card_survivingBCKernel_eq_card_sigmaReal {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n) :
    Fintype.card (SurvivingBCKernel n) = Fintype.card (SurvivingSigmaReal n) := by
  calc
    Fintype.card (SurvivingBCKernel n) = Fintype.card (SurvivingBCDiag n) :=
      card_survivingBCKernel_eq_card_diag quad
    _ = Fintype.card (SurvivingBCReal n) := by
      symm
      exact Fintype.card_congr (survivingBCReal_equiv_diag (n := n))
    _ = Fintype.card (SurvivingSigmaReal n) := card_survivingBCReal_eq_card_sigmaReal (n := n)

lemma card_survivingBCDiag_eq_card_sigmaReal {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCDiag n) = Fintype.card (SurvivingSigmaReal n) := by
  calc
    Fintype.card (SurvivingBCDiag n) = Fintype.card (SurvivingBCReal n) := by
      symm
      exact Fintype.card_congr (survivingBCReal_equiv_diag (n := n))
    _ = Fintype.card (SurvivingSigmaReal n) := card_survivingBCReal_eq_card_sigmaReal (n := n)

lemma card_survivingBCReal_eq_card_slice {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCReal n) = Fintype.card (SurvivingBCSlice n) := by
  exact Fintype.card_congr (survivingBCReal_equiv_slice (n := n))

lemma card_survivingBCSlice_eq_card_diag {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCSlice n) = Fintype.card (SurvivingBCDiag n) := by
  exact Fintype.card_congr (survivingBCSlice_equiv_diag (n := n))

lemma card_survivingBCReal_eq_card_diag {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBCReal n) = Fintype.card (SurvivingBCDiag n) := by
  exact Fintype.card_congr (survivingBCReal_equiv_diag (n := n))

lemma card_survivingSigmaReal_eq_sum_fiberCards {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingSigmaReal n)
      = ∑ h : HAdmissible n,
          Fintype.card (BFiberReal (n := n) (h : HRaw n))
            * Fintype.card (CFiberReal (n := n) (h : HRaw n)) := by
  simpa [SurvivingSigmaReal, Fintype.card_prod] using
    (Fintype.card_sigma (β := fun h : HAdmissible n =>
      BFiberReal (n := n) (h : HRaw n) × CFiberReal (n := n) (h : HRaw n)))

lemma card_HAdmissible {n : ℕ} [NeZero n] :
  Fintype.card (HAdmissible n) = 2 ^ ((n - 1) ^ 2) := by
  calc
    Fintype.card (HAdmissible n)
        = Fintype.card (CoreIdx n → CoreIdx n → F₂) := by
          exact Fintype.card_congr (hAdmissibleEquivCore (n := n))
    _ = 2 ^ ((n - 1) * (n - 1)) := by
          simp [pow_mul, card_CoreIdx (n := n)]
    _ = 2 ^ ((n - 1) ^ 2) := by
          simp [pow_two]

lemma Nat.card_profileCompatQuad_eq_two_pow_core {n : ℕ} [NeZero n] :
    Nat.card (ProfileCompatQuad n) = 2 ^ ((n - 1) ^ 2) := by
  calc
    Nat.card (ProfileCompatQuad n) = Nat.card (HAdmissible n) := by
      exact Nat.card_congr (profileCompatQuad_equiv_HAdmissible (n := n))
    _ = 2 ^ ((n - 1) ^ 2) := by
      simpa [Nat.card_eq_fintype_card] using (card_HAdmissible (n := n))

noncomputable def compatibleProfiles_equiv_HAdmissible {n : ℕ} [NeZero n] :
    CompatibleProfiles n ≃ HAdmissible n :=
  profileCompatQuad_equiv_HAdmissible (n := n)

theorem Nat.card_CompatibleProfiles {n : ℕ} [NeZero n] :
    Nat.card (CompatibleProfiles n) = 2 ^ ((n - 1) ^ 2) :=
  Nat.card_profileCompatQuad_eq_two_pow_core (n := n)

lemma finrank_ker_profileCompatConstraintLinearMap_eq_core {n : ℕ} [NeZero n] :
    Module.finrank F₂ (LinearMap.ker (profileCompatConstraintLinearMap (n := n))) = (n - 1) ^ 2 := by
  have h1 := Nat.card_profileCompatQuad_eq_two_pow_finrank_ker (n := n)
  have h2 := Nat.card_profileCompatQuad_eq_two_pow_core (n := n)
  rw [h2] at h1
  exact (Nat.pow_right_injective (by decide : (2 : ℕ) ≤ 2)) h1.symm

theorem deltaNo13Raw_eq_two_pow_profileCompatKer_closed {n : ℕ} [NeZero n] :
    deltaNo13Raw n =
      (2 : ℤ) ^ (n ^ 4 + ((n - 1) ^ 2 + 2 * (n ^ 4 - (n ^ 3 - n ^ 2)))) := by
  rw [deltaNo13Raw_eq_two_pow_profileCompatKer (n := n),
    finrank_ker_profileCompatConstraintLinearMap_eq_core (n := n)]

theorem fiber_exponent_identity {n : ℕ} [NeZero n] :
  ((n - 1) ^ 2) + (2 * (n ^ 4 - n ^ 3 + n ^ 2))
    = 2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1 := by
  have hsqAux (m : ℕ) : 2 * (m + 1) ≤ 3 * (m + 1) ^ 2 := by
    have hle1 : m + 1 ≤ (m + 1) ^ 2 := by
      have hpos : 1 ≤ m + 1 := by
        omega
      simpa [pow_two, Nat.mul_comm] using (Nat.mul_le_mul_left (m + 1) hpos)
    calc
      2 * (m + 1) ≤ 2 * ((m + 1) ^ 2) := by
        exact Nat.mul_le_mul_left 2 hle1
      _ ≤ 3 * (m + 1) ^ 2 := by
        omega
  have hsq (m : ℕ) :
      m ^ 2 + 2 * (m + 1) ^ 2 = 3 * (m + 1) ^ 2 - 2 * (m + 1) + 1 := by
    have hle2 : 2 * (m + 1) ≤ 3 * (m + 1) ^ 2 := hsqAux m
    have hsub : 3 * (m + 1) ^ 2 - 2 * (m + 1) = 3 * m ^ 2 + 4 * m + 1 := by
      apply (Nat.sub_eq_iff_eq_add hle2).2
      ring
    have hlhs : m ^ 2 + 2 * (m + 1) ^ 2 = 3 * m ^ 2 + 4 * m + 2 := by
      ring
    rw [hlhs, hsub]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have hleft :
      2 * (((m + 1) ^ 4 - (m + 1) ^ 3) + (m + 1) ^ 2)
        = (2 * (m + 1) ^ 4 - 2 * (m + 1) ^ 3) + 2 * (m + 1) ^ 2 := by
    rw [Nat.mul_add, Nat.mul_sub_left_distrib]
  have hle2 : 2 * (m + 1) ≤ 3 * (m + 1) ^ 2 := hsqAux m
  calc
    ((m + 1 - 1) ^ 2) + (2 * ((m + 1) ^ 4 - (m + 1) ^ 3 + (m + 1) ^ 2))
        = m ^ 2 + ((2 * (m + 1) ^ 4 - 2 * (m + 1) ^ 3) + 2 * (m + 1) ^ 2) := by
            simp [hleft]
    _ = (2 * (m + 1) ^ 4 - 2 * (m + 1) ^ 3) + (m ^ 2 + 2 * (m + 1) ^ 2) := by
          omega
    _ = (2 * (m + 1) ^ 4 - 2 * (m + 1) ^ 3) + (3 * (m + 1) ^ 2 - 2 * (m + 1) + 1) := by
          rw [hsq]
    _ = (2 * (m + 1) ^ 4 - 2 * (m + 1) ^ 3) + ((3 * (m + 1) ^ 2 - 2 * (m + 1)) + 1) := by
          simp
    _ = ((2 * (m + 1) ^ 4 - 2 * (m + 1) ^ 3) + (3 * (m + 1) ^ 2 - 2 * (m + 1))) + 1 := by
          simp [Nat.add_assoc]
    _ = (((2 * (m + 1) ^ 4 - 2 * (m + 1) ^ 3) + 3 * (m + 1) ^ 2) - 2 * (m + 1)) + 1 := by
          rw [Nat.add_sub_assoc hle2]
    _ = 2 * (m + 1) ^ 4 - 2 * (m + 1) ^ 3 + 3 * (m + 1) ^ 2 - 2 * (m + 1) + 1 := by
          simp

theorem Nat.card_survivingBC_closed_via_sigmaStrong {n : ℕ} [NeZero n] :
    Nat.card (SurvivingBC n) = 2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
  have hsub : n ^ 4 - (n ^ 3 - n ^ 2) = n ^ 4 - n ^ 3 + n ^ 2 := by
    have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
    have h32 : n ^ 2 ≤ n ^ 3 := by
      calc
        n ^ 2 = n ^ 2 * 1 := by simp
        _ ≤ n ^ 2 * n := Nat.mul_le_mul_left _ hn
        _ = n ^ 3 := by simp [pow_succ]
    have h43 : n ^ 3 ≤ n ^ 4 := by
      calc
        n ^ 3 = n ^ 3 * 1 := by simp
        _ ≤ n ^ 3 * n := Nat.mul_le_mul_left _ hn
        _ = n ^ 4 := by simp [pow_succ]
    omega
  rw [Nat.card_survivingBC_eq_two_pow_finrank_profileCompatKer (n := n),
    finrank_ker_profileCompatConstraintLinearMap_eq_core (n := n), hsub]
  exact congrArg (fun t : ℕ => (2 : ℕ) ^ t) (fiber_exponent_identity (n := n))

theorem Nat.card_survivingBC_closed {n : ℕ} [NeZero n] :
    Nat.card (SurvivingBC n) = 2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
  exact Nat.card_survivingBC_closed_via_sigmaStrong (n := n)

theorem deltaNo13Raw_eq_two_pow_via_sigmaStrong {n : ℕ} [NeZero n] :
    deltaNo13Raw n =
      (2 : ℤ) ^ (n ^ 4 + (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) := by
  have hcardNat := Nat.card_survivingBC_closed_via_sigmaStrong (n := n)
  have hcard :
      Fintype.card (SurvivingBC n) = 2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
    simpa [Nat.card_eq_fintype_card] using hcardNat
  rw [deltaNo13Raw_eq_survivingBC_card, hcard]
  norm_num
  rw [← pow_add]

theorem Fintype.card_survivingBC_closed_via_sigmaStrong {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBC n) = 2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
  simpa [Nat.card_eq_fintype_card] using
    (Nat.card_survivingBC_closed_via_sigmaStrong (n := n))

theorem signed_imbalance_no13_of_card_survivingBC {n : ℕ} [NeZero n]
    (hcard :
      Fintype.card (SurvivingBC n) =
        2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) :
    deltaNo13Raw n =
      (2 : ℤ) ^ (n ^ 4 + (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) := by
  rw [deltaNo13Raw_eq_survivingBC_card, hcard]
  norm_num
  rw [← pow_add]

theorem signed_imbalance_no13_of_card_survivingBCDiag {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n)
    (hcardDiag :
      Fintype.card (SurvivingBCDiag n) =
        2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) :
    deltaNo13Raw n =
      (2 : ℤ) ^ (n ^ 4 + (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) := by
  have hcardBC :
      Fintype.card (SurvivingBC n) =
        2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
    calc
      Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCDiag n) :=
        card_survivingBC_eq_card_diag quad
      _ = 2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := hcardDiag
  exact signed_imbalance_no13_of_card_survivingBC (n := n) hcardBC

theorem signed_imbalance_no13_of_card_survivingBCReal {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n)
    (hcardReal :
      Fintype.card (SurvivingBCReal n) =
        2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) :
    deltaNo13Raw n =
      (2 : ℤ) ^ (n ^ 4 + (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) := by
  have hcardDiag :
      Fintype.card (SurvivingBCDiag n) =
        2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
    calc
      Fintype.card (SurvivingBCDiag n) = Fintype.card (SurvivingBCReal n) := by
        symm
        exact card_survivingBCReal_eq_card_diag (n := n)
      _ = 2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := hcardReal
  exact signed_imbalance_no13_of_card_survivingBCDiag (n := n) quad hcardDiag

theorem signed_imbalance_no13_of_card_survivingBCKernel {n : ℕ} [NeZero n]
    (hcardKernel :
      Fintype.card (SurvivingBCKernel n) =
        2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) :
    deltaNo13Raw n =
      (2 : ℤ) ^ (n ^ 4 + (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) := by
  have hcardBC :
      Fintype.card (SurvivingBC n) =
        2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
    calc
      Fintype.card (SurvivingBC n) = Fintype.card (SurvivingBCKernel n) :=
        card_survivingBC_eq_card_kernel (n := n)
      _ = 2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := hcardKernel
  exact signed_imbalance_no13_of_card_survivingBC (n := n) hcardBC

theorem signed_imbalance_no13_of_card_survivingSigmaReal {n : ℕ} [NeZero n] (quad : QuadSliceCardHyp n)
    (hcardSigma :
      Fintype.card (SurvivingSigmaReal n) = 2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) :
    deltaNo13Raw n =
      (2 : ℤ) ^ (n ^ 4 + (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) := by
  have hcardReal :
      Fintype.card (SurvivingBCReal n) =
        2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
    calc
      Fintype.card (SurvivingBCReal n) =
          Fintype.card
            (SurvivingSigmaReal n) := by
              exact card_survivingBCReal_eq_card_sigmaReal (n := n)
      _ = 2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := hcardSigma
  exact signed_imbalance_no13_of_card_survivingBCReal (n := n) quad hcardReal

theorem signed_imbalance_no13_of_card_survivingBCKernel_via_sigma {n : ℕ} [NeZero n]
    (quad : QuadSliceCardHyp n)
    (hcardKernel :
      Fintype.card (SurvivingBCKernel n) =
        2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) :
    deltaNo13Raw n =
      (2 : ℤ) ^ (n ^ 4 + (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)) := by
  have hcardSigma :
      Fintype.card (SurvivingSigmaReal n) =
        2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
    calc
      Fintype.card (SurvivingSigmaReal n) = Fintype.card (SurvivingBCKernel n) := by
        symm
        exact card_survivingBCKernel_eq_card_sigmaReal quad
      _ = 2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := hcardKernel
  exact signed_imbalance_no13_of_card_survivingSigmaReal (n := n) quad hcardSigma

lemma no13_closed_exponent_from_card {n : ℕ} [NeZero n] :
    n ^ 4 + (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1)
      = 3 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1 := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
  have h43 : n ^ 3 ≤ n ^ 4 := by
    calc
      n ^ 3 = n ^ 3 * 1 := by simp
      _ ≤ n ^ 3 * n := Nat.mul_le_mul_left _ hn
      _ = n ^ 4 := by simp [pow_succ]
  have h21 : n ≤ n ^ 2 := by
    calc
      n = n * 1 := by simp
      _ ≤ n * n := Nat.mul_le_mul_left _ hn
      _ = n ^ 2 := by simp [pow_two]
  omega

theorem signed_imbalance_no13_closed {n : ℕ} [NeZero n] :
    deltaNo13Raw n = (2 : ℤ) ^ (3 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
  rw [deltaNo13Raw_eq_two_pow_via_sigmaStrong (n := n)]
  congr 1
  exact no13_closed_exponent_from_card (n := n)

end No13Migration

namespace No13Migration

/-! ## General `(a,b,c)` counting shell -/

abbrev Coord (k n : ℕ) := Fin k → ZMod n

abbrev XCoord (a n : ℕ) := Coord (a - 1) n
abbrev YCoord (b n : ℕ) := Coord b n
abbrev ZCoord (c n : ℕ) := Coord c n

abbrev ASiteABC (b c n : ℕ) := YCoord b n × ZCoord c n
abbrev BSiteABC (a c n : ℕ) := XCoord a n × ZMod n × ZCoord c n
abbrev CSiteABC (a b n : ℕ) := XCoord a n × YCoord b n × ZMod n

abbrev AFieldABC (b c n : ℕ) := ASiteABC b c n → F₂
abbrev BFieldABC (a c n : ℕ) := BSiteABC a c n → F₂
abbrev CFieldABC (a b n : ℕ) := CSiteABC a b n → F₂

abbrev ABCAssignment (a b c n : ℕ) [NeZero n] :=
  AFieldABC b c n × BFieldABC a c n × CFieldABC a b n

abbrev ABCNormalForm (a b c n : ℕ) [NeZero n] := ABCAssignment a b c n

lemma card_Coord (k n : ℕ) [NeZero n] :
    Fintype.card (Coord k n) = n ^ k := by
  simpa [Coord, ZMod.card] using (Fintype.card_fun (α := Fin k) (β := ZMod n))

lemma card_XCoord (a n : ℕ) [NeZero n] :
    Fintype.card (XCoord a n) = n ^ (a - 1) := by
  simpa [XCoord] using card_Coord (k := a - 1) (n := n)

lemma card_YCoord (b n : ℕ) [NeZero n] :
    Fintype.card (YCoord b n) = n ^ b := by
  simpa [YCoord] using card_Coord (k := b) (n := n)

lemma card_ZCoord (c n : ℕ) [NeZero n] :
    Fintype.card (ZCoord c n) = n ^ c := by
  simpa [ZCoord] using card_Coord (k := c) (n := n)

lemma card_ASiteABC (b c n : ℕ) [NeZero n] :
    Fintype.card (ASiteABC b c n) = n ^ (b + c) := by
  calc
    Fintype.card (ASiteABC b c n)
        = Fintype.card (YCoord b n) * Fintype.card (ZCoord c n) := by
            simp [ASiteABC]
    _ = n ^ b * n ^ c := by rw [card_YCoord, card_ZCoord]
    _ = n ^ (b + c) := by rw [Nat.pow_add]

lemma card_BSiteABC {a c n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (BSiteABC a c n) = n ^ (a + c) := by
  have hexp : (a - 1) + 1 = a := Nat.sub_add_cancel (Nat.succ_le_of_lt ha)
  have hpow : n ^ (a - 1) * n = n ^ ((a - 1) + 1) := by
    simpa using (pow_succ n (a - 1)).symm
  calc
    Fintype.card (BSiteABC a c n)
        = Fintype.card (XCoord a n) * Fintype.card (ZMod n) * Fintype.card (ZCoord c n) := by
            simp [BSiteABC, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = n ^ (a - 1) * n * n ^ c := by rw [card_XCoord, ZMod.card, card_ZCoord]
    _ = (n ^ (a - 1) * n) * n ^ c := by simp [Nat.mul_assoc]
    _ = n ^ ((a - 1) + 1) * n ^ c := by rw [hpow]
    _ = n ^ a * n ^ c := by rw [hexp]
    _ = n ^ (a + c) := by rw [Nat.pow_add]

lemma card_CSiteABC {a b n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (CSiteABC a b n) = n ^ (a + b) := by
  have hexp : (a - 1) + 1 = a := Nat.sub_add_cancel (Nat.succ_le_of_lt ha)
  have hpow : n ^ (a - 1) * n = n ^ ((a - 1) + 1) := by
    simpa using (pow_succ n (a - 1)).symm
  calc
    Fintype.card (CSiteABC a b n)
        = Fintype.card (XCoord a n) * Fintype.card (YCoord b n) * Fintype.card (ZMod n) := by
            simp [CSiteABC, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = n ^ (a - 1) * n ^ b * n := by rw [card_XCoord, card_YCoord, ZMod.card]
    _ = (n ^ (a - 1) * n) * n ^ b := by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = n ^ ((a - 1) + 1) * n ^ b := by rw [hpow]
    _ = n ^ a * n ^ b := by rw [hexp]
    _ = n ^ (a + b) := by rw [Nat.pow_add]

lemma card_uSpace_abc (c n : ℕ) [NeZero n] :
    Fintype.card (ZCoord c n → F₂) = 2 ^ (n ^ c) := by
  rw [Fintype.card_fun, card_ZCoord]
  simp [F₂, ZMod.card]

lemma card_thetaSpace_abc (b n : ℕ) [NeZero n] :
    Fintype.card (YCoord b n → F₂) = 2 ^ (n ^ b) := by
  rw [Fintype.card_fun, card_YCoord]
  simp [F₂, ZMod.card]

lemma card_AFieldABC (b c n : ℕ) [NeZero n] :
    Fintype.card (AFieldABC b c n) = 2 ^ (n ^ (b + c)) := by
  simpa [AFieldABC, F₂, ZMod.card, card_ASiteABC (b := b) (c := c) (n := n)] using
    (Fintype.card_fun (α := ASiteABC b c n) (β := F₂))

lemma card_BFieldABC {a c n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (BFieldABC a c n) = 2 ^ (n ^ (a + c)) := by
  simpa [BFieldABC, F₂, ZMod.card, card_BSiteABC (a := a) (c := c) (n := n) ha] using
    (Fintype.card_fun (α := BSiteABC a c n) (β := F₂))

lemma card_CFieldABC {a b n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (CFieldABC a b n) = 2 ^ (n ^ (a + b)) := by
  simpa [CFieldABC, F₂, ZMod.card, card_CSiteABC (a := a) (b := b) (n := n) ha] using
    (Fintype.card_fun (α := CSiteABC a b n) (β := F₂))

lemma finrank_AFieldABC (b c n : ℕ) [NeZero n] :
    Module.finrank F₂ (AFieldABC b c n) = n ^ (b + c) := by
  simpa [AFieldABC, card_ASiteABC (b := b) (c := c) (n := n)] using
    (Module.finrank_fintype_fun_eq_card (R := F₂) (η := ASiteABC b c n))

lemma finrank_BFieldABC {a c n : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F₂ (BFieldABC a c n) = n ^ (a + c) := by
  simpa [BFieldABC, card_BSiteABC (a := a) (c := c) (n := n) ha] using
    (Module.finrank_fintype_fun_eq_card (R := F₂) (η := BSiteABC a c n))

lemma finrank_CFieldABC {a b n : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F₂ (CFieldABC a b n) = n ^ (a + b) := by
  simpa [CFieldABC, card_CSiteABC (a := a) (b := b) (n := n) ha] using
    (Module.finrank_fintype_fun_eq_card (R := F₂) (η := CSiteABC a b n))

theorem card_validAssignments_abc {a b c n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (ABCAssignment a b c n) =
      2 ^ (n ^ (b + c) + n ^ (a + c) + n ^ (a + b)) := by
  calc
    Fintype.card (ABCAssignment a b c n)
        = Fintype.card (AFieldABC b c n) *
            (Fintype.card (BFieldABC a c n) * Fintype.card (CFieldABC a b n)) := by
              simp [ABCAssignment, Nat.mul_assoc]
    _ = 2 ^ (n ^ (b + c)) * (2 ^ (n ^ (a + c)) * 2 ^ (n ^ (a + b))) := by
          rw [card_AFieldABC, card_BFieldABC ha, card_CFieldABC ha]
    _ = 2 ^ (n ^ (b + c)) * 2 ^ (n ^ (a + c) + n ^ (a + b)) := by
          rw [← Nat.pow_add]
    _ = 2 ^ (n ^ (b + c) + (n ^ (a + c) + n ^ (a + b))) := by
          rw [← Nat.pow_add]
    _ = 2 ^ (n ^ (b + c) + n ^ (a + c) + n ^ (a + b)) := by simp [add_assoc]

theorem card_HAdmissible_closed_abc {n : ℕ} [NeZero n] :
    Fintype.card (HAdmissible n) = 2 ^ ((n - 1) ^ 2) :=
  card_HAdmissible (n := n)

abbrev survivingExponentABC (a b c n : ℕ) : ℕ :=
  (n - 1) ^ 2 + (n ^ c + (n ^ (a + c) - n ^ (c + 1))) +
    (n ^ b + (n ^ (a + b) - n ^ (b + 1)))

abbrev totalExponentABC (a b c n : ℕ) : ℕ :=
  n ^ (b + c) + survivingExponentABC a b c n

lemma survivingExponentABC_eq_explicit {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) :
    survivingExponentABC a b c n =
      n ^ (a + c) + n ^ (a + b) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b +
        (n - 1) ^ 2 := by
  have hca : n ^ (c + 1) ≤ n ^ (a + c) := by
    apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne n))
    omega
  have hba : n ^ (b + 1) ≤ n ^ (a + b) := by
    apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne n))
    omega
  simp [survivingExponentABC]
  omega

lemma totalExponentABC_eq_explicit {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) :
    totalExponentABC a b c n =
      n ^ (a + b) + n ^ (a + c) + n ^ (b + c) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b +
        (n - 1) ^ 2 := by
  rw [totalExponentABC, survivingExponentABC_eq_explicit (a := a) (b := b) (c := c) (n := n) ha]
  have hca : n ^ (c + 1) ≤ n ^ (a + c) := by
    apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne n))
    omega
  have hba : n ^ (b + 1) ≤ n ^ (a + b) := by
    apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne n))
    omega
  omega

lemma surviving_exponent_222 {n : ℕ} [NeZero n] :
    survivingExponentABC 2 2 2 n = 2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1 := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
  have h32 : n ^ 2 ≤ n ^ 3 := by
    calc
      n ^ 2 = n ^ 2 * 1 := by simp
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_left _ hn
      _ = n ^ 3 := by simp [pow_succ]
  have h43 : n ^ 3 ≤ n ^ 4 := by
    calc
      n ^ 3 = n ^ 3 * 1 := by simp
      _ ≤ n ^ 3 * n := Nat.mul_le_mul_left _ hn
      _ = n ^ 4 := by simp [pow_succ]
  have hrewrite :
      survivingExponentABC 2 2 2 n
        = (n - 1) ^ 2 + (2 * (n ^ 4 - n ^ 3 + n ^ 2)) := by
    simp [survivingExponentABC]
    omega
  rw [hrewrite]
  exact fiber_exponent_identity (n := n)

lemma total_exponent_222 {n : ℕ} [NeZero n] :
    totalExponentABC 2 2 2 n = 3 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1 := by
  calc
    totalExponentABC 2 2 2 n = n ^ 4 + survivingExponentABC 2 2 2 n := by
      simp [totalExponentABC, survivingExponentABC]
    _ = n ^ 4 + (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
          rw [surviving_exponent_222 (n := n)]
    _ = 3 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1 := by
          exact no13_closed_exponent_from_card (n := n)

lemma total_exponent_222_explicit {n : ℕ} [NeZero n] :
    n ^ (2 + 2) + n ^ (2 + 2) + n ^ (2 + 2) - n ^ (2 + 1) - n ^ (2 + 1) + n ^ 2 + n ^ 2 +
        (n - 1) ^ 2
      = 3 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1 := by
  calc
    n ^ (2 + 2) + n ^ (2 + 2) + n ^ (2 + 2) - n ^ (2 + 1) - n ^ (2 + 1) + n ^ 2 + n ^ 2 +
        (n - 1) ^ 2 = totalExponentABC 2 2 2 n := by
          symm
          exact totalExponentABC_eq_explicit (a := 2) (b := 2) (c := 2) (n := n) (by decide)
    _ = 3 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1 := total_exponent_222 (n := n)

/-! ## Honest normal-form core for `(a,b,c)`

This section restores the actual linear coefficient map and signed-sum reduction on the
normal-form space `AFieldABC × BFieldABC × CFieldABC`.  It does not yet replace the endpoint
closed-form theorems above; it provides the truthful kernel/sum objects that those endpoints
must eventually be rewritten to use. -/

noncomputable def sumCoord {k n : ℕ} [NeZero n] (u : Coord k n) : ZMod n :=
  ∑ i : Fin k, u i

noncomputable abbrev sumY {b n : ℕ} [NeZero n] (y : YCoord b n) : ZMod n := sumCoord y
noncomputable abbrev sumZ {c n : ℕ} [NeZero n] (z : ZCoord c n) : ZMod n := sumCoord z

noncomputable def alphaCoeffABC {b c n : ℕ} [NeZero n]
    (coeff A : AFieldABC b c n) : F₂ :=
  ∑ u : ASiteABC b c n, A u * coeff u

noncomputable def alphaSignedABC {b c n : ℕ} [NeZero n]
    (coeff A : AFieldABC b c n) : ℤ :=
  bitSign (alphaCoeffABC coeff A)

def toggleAtABC {b c n : ℕ} [NeZero n] (u0 : ASiteABC b c n)
    (A : AFieldABC b c n) : AFieldABC b c n :=
  fun u => A u + if u = u0 then 1 else 0

noncomputable def toggleEquivABC {b c n : ℕ} [NeZero n] (u0 : ASiteABC b c n) :
    AFieldABC b c n ≃ AFieldABC b c n where
  toFun := toggleAtABC u0
  invFun := toggleAtABC u0
  left_inv A := by
    ext u
    by_cases h : u = u0
    · subst h
      have h11 : (1 : F₂) + 1 = 0 := by decide
      simp [toggleAtABC, add_assoc, h11]
    · simp [toggleAtABC, h]
  right_inv := by
    intro A
    ext u
    by_cases h : u = u0
    · subst h
      have h11 : (1 : F₂) + 1 = 0 := by decide
      simp [toggleAtABC, add_assoc, h11]
    · simp [toggleAtABC, h]

lemma alphaCoeffABC_toggleAtABC {b c n : ℕ} [NeZero n]
    (coeff A : AFieldABC b c n) (u0 : ASiteABC b c n) :
    alphaCoeffABC coeff (toggleAtABC u0 A) = alphaCoeffABC coeff A + coeff u0 := by
  classical
  unfold alphaCoeffABC toggleAtABC
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hs :
      ∑ u : ASiteABC b c n, (if u = u0 then 1 else 0) * coeff u = coeff u0 := by
    simp
  simpa [hs]

lemma alphaSignedABC_toggleAtABC {b c n : ℕ} [NeZero n]
    (coeff A : AFieldABC b c n) (u0 : ASiteABC b c n) (hc : coeff u0 = 1) :
    alphaSignedABC coeff (toggleAtABC u0 A) = -alphaSignedABC coeff A := by
  unfold alphaSignedABC
  rw [alphaCoeffABC_toggleAtABC, hc, bitSign_add_one]

noncomputable def alphaSignedSumABC {b c n : ℕ} [NeZero n]
    (coeff : AFieldABC b c n) : ℤ :=
  ∑ A : AFieldABC b c n, alphaSignedABC coeff A

lemma alphaSignedSumABC_zero {b c n : ℕ} [NeZero n] :
    alphaSignedSumABC (b := b) (c := c) (n := n) 0 = (2 : ℤ) ^ (n ^ (b + c)) := by
  unfold alphaSignedSumABC alphaSignedABC alphaCoeffABC
  have hcard : (((Fintype.card (AFieldABC b c n)) : ℕ) : ℤ) = (2 : ℤ) ^ (n ^ (b + c)) := by
    rw [card_AFieldABC]
    norm_num
  calc
    ∑ A : AFieldABC b c n, bitSign (∑ u : ASiteABC b c n, A u * (0 : AFieldABC b c n) u)
        = ∑ A : AFieldABC b c n, (1 : ℤ) := by
            congr with A
            simp [bitSign_zero]
    _ = Fintype.card (AFieldABC b c n) := by simp
    _ = (2 : ℤ) ^ (n ^ (b + c)) := hcard

theorem alphaSignedSumABC_formula {b c n : ℕ} [NeZero n]
    (coeff : AFieldABC b c n) :
    alphaSignedSumABC (b := b) (c := c) (n := n) coeff =
      if coeff = 0 then (2 : ℤ) ^ (n ^ (b + c)) else 0 := by
  classical
  by_cases hcoeff : coeff = 0
  · simp [hcoeff, alphaSignedSumABC_zero]
  · have hne : ∃ u0 : ASiteABC b c n, coeff u0 ≠ 0 := by
      by_contra hforall
      push_neg at hforall
      apply hcoeff
      ext u
      exact hforall u
    rcases hne with ⟨u0, hu0⟩
    have hcu0 : coeff u0 = 1 := F2_ne_zero_eq_one _ hu0
    have hs :
        alphaSignedSumABC (b := b) (c := c) (n := n) coeff =
          -alphaSignedSumABC (b := b) (c := c) (n := n) coeff := by
      unfold alphaSignedSumABC
      calc
        ∑ A : AFieldABC b c n, alphaSignedABC coeff A
            = ∑ A : AFieldABC b c n, alphaSignedABC coeff (toggleAtABC u0 A) := by
                simpa using
                  (((toggleEquivABC (b := b) (c := c) (n := n) u0).sum_comp
                    (fun A : AFieldABC b c n => alphaSignedABC coeff A)).symm)
        _ = ∑ A : AFieldABC b c n, -alphaSignedABC coeff A := by
              congr with A
              exact alphaSignedABC_toggleAtABC coeff A u0 hcu0
        _ = -∑ A : AFieldABC b c n, alphaSignedABC coeff A := by
              simp
    have hz : alphaSignedSumABC (b := b) (c := c) (n := n) coeff = 0 := by
      linarith
    simp [hcoeff, hz]

noncomputable def coeffFromBC_abc_real {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) : AFieldABC b c n :=
  fun yz =>
    ∑ p : XCoord a n,
      (B (p, sumY yz.1, yz.2) +
        B (p, sumY yz.1 + 1, yz.2) +
        C (p, yz.1, sumZ yz.2) +
        C (p, yz.1, sumZ yz.2 + 1))

set_option maxHeartbeats 800000 in
lemma coeffFromBC_abc_real_add_add {a b c n : ℕ} [NeZero n]
    (B1 B2 : BFieldABC a c n) (C1 C2 : CFieldABC a b n) :
    coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) (B1 + B2) (C1 + C2) =
      coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B1 C1 +
        coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B2 C2 := by
  funext yz
  unfold coeffFromBC_abc_real
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  simp [add_assoc, add_left_comm, add_comm]

lemma coeffFromBC_abc_real_zero_zero {a b c n : ℕ} [NeZero n] :
    coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n)
      (0 : BFieldABC a c n) (0 : CFieldABC a b n) = 0 := by
  funext yz
  simp [coeffFromBC_abc_real]

lemma coeffFromBC_abc_real_smul_pair {a b c n : ℕ} [NeZero n]
    (r : F₂) (B : BFieldABC a c n) (C : CFieldABC a b n) :
    coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) (r • B) (r • C) =
      r • coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B C := by
  rcases eq_or_ne r 0 with hr0 | hr1
  · subst hr0
    ext yz
    simp [coeffFromBC_abc_real_zero_zero, Pi.smul_apply]
  · rw [ZMod_two_eq_one_of_ne_zero hr1]
    simp [one_smul]

noncomputable def coeffFromBCLinearMap_abc_real {a b c n : ℕ} [NeZero n] :
    (BFieldABC a c n × CFieldABC a b n) →ₗ[F₂] AFieldABC b c n where
  toFun bc := coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) bc.1 bc.2
  map_add' bc1 bc2 := by
    rcases bc1 with ⟨B1, C1⟩
    rcases bc2 with ⟨B2, C2⟩
    simpa using coeffFromBC_abc_real_add_add (a := a) (b := b) (c := c) (n := n) B1 B2 C1 C2
  map_smul' r bc := by
    rcases bc with ⟨B, C⟩
    simpa using coeffFromBC_abc_real_smul_pair (a := a) (b := b) (c := c) (n := n) r B C

abbrev SurvivingBC_abc_real (a b c n : ℕ) [NeZero n] :=
  { bc : BFieldABC a c n × CFieldABC a b n //
      coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) bc.1 bc.2 = 0 }

noncomputable def W_abc_real {a b c n : ℕ} [NeZero n]
    (nf : ABCNormalForm a b c n) : ℤ :=
  alphaSignedABC (b := b) (c := c) (n := n)
    (coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2) nf.1

noncomputable def deltaABCraw_real {a b c n : ℕ} [NeZero n] : ℤ :=
  ∑ nf : ABCNormalForm a b c n, W_abc_real (a := a) (b := b) (c := c) (n := n) nf

lemma sum_W_abc_real_over_A {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) :
    ∑ A : AFieldABC b c n,
        W_abc_real (a := a) (b := b) (c := c) (n := n) (A, B, C)
      = if coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B C = 0
          then (2 : ℤ) ^ (n ^ (b + c))
          else 0 := by
  calc
    ∑ A : AFieldABC b c n,
        W_abc_real (a := a) (b := b) (c := c) (n := n) (A, B, C)
        = ∑ A : AFieldABC b c n,
            alphaSignedABC (b := b) (c := c) (n := n)
              (coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B C) A := by
            rfl
    _ = if coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B C = 0
          then (2 : ℤ) ^ (n ^ (b + c))
          else 0 := by
            simpa using alphaSignedSumABC_formula (b := b) (c := c) (n := n)
              (coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B C)

lemma deltaABCraw_real_eq_sum_survivingIndicator {a b c n : ℕ} [NeZero n] :
    deltaABCraw_real (a := a) (b := b) (c := c) (n := n)
      = ∑ q : BFieldABC a c n × CFieldABC a b n,
          if coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) q.1 q.2 = 0
            then (2 : ℤ) ^ (n ^ (b + c))
            else 0 := by
  unfold deltaABCraw_real
  rw [Fintype.sum_prod_type_right]
  congr with q
  simpa using sum_W_abc_real_over_A (a := a) (b := b) (c := c) (n := n) q.1 q.2

lemma deltaABCraw_real_eq_survivingBC_card {a b c n : ℕ} [NeZero n] :
    deltaABCraw_real (a := a) (b := b) (c := c) (n := n) =
      (2 : ℤ) ^ (n ^ (b + c)) * Fintype.card (SurvivingBC_abc_real a b c n) := by
  classical
  let p : BFieldABC a c n × CFieldABC a b n → Prop := fun q =>
    coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) q.1 q.2 = 0
  let a0 : ℤ := (2 : ℤ) ^ (n ^ (b + c))
  rw [deltaABCraw_real_eq_sum_survivingIndicator]
  have hsum :
      (∑ q : BFieldABC a c n × CFieldABC a b n, if p q then a0 else 0)
        = ((Finset.univ.filter p).card : ℤ) * a0 := by
    simpa using
      sum_ite_const_eq_card_filter
        (s := (Finset.univ : Finset (BFieldABC a c n × CFieldABC a b n))) (p := p) (a := a0)
  have hcardNat :
      (Finset.univ.filter p).card = Fintype.card (SurvivingBC_abc_real a b c n) := by
    simpa [SurvivingBC_abc_real, p] using (Fintype.card_subtype p).symm
  have hcard : ((Finset.univ.filter p).card : ℤ) = Fintype.card (SurvivingBC_abc_real a b c n) := by
    exact_mod_cast hcardNat
  calc
    (∑ q : BFieldABC a c n × CFieldABC a b n,
        if coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) q.1 q.2 = 0
          then (2 : ℤ) ^ (n ^ (b + c))
          else 0)
        = ((Finset.univ.filter p).card : ℤ) * a0 := by
            simpa [p, a0] using hsum
    _ = Fintype.card (SurvivingBC_abc_real a b c n) * a0 := by rw [hcard]
    _ = (2 : ℤ) ^ (n ^ (b + c)) * Fintype.card (SurvivingBC_abc_real a b c n) := by
          simp [a0, mul_comm]

noncomputable def bKernelABC_real {a c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (s : ZMod n) (z : ZCoord c n) : F₂ :=
  ∑ p : XCoord a n, (B (p, s, z) + B (p, s + 1, z))

noncomputable def cKernelABC_real {a b n : ℕ} [NeZero n]
    (C : CFieldABC a b n) (y : YCoord b n) (r : ZMod n) : F₂ :=
  ∑ p : XCoord a n, (C (p, y, r) + C (p, y, r + 1))

lemma coeffFromBC_abc_real_eq_kernels {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) (yz : ASiteABC b c n) :
    coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B C yz =
      bKernelABC_real (a := a) (c := c) (n := n) B (sumY yz.1) yz.2 +
        cKernelABC_real (a := a) (b := b) (n := n) C yz.1 (sumZ yz.2) := by
  unfold coeffFromBC_abc_real bKernelABC_real cKernelABC_real
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  simp [add_assoc, add_left_comm, add_comm]

lemma F2_add_eq_zero_iff_eq' (u v : F₂) : u + v = 0 ↔ u = v := by
  simpa using (add_eq_zero_iff_eq_neg : u + v = 0 ↔ u = -v)

lemma coeffFromBC_abc_real_eq_zero_iff {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) :
    coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B C = 0 ↔
      ∀ yz : ASiteABC b c n,
        bKernelABC_real (a := a) (c := c) (n := n) B (sumY yz.1) yz.2 =
          cKernelABC_real (a := a) (b := b) (n := n) C yz.1 (sumZ yz.2) := by
  constructor
  · intro h yz
    have hyz : coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B C yz = 0 := by
      simpa [h]
    have hyz' :
        bKernelABC_real (a := a) (c := c) (n := n) B (sumY yz.1) yz.2 +
          cKernelABC_real (a := a) (b := b) (n := n) C yz.1 (sumZ yz.2) = 0 := by
      simpa [coeffFromBC_abc_real_eq_kernels] using hyz
    exact (F2_add_eq_zero_iff_eq' _ _).1 hyz'
  · intro h
    ext yz
    have hyz' :
        bKernelABC_real (a := a) (c := c) (n := n) B (sumY yz.1) yz.2 +
          cKernelABC_real (a := a) (b := b) (n := n) C yz.1 (sumZ yz.2) = 0 := by
      exact (F2_add_eq_zero_iff_eq' _ _).2 (h yz)
    simpa [coeffFromBC_abc_real_eq_kernels] using hyz'

abbrev BProfileRawABC (c n : ℕ) := ZMod n → ZCoord c n → F₂
abbrev CProfileRawABC (b n : ℕ) := YCoord b n → ZMod n → F₂
abbrev BProfileSumCodomainABC (c n : ℕ) := ZCoord c n → F₂
abbrev CProfileSumCodomainABC (b n : ℕ) := YCoord b n → F₂

noncomputable def BProfileRawABC_equiv_pair (c n : ℕ) [NeZero n] :
    BProfileRawABC c n ≃ₗ[F₂] (ZMod n × ZCoord c n → F₂) where
  toFun f := fun p => f p.1 p.2
  invFun g := fun s z => g (s, z)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def CProfileRawABC_equiv_pair (b n : ℕ) [NeZero n] :
    CProfileRawABC b n ≃ₗ[F₂] (YCoord b n × ZMod n → F₂) where
  toFun f := fun p => f p.1 p.2
  invFun g := fun y r => g (y, r)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma finrank_BProfileRawABC (c n : ℕ) [NeZero n] :
    Module.finrank F₂ (BProfileRawABC c n) = n ^ (c + 1) := by
  rw [(BProfileRawABC_equiv_pair (c := c) (n := n)).finrank_eq, Module.finrank_fintype_fun_eq_card]
  rw [Fintype.card_prod, card_ZCoord]
  simp [ZMod.card, Nat.pow_add, Nat.mul_comm]

lemma finrank_CProfileRawABC (b n : ℕ) [NeZero n] :
    Module.finrank F₂ (CProfileRawABC b n) = n ^ (b + 1) := by
  rw [(CProfileRawABC_equiv_pair (b := b) (n := n)).finrank_eq, Module.finrank_fintype_fun_eq_card]
  rw [Fintype.card_prod, card_YCoord]
  simp [ZMod.card, Nat.pow_add, Nat.mul_comm]

lemma finrank_BProfileSumCodomainABC (c n : ℕ) [NeZero n] :
    Module.finrank F₂ (BProfileSumCodomainABC c n) = n ^ c := by
  simpa [BProfileSumCodomainABC, card_ZCoord] using
    (Module.finrank_fintype_fun_eq_card (R := F₂) (η := ZCoord c n))

lemma finrank_CProfileSumCodomainABC (b n : ℕ) [NeZero n] :
    Module.finrank F₂ (CProfileSumCodomainABC b n) = n ^ b := by
  simpa [CProfileSumCodomainABC, card_YCoord] using
    (Module.finrank_fintype_fun_eq_card (R := F₂) (η := YCoord b n))

noncomputable def bProfileSumConstraintLinearMap_abc {c n : ℕ} [NeZero n] :
    BProfileRawABC c n →ₗ[F₂] BProfileSumCodomainABC c n where
  toFun f := fun z => ∑ s : ZMod n, f s z
  map_add' f g := by
    funext z
    simp [Finset.sum_add_distrib]
  map_smul' r f := by
    funext z
    simp_rw [Pi.smul_apply]
    convert (Finset.smul_sum (f := fun s => f s z) (s := Finset.univ)).symm using 1

noncomputable def cProfileSumConstraintLinearMap_abc {b n : ℕ} [NeZero n] :
    CProfileRawABC b n →ₗ[F₂] CProfileSumCodomainABC b n where
  toFun f := fun y => ∑ r : ZMod n, f y r
  map_add' f g := by
    funext y
    simp [Finset.sum_add_distrib]
  map_smul' r f := by
    funext y
    simp_rw [Pi.smul_apply]
    convert (Finset.smul_sum (f := fun r => f y r) (s := Finset.univ)).symm using 1

lemma bProfileSumConstraintLinearMap_abc_surjective {c n : ℕ} [NeZero n] :
    Function.Surjective (bProfileSumConstraintLinearMap_abc (c := c) (n := n)) := by
  intro g
  refine ⟨fun s z => if s = (0 : ZMod n) then g z else 0, ?_⟩
  funext z
  dsimp [bProfileSumConstraintLinearMap_abc]
  rw [Finset.sum_eq_single (0 : ZMod n)]
  · simp
  · intro s hs hs0
    dsimp
    rw [if_neg hs0]
  · simp

lemma cProfileSumConstraintLinearMap_abc_surjective {b n : ℕ} [NeZero n] :
    Function.Surjective (cProfileSumConstraintLinearMap_abc (b := b) (n := n)) := by
  intro g
  refine ⟨fun y r => if r = (0 : ZMod n) then g y else 0, ?_⟩
  funext y
  dsimp [cProfileSumConstraintLinearMap_abc]
  rw [Finset.sum_eq_single (0 : ZMod n)]
  · simp
  · intro r hr hr0
    dsimp
    rw [if_neg hr0]
  · simp

noncomputable def BProfileAdmSubmoduleABC (c n : ℕ) [NeZero n] : Submodule F₂ (BProfileRawABC c n) :=
  LinearMap.ker (bProfileSumConstraintLinearMap_abc (c := c) (n := n))

noncomputable def CProfileAdmSubmoduleABC (b n : ℕ) [NeZero n] : Submodule F₂ (CProfileRawABC b n) :=
  LinearMap.ker (cProfileSumConstraintLinearMap_abc (b := b) (n := n))

lemma mem_BProfileAdmSubmoduleABC_iff {c n : ℕ} [NeZero n] (f : BProfileRawABC c n) :
    f ∈ BProfileAdmSubmoduleABC c n ↔ ∀ z : ZCoord c n, (∑ s : ZMod n, f s z) = 0 := by
  rw [BProfileAdmSubmoduleABC, LinearMap.mem_ker]
  constructor
  · intro hf z
    simpa [bProfileSumConstraintLinearMap_abc, Pi.zero_apply] using congr_arg (fun g => g z) hf
  · intro hf
    ext z
    simpa [bProfileSumConstraintLinearMap_abc, Pi.zero_apply] using hf z

lemma mem_CProfileAdmSubmoduleABC_iff {b n : ℕ} [NeZero n] (f : CProfileRawABC b n) :
    f ∈ CProfileAdmSubmoduleABC b n ↔ ∀ y : YCoord b n, (∑ r : ZMod n, f y r) = 0 := by
  rw [CProfileAdmSubmoduleABC, LinearMap.mem_ker]
  constructor
  · intro hf y
    simpa [cProfileSumConstraintLinearMap_abc, Pi.zero_apply] using congr_arg (fun g => g y) hf
  · intro hf
    ext y
    simpa [cProfileSumConstraintLinearMap_abc, Pi.zero_apply] using hf y

lemma finrank_BProfileAdmSubmoduleABC {c n : ℕ} [NeZero n] :
    Module.finrank F₂ (BProfileAdmSubmoduleABC c n) = n ^ (c + 1) - n ^ c := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (bProfileSumConstraintLinearMap_abc (c := c) (n := n))
  have hrng :
      Module.finrank F₂ (LinearMap.range (bProfileSumConstraintLinearMap_abc (c := c) (n := n))) = n ^ c := by
    have htop : LinearMap.range (bProfileSumConstraintLinearMap_abc (c := c) (n := n)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact LinearMap.mem_range.2 (bProfileSumConstraintLinearMap_abc_surjective (c := c) (n := n) x)
    rw [htop, finrank_top, finrank_BProfileSumCodomainABC]
  have hdom := finrank_BProfileRawABC (c := c) (n := n)
  rw [hrng, hdom] at hsum
  have hle : n ^ c ≤ n ^ (c + 1) := by
    rw [Nat.pow_succ]
    calc
      n ^ c = n ^ c * 1 := by simp
      _ ≤ n ^ c * n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n)))
  have hker :
      Module.finrank F₂ (LinearMap.ker (bProfileSumConstraintLinearMap_abc (c := c) (n := n)))
        = n ^ (c + 1) - n ^ c := by
    omega
  simpa [BProfileAdmSubmoduleABC] using hker

lemma finrank_CProfileAdmSubmoduleABC {b n : ℕ} [NeZero n] :
    Module.finrank F₂ (CProfileAdmSubmoduleABC b n) = n ^ (b + 1) - n ^ b := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (cProfileSumConstraintLinearMap_abc (b := b) (n := n))
  have hrng :
      Module.finrank F₂ (LinearMap.range (cProfileSumConstraintLinearMap_abc (b := b) (n := n))) = n ^ b := by
    have htop : LinearMap.range (cProfileSumConstraintLinearMap_abc (b := b) (n := n)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact LinearMap.mem_range.2 (cProfileSumConstraintLinearMap_abc_surjective (b := b) (n := n) x)
    rw [htop, finrank_top, finrank_CProfileSumCodomainABC]
  have hdom := finrank_CProfileRawABC (b := b) (n := n)
  rw [hrng, hdom] at hsum
  have hle : n ^ b ≤ n ^ (b + 1) := by
    rw [Nat.pow_succ]
    calc
      n ^ b = n ^ b * 1 := by simp
      _ ≤ n ^ b * n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n)))
  have hker :
      Module.finrank F₂ (LinearMap.ker (cProfileSumConstraintLinearMap_abc (b := b) (n := n)))
        = n ^ (b + 1) - n ^ b := by
    omega
  simpa [CProfileAdmSubmoduleABC] using hker

noncomputable def bProfileLinearMap_abc_real {a c n : ℕ} [NeZero n] :
    BFieldABC a c n →ₗ[F₂] BProfileRawABC c n where
  toFun B := fun s z => bKernelABC_real (a := a) (c := c) (n := n) B s z
  map_add' B1 B2 := by
    funext s z
    unfold bKernelABC_real
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    simp [add_assoc, add_left_comm, add_comm]
  map_smul' r B := by
    rcases eq_or_ne r 0 with hr0 | hr1
    · subst hr0
      funext s z
      simp [bKernelABC_real, Pi.smul_apply]
    · rw [ZMod_two_eq_one_of_ne_zero hr1]
      simp [one_smul]

noncomputable def cProfileLinearMap_abc_real {a b n : ℕ} [NeZero n] :
    CFieldABC a b n →ₗ[F₂] CProfileRawABC b n where
  toFun C := fun y r => cKernelABC_real (a := a) (b := b) (n := n) C y r
  map_add' C1 C2 := by
    funext y r
    unfold cKernelABC_real
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    simp [add_assoc, add_left_comm, add_comm]
  map_smul' r C := by
    rcases eq_or_ne r 0 with hr0 | hr1
    · subst hr0
      funext y r
      simp [cKernelABC_real, Pi.smul_apply]
    · rw [ZMod_two_eq_one_of_ne_zero hr1]
      simp [one_smul]

lemma sum_bKernelABC_real_over_s_zero {a c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (z : ZCoord c n) :
    (∑ s : ZMod n, bKernelABC_real (a := a) (c := c) (n := n) B s z) = 0 := by
  let g : XCoord a n → ZMod n → F₂ := fun p s => B (p, s, z)
  calc
    (∑ s : ZMod n, bKernelABC_real (a := a) (c := c) (n := n) B s z)
        = ∑ p : XCoord a n, ∑ s : ZMod n, (g p s + g p (s + 1)) := by
            unfold bKernelABC_real
            rw [Finset.sum_comm]
    _ = ∑ p : XCoord a n, ((∑ s : ZMod n, g p s) + ∑ s : ZMod n, g p (s + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [Finset.sum_add_distrib]
    _ = ∑ p : XCoord a n, ((∑ s : ZMod n, g p s) + ∑ s : ZMod n, g p s) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [sum_zmod_add_right (f := g p) (a := (1 : ZMod n))]
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro p hp
          simpa using F2_add_self (∑ s : ZMod n, g p s)

lemma sum_cKernelABC_real_over_r_zero {a b n : ℕ} [NeZero n]
    (C : CFieldABC a b n) (y : YCoord b n) :
    (∑ r : ZMod n, cKernelABC_real (a := a) (b := b) (n := n) C y r) = 0 := by
  let g : XCoord a n → ZMod n → F₂ := fun p r => C (p, y, r)
  calc
    (∑ r : ZMod n, cKernelABC_real (a := a) (b := b) (n := n) C y r)
        = ∑ p : XCoord a n, ∑ r : ZMod n, (g p r + g p (r + 1)) := by
            unfold cKernelABC_real
            rw [Finset.sum_comm]
    _ = ∑ p : XCoord a n, ((∑ r : ZMod n, g p r) + ∑ r : ZMod n, g p (r + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [Finset.sum_add_distrib]
    _ = ∑ p : XCoord a n, ((∑ r : ZMod n, g p r) + ∑ r : ZMod n, g p r) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [sum_zmod_add_right (f := g p) (a := (1 : ZMod n))]
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro p hp
          simpa using F2_add_self (∑ r : ZMod n, g p r)

lemma bProfileSumConstraint_comp_bProfileLinearMap_abc_real_eq_zero {a c n : ℕ} [NeZero n] :
    bProfileSumConstraintLinearMap_abc (c := c) (n := n) ∘ₗ
      bProfileLinearMap_abc_real (a := a) (c := c) (n := n) = 0 := by
  refine LinearMap.ext ?_
  intro B
  ext z
  simpa [LinearMap.comp_apply, bProfileSumConstraintLinearMap_abc, bProfileLinearMap_abc_real] using
    sum_bKernelABC_real_over_s_zero (a := a) (c := c) (n := n) B z

lemma cProfileSumConstraint_comp_cProfileLinearMap_abc_real_eq_zero {a b n : ℕ} [NeZero n] :
    cProfileSumConstraintLinearMap_abc (b := b) (n := n) ∘ₗ
      cProfileLinearMap_abc_real (a := a) (b := b) (n := n) = 0 := by
  refine LinearMap.ext ?_
  intro C
  ext y
  simpa [LinearMap.comp_apply, cProfileSumConstraintLinearMap_abc, cProfileLinearMap_abc_real] using
    sum_cKernelABC_real_over_r_zero (a := a) (b := b) (n := n) C y

noncomputable def coordSingle {k n : ℕ} [NeZero n] (hk : 0 < k) (t : ZMod n) : Coord k n :=
  fun i => if i = ⟨0, hk⟩ then t else 0

lemma sumCoord_coordSingle {k n : ℕ} [NeZero n] (hk : 0 < k) (t : ZMod n) :
    sumCoord (coordSingle (k := k) (n := n) hk t) = t := by
  classical
  unfold sumCoord coordSingle
  rw [Finset.sum_eq_single ⟨0, hk⟩]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

noncomputable abbrev yOfSum {b n : ℕ} [NeZero n] (hb : 0 < b) (s : ZMod n) : YCoord b n :=
  coordSingle (k := b) (n := n) hb s

noncomputable abbrev zOfSum {c n : ℕ} [NeZero n] (hc : 0 < c) (r : ZMod n) : ZCoord c n :=
  coordSingle (k := c) (n := n) hc r

@[simp] lemma sumY_yOfSum {b n : ℕ} [NeZero n] (hb : 0 < b) (s : ZMod n) :
    sumY (yOfSum (n := n) hb s) = s := by
  simpa [yOfSum] using sumCoord_coordSingle (k := b) (n := n) hb s

@[simp] lemma sumZ_zOfSum {c n : ℕ} [NeZero n] (hc : 0 < c) (r : ZMod n) :
    sumZ (zOfSum (n := n) hc r) = r := by
  simpa [zOfSum] using sumCoord_coordSingle (k := c) (n := n) hc r

lemma sumCoord_add_single {k n : ℕ} [NeZero n] (u : Coord k n) (i : Fin k) (t : ZMod n) :
    sumCoord (u + Pi.single i t) = sumCoord u + t := by
  classical
  unfold sumCoord
  simp_rw [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  have hs : (∑ j : Fin k, (Pi.single i t) j) = t := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  simp [hs]

@[simp] lemma sumY_add_single {b n : ℕ} [NeZero n]
    (y : YCoord b n) (i : Fin b) :
    sumY (y + Pi.single i 1) = sumY y + 1 := by
  simpa [sumY] using sumCoord_add_single (u := y) (i := i) (t := (1 : ZMod n))

@[simp] lemma sumZ_add_single {c n : ℕ} [NeZero n]
    (z : ZCoord c n) (i : Fin c) :
    sumZ (z + Pi.single i 1) = sumZ z + 1 := by
  simpa [sumZ] using sumCoord_add_single (u := z) (i := i) (t := (1 : ZMod n))

lemma sub_single_succ_add_single_one {k n : ℕ} [NeZero n]
    (u : Coord k n) (j : Fin k) (t : ZMod n) :
    (u - Pi.single j (t + 1)) + Pi.single j 1 = u - Pi.single j t := by
  ext i
  by_cases hij : i = j
  · subst hij
    simp [sub_eq_add_neg, add_assoc]
  · simp [Pi.single_apply, hij, sub_eq_add_neg, add_assoc]

/-! ## Honest raw assignment layer for `(a,b,c)`

This is the first upward extension of the honest `*_real` normal-form chain back to a genuine
raw 5-field assignment space.  The validity notion below is no longer the scaffold `True`; it is
an actual dependency/shift condition on raw fields.  The remaining gap to a fully faithful raw
bit-string formalization is to replace these dependency clauses by the original pure
contraction/shift axioms and then identify the resulting signed sum with `deltaABCraw_real`. -/

abbrev RawSiteABC (a b c n : ℕ) := XCoord a n × YCoord b n × ZCoord c n

structure RawAssignmentABC (a b c n : ℕ) where
  alpha : RawSiteABC a b c n → F₂
  beta : RawSiteABC a b c n → F₂
  gamma : RawSiteABC a b c n → F₂
  delta : RawSiteABC a b c n → F₂
  eta : RawSiteABC a b c n → F₂

def rawAssignmentABCEquivProd (a b c n : ℕ) :
    RawAssignmentABC a b c n ≃
      (RawSiteABC a b c n → F₂) ×
        ((RawSiteABC a b c n → F₂) ×
          ((RawSiteABC a b c n → F₂) ×
            ((RawSiteABC a b c n → F₂) × (RawSiteABC a b c n → F₂)))) where
  toFun S := ⟨S.alpha, ⟨S.beta, S.gamma, S.delta, S.eta⟩⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[ext] theorem RawAssignmentABC.ext {a b c n : ℕ} {S T : RawAssignmentABC a b c n}
    (hα : S.alpha = T.alpha) (hβ : S.beta = T.beta) (hγ : S.gamma = T.gamma)
    (hδ : S.delta = T.delta) (hη : S.eta = T.eta) : S = T := by
  cases S
  cases T
  simp_all

structure RawValidPrimitiveABC {a b c n : ℕ} [NeZero n] (S : RawAssignmentABC a b c n) : Prop where
  alpha_x_indep :
    ∀ (x x' : XCoord a n) (y : YCoord b n) (z : ZCoord c n), S.alpha (x, y, z) = S.alpha (x', y, z)
  gamma_beta_shift :
    ∀ (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n) (i : Fin b),
      S.gamma (x, y, z) = S.beta (x, y + Pi.single i 1, z)
  eta_delta_shift :
    ∀ (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n) (i : Fin c),
      S.eta (x, y, z) = S.delta (x, y, z + Pi.single i 1)

structure RawValidABC {a b c n : ℕ} [NeZero n] (S : RawAssignmentABC a b c n) : Prop where
  alpha_x_indep :
    ∀ (x x' : XCoord a n) (y : YCoord b n) (z : ZCoord c n), S.alpha (x, y, z) = S.alpha (x', y, z)
  beta_sum_indep :
    ∀ (x : XCoord a n) (y y' : YCoord b n) (z : ZCoord c n),
      sumY y = sumY y' → S.beta (x, y, z) = S.beta (x, y', z)
  gamma_beta_shift :
    ∀ (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n) (i : Fin b),
      S.gamma (x, y, z) = S.beta (x, y + Pi.single i 1, z)
  delta_sum_indep :
    ∀ (x : XCoord a n) (y : YCoord b n) (z z' : ZCoord c n),
      sumZ z = sumZ z' → S.delta (x, y, z) = S.delta (x, y, z')
  eta_delta_shift :
    ∀ (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n) (i : Fin c),
      S.eta (x, y, z) = S.delta (x, y, z + Pi.single i 1)

abbrev RawValidPrimitiveAssignmentsABC (a b c n : ℕ) [NeZero n] :=
  { S : RawAssignmentABC a b c n // RawValidPrimitiveABC S }

lemma rawValidABC_to_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidABC S) :
    RawValidPrimitiveABC S := by
  exact ⟨hS.alpha_x_indep, hS.gamma_beta_shift, hS.eta_delta_shift⟩

def baseCoord {k : ℕ} (hk : 0 < k) : Fin k := ⟨0, hk⟩

def transferToBaseY {b n : ℕ} [NeZero n] (hb : 0 < b) (y : YCoord b n) (j : Fin b) : YCoord b n :=
  y + Pi.single (baseCoord hb) (y j) - Pi.single j (y j)

def transferToBaseZ {c n : ℕ} [NeZero n] (hc : 0 < c) (z : ZCoord c n) (j : Fin c) : ZCoord c n :=
  z + Pi.single (baseCoord hc) (z j) - Pi.single j (z j)

lemma beta_shift_eq_of_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidPrimitiveABC S)
    (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n) (i j : Fin b) :
    S.beta (x, y + Pi.single i 1, z) = S.beta (x, y + Pi.single j 1, z) := by
  calc
    S.beta (x, y + Pi.single i 1, z) = S.gamma (x, y, z) := by
      symm
      exact hS.gamma_beta_shift x y z i
    _ = S.beta (x, y + Pi.single j 1, z) := hS.gamma_beta_shift x y z j

lemma delta_shift_eq_of_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidPrimitiveABC S)
    (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n) (i j : Fin c) :
    S.delta (x, y, z + Pi.single i 1) = S.delta (x, y, z + Pi.single j 1) := by
  calc
    S.delta (x, y, z + Pi.single i 1) = S.eta (x, y, z) := by
      symm
      exact hS.eta_delta_shift x y z i
    _ = S.delta (x, y, z + Pi.single j 1) := hS.eta_delta_shift x y z j

lemma beta_transferToBaseY_eq_of_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidPrimitiveABC S)
    (hb : 0 < b) (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n) (j : Fin b) :
    S.beta (x, y, z) = S.beta (x, transferToBaseY hb y j, z) := by
  let i0 : Fin b := baseCoord hb
  let g : ZMod n → F₂ := fun t => S.beta (x, y + Pi.single i0 t - Pi.single j t, z)
  have hg : ∀ t, g (t + 1) = g t := by
    intro t
    have hstep := beta_shift_eq_of_rawValidPrimitiveABC hS x
      (y + Pi.single i0 t - Pi.single j (t + 1)) z i0 j
    calc
      g (t + 1)
          = S.beta
              (x, (y + Pi.single i0 t - Pi.single j (t + 1)) + Pi.single i0 1, z) := by
                simp [g, i0, Pi.single_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = S.beta
            (x, (y + Pi.single i0 t - Pi.single j (t + 1)) + Pi.single j 1, z) := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hstep
      _ = g t := by
            have hcancel :
                ((y + Pi.single i0 t) - Pi.single j (t + 1)) + Pi.single j 1 =
                  (y + Pi.single i0 t) - Pi.single j t :=
              sub_single_succ_add_single_one (u := y + Pi.single i0 t) (j := j) (t := t)
            simpa [g, sub_eq_add_neg, add_assoc] using
              congrArg (fun yy => S.beta (x, yy, z)) hcancel
  have hconst := zmod_step_const (n := n) g hg (y j)
  dsimp [g] at hconst ⊢
  calc
    S.beta (x, y, z) = g 0 := by simp [g]
    _ = g (y j) := hconst.symm
    _ = S.beta (x, transferToBaseY hb y j, z) := by
          simp [transferToBaseY, i0, g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma delta_transferToBaseZ_eq_of_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidPrimitiveABC S)
    (hc : 0 < c) (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n) (j : Fin c) :
    S.delta (x, y, z) = S.delta (x, y, transferToBaseZ hc z j) := by
  let i0 : Fin c := baseCoord hc
  let g : ZMod n → F₂ := fun t => S.delta (x, y, z + Pi.single i0 t - Pi.single j t)
  have hg : ∀ t, g (t + 1) = g t := by
    intro t
    have hstep := delta_shift_eq_of_rawValidPrimitiveABC hS x y
      (z + Pi.single i0 t - Pi.single j (t + 1)) i0 j
    calc
      g (t + 1)
          = S.delta
              (x, y, (z + Pi.single i0 t - Pi.single j (t + 1)) + Pi.single i0 1) := by
                simp [g, i0, Pi.single_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = S.delta
            (x, y, (z + Pi.single i0 t - Pi.single j (t + 1)) + Pi.single j 1) := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hstep
      _ = g t := by
            have hcancel :
                ((z + Pi.single i0 t) - Pi.single j (t + 1)) + Pi.single j 1 =
                  (z + Pi.single i0 t) - Pi.single j t :=
              sub_single_succ_add_single_one (u := z + Pi.single i0 t) (j := j) (t := t)
            simpa [g, sub_eq_add_neg, add_assoc] using
              congrArg (fun zz => S.delta (x, y, zz)) hcancel
  have hconst := zmod_step_const (n := n) g hg (z j)
  dsimp [g] at hconst ⊢
  calc
    S.delta (x, y, z) = g 0 := by simp [g]
    _ = g (z j) := hconst.symm
    _ = S.delta (x, y, transferToBaseZ hc z j) := by
          simp [transferToBaseZ, i0, g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

def collapseSubsetY {b n : ℕ} [NeZero n] (hb : 0 < b)
    (y : YCoord b n) (s : Finset (Fin b)) : YCoord b n :=
  fun i =>
    if h : i = baseCoord hb then y (baseCoord hb) + Finset.sum s (fun j => y j)
    else if hs : i ∈ s then 0 else y i

def collapseSubsetZ {c n : ℕ} [NeZero n] (hc : 0 < c)
    (z : ZCoord c n) (s : Finset (Fin c)) : ZCoord c n :=
  fun i =>
    if h : i = baseCoord hc then z (baseCoord hc) + Finset.sum s (fun j => z j)
    else if hs : i ∈ s then 0 else z i

lemma collapseSubsetY_empty {b n : ℕ} [NeZero n] (hb : 0 < b) (y : YCoord b n) :
    collapseSubsetY hb y ∅ = y := by
  ext i
  by_cases hi : i = baseCoord hb
  · subst hi
    simp [collapseSubsetY]
  · simp [collapseSubsetY, hi]

lemma collapseSubsetZ_empty {c n : ℕ} [NeZero n] (hc : 0 < c) (z : ZCoord c n) :
    collapseSubsetZ hc z ∅ = z := by
  ext i
  by_cases hi : i = baseCoord hc
  · subst hi
    simp [collapseSubsetZ]
  · simp [collapseSubsetZ, hi]

lemma transferToBaseY_collapseSubsetY {b n : ℕ} [NeZero n]
    (hb : 0 < b) (y : YCoord b n) (s : Finset (Fin b)) (j : Fin b)
    (hj : j ∉ s) (hj0 : j ≠ baseCoord hb) :
    transferToBaseY hb (collapseSubsetY hb y s) j = collapseSubsetY hb y (insert j s) := by
  ext i
  by_cases hi0 : i = baseCoord hb
  · subst hi0
    simp [transferToBaseY, collapseSubsetY, hj, hj0, add_assoc, add_left_comm, add_comm]
  · by_cases hij : i = j
    · subst hij
      simp [transferToBaseY, collapseSubsetY, hj, hj0, hi0, add_assoc]
    · by_cases his : i ∈ s
      · simp [transferToBaseY, collapseSubsetY, hj, hj0, hi0, hij, his]
      · simp [transferToBaseY, collapseSubsetY, hj, hj0, hi0, hij, his]

lemma transferToBaseZ_collapseSubsetZ {c n : ℕ} [NeZero n]
    (hc : 0 < c) (z : ZCoord c n) (s : Finset (Fin c)) (j : Fin c)
    (hj : j ∉ s) (hj0 : j ≠ baseCoord hc) :
    transferToBaseZ hc (collapseSubsetZ hc z s) j = collapseSubsetZ hc z (insert j s) := by
  ext i
  by_cases hi0 : i = baseCoord hc
  · subst hi0
    simp [transferToBaseZ, collapseSubsetZ, hj, hj0, add_assoc, add_left_comm, add_comm]
  · by_cases hij : i = j
    · subst hij
      simp [transferToBaseZ, collapseSubsetZ, hj, hj0, hi0, add_assoc]
    · by_cases his : i ∈ s
      · simp [transferToBaseZ, collapseSubsetZ, hj, hj0, hi0, hij, his]
      · simp [transferToBaseZ, collapseSubsetZ, hj, hj0, hi0, hij, his]

lemma beta_eq_collapseSubsetY_of_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidPrimitiveABC S)
    (hb : 0 < b) (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n)
    (s : Finset (Fin b)) (hs : s ⊆ Finset.univ.erase (baseCoord hb)) :
    S.beta (x, y, z) = S.beta (x, collapseSubsetY hb y s, z) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [collapseSubsetY_empty]
  | @insert j s hj ih =>
      have hs' : s ⊆ Finset.univ.erase (baseCoord hb) := by
        intro i hi
        exact hs (by simp [hi])
      have hjmem : j ∈ Finset.univ.erase (baseCoord hb) := hs (by simp [hj])
      have hj0 : j ≠ baseCoord hb := by
        simpa [Finset.mem_erase] using hjmem
      calc
        S.beta (x, y, z) = S.beta (x, collapseSubsetY hb y s, z) := ih hs'
        _ = S.beta (x, transferToBaseY hb (collapseSubsetY hb y s) j, z) := by
              exact beta_transferToBaseY_eq_of_rawValidPrimitiveABC hS hb x (collapseSubsetY hb y s) z j
        _ = S.beta (x, collapseSubsetY hb y (insert j s), z) := by
              rw [transferToBaseY_collapseSubsetY hb y s j hj hj0]

lemma delta_eq_collapseSubsetZ_of_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidPrimitiveABC S)
    (hc : 0 < c) (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n)
    (s : Finset (Fin c)) (hs : s ⊆ Finset.univ.erase (baseCoord hc)) :
    S.delta (x, y, z) = S.delta (x, y, collapseSubsetZ hc z s) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [collapseSubsetZ_empty]
  | @insert j s hj ih =>
      have hs' : s ⊆ Finset.univ.erase (baseCoord hc) := by
        intro i hi
        exact hs (by simp [hi])
      have hjmem : j ∈ Finset.univ.erase (baseCoord hc) := hs (by simp [hj])
      have hj0 : j ≠ baseCoord hc := by
        simpa [Finset.mem_erase] using hjmem
      calc
        S.delta (x, y, z) = S.delta (x, y, collapseSubsetZ hc z s) := ih hs'
        _ = S.delta (x, y, transferToBaseZ hc (collapseSubsetZ hc z s) j) := by
              exact delta_transferToBaseZ_eq_of_rawValidPrimitiveABC hS hc x y (collapseSubsetZ hc z s) j
        _ = S.delta (x, y, collapseSubsetZ hc z (insert j s)) := by
              rw [transferToBaseZ_collapseSubsetZ hc z s j hj hj0]

lemma collapseSubsetY_univ_eq_yOfSum {b n : ℕ} [NeZero n]
    (hb : 0 < b) (y : YCoord b n) :
    collapseSubsetY hb y (Finset.univ.erase (baseCoord hb)) = yOfSum (n := n) hb (sumY y) := by
  ext i
  by_cases hi0 : i = baseCoord hb
  · subst hi0
    have hmem : baseCoord hb ∈ (Finset.univ : Finset (Fin b)) := by simp
    have hsum :
        y (baseCoord hb) + Finset.sum (Finset.univ.erase (baseCoord hb)) (fun j => y j) = sumY y := by
      unfold sumY sumCoord
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := Finset.univ) (f := fun j : Fin b => y j) (a := baseCoord hb) hmem)
    simpa [collapseSubsetY, yOfSum, coordSingle, baseCoord] using hsum
  · have himem : i ∈ Finset.univ.erase (baseCoord hb) := by simp [hi0]
    have hneq0 : i ≠ ⟨0, hb⟩ := by simpa [baseCoord] using hi0
    simp [collapseSubsetY, yOfSum, coordSingle, hi0, himem, hneq0, baseCoord]

lemma collapseSubsetZ_univ_eq_zOfSum {c n : ℕ} [NeZero n]
    (hc : 0 < c) (z : ZCoord c n) :
    collapseSubsetZ hc z (Finset.univ.erase (baseCoord hc)) = zOfSum (n := n) hc (sumZ z) := by
  ext i
  by_cases hi0 : i = baseCoord hc
  · subst hi0
    have hmem : baseCoord hc ∈ (Finset.univ : Finset (Fin c)) := by simp
    have hsum :
        z (baseCoord hc) + Finset.sum (Finset.univ.erase (baseCoord hc)) (fun j => z j) = sumZ z := by
      unfold sumZ sumCoord
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := Finset.univ) (f := fun j : Fin c => z j) (a := baseCoord hc) hmem)
    simpa [collapseSubsetZ, zOfSum, coordSingle, baseCoord] using hsum
  · have himem : i ∈ Finset.univ.erase (baseCoord hc) := by simp [hi0]
    have hneq0 : i ≠ ⟨0, hc⟩ := by simpa [baseCoord] using hi0
    simp [collapseSubsetZ, zOfSum, coordSingle, hi0, himem, hneq0, baseCoord]

lemma beta_eq_yOfSum_of_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidPrimitiveABC S)
    (hb : 0 < b) (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n) :
    S.beta (x, y, z) = S.beta (x, yOfSum (n := n) hb (sumY y), z) := by
  calc
    S.beta (x, y, z)
        = S.beta (x, collapseSubsetY hb y (Finset.univ.erase (baseCoord hb)), z) := by
            exact beta_eq_collapseSubsetY_of_rawValidPrimitiveABC hS hb x y z _ (by intro i hi; exact hi)
    _ = S.beta (x, yOfSum (n := n) hb (sumY y), z) := by
          rw [collapseSubsetY_univ_eq_yOfSum hb y]

lemma delta_eq_zOfSum_of_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidPrimitiveABC S)
    (hc : 0 < c) (x : XCoord a n) (y : YCoord b n) (z : ZCoord c n) :
    S.delta (x, y, z) = S.delta (x, y, zOfSum (n := n) hc (sumZ z)) := by
  calc
    S.delta (x, y, z)
        = S.delta (x, y, collapseSubsetZ hc z (Finset.univ.erase (baseCoord hc))) := by
            exact delta_eq_collapseSubsetZ_of_rawValidPrimitiveABC hS hc x y z _ (by intro i hi; exact hi)
    _ = S.delta (x, y, zOfSum (n := n) hc (sumZ z)) := by
          rw [collapseSubsetZ_univ_eq_zOfSum hc z]

lemma beta_sum_indep_of_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidPrimitiveABC S)
    (hb : 0 < b) (x : XCoord a n) (y y' : YCoord b n) (z : ZCoord c n)
    (hyy : sumY y = sumY y') :
    S.beta (x, y, z) = S.beta (x, y', z) := by
  calc
    S.beta (x, y, z) = S.beta (x, yOfSum (n := n) hb (sumY y), z) := by
      exact beta_eq_yOfSum_of_rawValidPrimitiveABC hS hb x y z
    _ = S.beta (x, yOfSum (n := n) hb (sumY y'), z) := by rw [hyy]
    _ = S.beta (x, y', z) := by
      exact (beta_eq_yOfSum_of_rawValidPrimitiveABC hS hb x y' z).symm

lemma delta_sum_indep_of_rawValidPrimitiveABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hS : RawValidPrimitiveABC S)
    (hc : 0 < c) (x : XCoord a n) (y : YCoord b n) (z z' : ZCoord c n)
    (hzz : sumZ z = sumZ z') :
    S.delta (x, y, z) = S.delta (x, y, z') := by
  calc
    S.delta (x, y, z) = S.delta (x, y, zOfSum (n := n) hc (sumZ z)) := by
      exact delta_eq_zOfSum_of_rawValidPrimitiveABC hS hc x y z
    _ = S.delta (x, y, zOfSum (n := n) hc (sumZ z')) := by rw [hzz]
    _ = S.delta (x, y, z') := by
      exact (delta_eq_zOfSum_of_rawValidPrimitiveABC hS hc x y z').symm

lemma rawValidPrimitiveABC_to_rawValidABC {a b c n : ℕ} [NeZero n]
    {S : RawAssignmentABC a b c n} (hb : 0 < b) (hc : 0 < c) (hS : RawValidPrimitiveABC S) :
    RawValidABC S := by
  refine ⟨hS.alpha_x_indep, ?_, hS.gamma_beta_shift, ?_, hS.eta_delta_shift⟩
  · intro x y y' z hyy
    exact beta_sum_indep_of_rawValidPrimitiveABC hS hb x y y' z hyy
  · intro x y z z' hzz
    exact delta_sum_indep_of_rawValidPrimitiveABC hS hc x y z z' hzz

abbrev RawValidAssignmentsABC (a b c n : ℕ) [NeZero n] :=
  { S : RawAssignmentABC a b c n // RawValidABC S }

noncomputable instance instFintypeRawSiteABC (a b c n : ℕ) [NeZero n] :
    Fintype (RawSiteABC a b c n) := by
  classical
  infer_instance

noncomputable instance instFintypeRawAssignmentABC (a b c n : ℕ) [NeZero n] :
    Fintype (RawAssignmentABC a b c n) := by
  classical
  let R : Type := RawSiteABC a b c n → F₂
  letI : Fintype (RawSiteABC a b c n) := instFintypeRawSiteABC a b c n
  letI : Fintype R := inferInstance
  exact Fintype.ofEquiv (R × (R × (R × (R × R)))) (rawAssignmentABCEquivProd a b c n).symm

noncomputable instance instFintypeRawValidAssignmentsABC (a b c n : ℕ) [NeZero n] :
    Fintype (RawValidAssignmentsABC a b c n) := by
  classical
  exact inferInstance

noncomputable instance instFintypeRawValidPrimitiveAssignmentsABC (a b c n : ℕ) [NeZero n] :
    Fintype (RawValidPrimitiveAssignmentsABC a b c n) := by
  classical
  exact inferInstance

noncomputable def toRawAssignmentABC {a b c n : ℕ} [NeZero n]
    (nf : ABCAssignment a b c n) : RawAssignmentABC a b c n where
  alpha xyz := nf.1 (xyz.2.1, xyz.2.2)
  beta xyz := nf.2.1 (xyz.1, sumY xyz.2.1, xyz.2.2)
  gamma xyz := nf.2.1 (xyz.1, sumY xyz.2.1 + 1, xyz.2.2)
  delta xyz := nf.2.2 (xyz.1, xyz.2.1, sumZ xyz.2.2)
  eta xyz := nf.2.2 (xyz.1, xyz.2.1, sumZ xyz.2.2 + 1)

lemma rawValid_toRawAssignmentABC {a b c n : ℕ} [NeZero n]
    (nf : ABCAssignment a b c n) : RawValidABC (toRawAssignmentABC nf) := by
  constructor
  · intro x x' y z
    simp [toRawAssignmentABC]
  · intro x y y' z hyy
    simp [toRawAssignmentABC, hyy]
  · intro x y z i
    simp [toRawAssignmentABC]
  · intro x y z z' hzz
    simp [toRawAssignmentABC, hzz]
  · intro x y z i
    simp [toRawAssignmentABC]

noncomputable def rawToABCAssignment {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (S : RawAssignmentABC a b c n) (_hS : RawValidABC S) :
    ABCAssignment a b c n where
  fst := fun yz => S.alpha (0, yz.1, yz.2)
  snd := (
    fun bs => S.beta (bs.1, yOfSum (n := n) hb bs.2.1, bs.2.2),
    fun cs => S.delta (cs.1, cs.2.1, zOfSum (n := n) hc cs.2.2))

lemma rawToABCAssignment_toRawAssignmentABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (nf : ABCAssignment a b c n) :
    rawToABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc
        (toRawAssignmentABC nf) (rawValid_toRawAssignmentABC nf)
      = nf := by
  rcases nf with ⟨A, B, C⟩
  apply Prod.ext
  · funext u
    simp [rawToABCAssignment, toRawAssignmentABC]
  · apply Prod.ext
    · funext u
      rcases u with ⟨x, s, z⟩
      simp [rawToABCAssignment, toRawAssignmentABC]
    · funext u
      rcases u with ⟨x, y, r⟩
      simp [rawToABCAssignment, toRawAssignmentABC]

lemma toRawAssignmentABC_rawToABCAssignment {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (S : RawAssignmentABC a b c n) (hS : RawValidABC S) :
    toRawAssignmentABC
        (rawToABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc S hS) = S := by
  apply RawAssignmentABC.ext
  · funext xyz
    rcases xyz with ⟨x, y, z⟩
    simp [toRawAssignmentABC, rawToABCAssignment]
    exact (hS.alpha_x_indep x 0 y z).symm
  · funext xyz
    rcases xyz with ⟨x, y, z⟩
    simp [toRawAssignmentABC, rawToABCAssignment]
    exact (hS.beta_sum_indep x y (yOfSum (n := n) hb (sumY y)) z (sumY_yOfSum (n := n) hb (sumY y)).symm).symm
  · funext xyz
    rcases xyz with ⟨x, y, z⟩
    let i0 : Fin b := ⟨0, hb⟩
    calc
      (toRawAssignmentABC
          (rawToABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc S hS)).gamma (x, y, z)
          = S.beta (x, yOfSum (n := n) hb (sumY y + 1), z) := by
              simp [toRawAssignmentABC, rawToABCAssignment]
      _ = S.beta (x, y + Pi.single i0 1, z) := by
            apply hS.beta_sum_indep
            simp [i0]
      _ = S.gamma (x, y, z) := by
            symm
            exact hS.gamma_beta_shift x y z (i := i0)
  · funext xyz
    rcases xyz with ⟨x, y, z⟩
    simp [toRawAssignmentABC, rawToABCAssignment]
    exact (hS.delta_sum_indep x y z (zOfSum (n := n) hc (sumZ z)) (sumZ_zOfSum (n := n) hc (sumZ z)).symm).symm
  · funext xyz
    rcases xyz with ⟨x, y, z⟩
    let i0 : Fin c := ⟨0, hc⟩
    calc
      (toRawAssignmentABC
          (rawToABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc S hS)).eta (x, y, z)
          = S.delta (x, y, zOfSum (n := n) hc (sumZ z + 1)) := by
              simp [toRawAssignmentABC, rawToABCAssignment]
      _ = S.delta (x, y, z + Pi.single i0 1) := by
            apply hS.delta_sum_indep
            simp [i0]
      _ = S.eta (x, y, z) := by
            symm
            exact hS.eta_delta_shift x y z (i := i0)

noncomputable def rawValidAssignmentsEquivABCAssignment {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    RawValidAssignmentsABC a b c n ≃ ABCAssignment a b c n where
  toFun S := rawToABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc S.1 S.2
  invFun nf := ⟨toRawAssignmentABC nf, rawValid_toRawAssignmentABC nf⟩
  left_inv S := by
    apply Subtype.ext
    exact toRawAssignmentABC_rawToABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc S.1 S.2
  right_inv nf := by
    exact rawToABCAssignment_toRawAssignmentABC (a := a) (b := b) (c := c) (n := n) hb hc nf

theorem card_rawValidAssignmentsABC {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (RawValidAssignmentsABC a b c n) =
      2 ^ (n ^ (b + c) + n ^ (a + c) + n ^ (a + b)) := by
  calc
    Fintype.card (RawValidAssignmentsABC a b c n)
        = Fintype.card (ABCAssignment a b c n) := by
            exact Fintype.card_congr
              (rawValidAssignmentsEquivABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc)
    _ = 2 ^ (n ^ (b + c) + n ^ (a + c) + n ^ (a + b)) := by
          exact card_validAssignments_abc (a := a) (b := b) (c := c) (n := n) ha

noncomputable def rawValidPrimitiveAssignmentsEquivRawValidAssignments {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    RawValidPrimitiveAssignmentsABC a b c n ≃ RawValidAssignmentsABC a b c n where
  toFun S := ⟨S.1, rawValidPrimitiveABC_to_rawValidABC (b := b) (c := c) (n := n) hb hc S.2⟩
  invFun S := ⟨S.1, rawValidABC_to_rawValidPrimitiveABC S.2⟩
  left_inv S := by
    apply Subtype.ext
    rfl
  right_inv S := by
    apply Subtype.ext
    rfl

noncomputable def rawValidPrimitiveAssignmentsEquivABCAssignment {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    RawValidPrimitiveAssignmentsABC a b c n ≃ ABCAssignment a b c n :=
  (rawValidPrimitiveAssignmentsEquivRawValidAssignments (a := a) (b := b) (c := c) (n := n) hb hc).trans
    (rawValidAssignmentsEquivABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc)

theorem card_rawValidPrimitiveAssignmentsABC {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (RawValidPrimitiveAssignmentsABC a b c n) =
      2 ^ (n ^ (b + c) + n ^ (a + c) + n ^ (a + b)) := by
  calc
    Fintype.card (RawValidPrimitiveAssignmentsABC a b c n)
        = Fintype.card (ABCAssignment a b c n) := by
            exact Fintype.card_congr
              (rawValidPrimitiveAssignmentsEquivABCAssignment
                (a := a) (b := b) (c := c) (n := n) hb hc)
    _ = 2 ^ (n ^ (b + c) + n ^ (a + c) + n ^ (a + b)) := by
          exact card_validAssignments_abc (a := a) (b := b) (c := c) (n := n) ha

def rawLocalPhaseBitABC {a b c n : ℕ} [NeZero n]
    (S : RawAssignmentABC a b c n) (xyz : RawSiteABC a b c n) : F₂ :=
  S.alpha xyz * (S.beta xyz + S.gamma xyz + S.delta xyz + S.eta xyz)

noncomputable def W_abc_raw {a b c n : ℕ} [NeZero n]
    (S : RawAssignmentABC a b c n) : ℤ :=
  ∏ xyz : RawSiteABC a b c n, bitSign (rawLocalPhaseBitABC S xyz)

lemma rawLocalPhaseBitABC_toRawAssignmentABC {a b c n : ℕ} [NeZero n]
    (nf : ABCAssignment a b c n) (xyz : RawSiteABC a b c n) :
    rawLocalPhaseBitABC (a := a) (b := b) (c := c) (n := n) (toRawAssignmentABC nf) xyz =
      nf.1 (xyz.2.1, xyz.2.2) *
        (nf.2.1 (xyz.1, sumY xyz.2.1, xyz.2.2) +
          nf.2.1 (xyz.1, sumY xyz.2.1 + 1, xyz.2.2) +
          nf.2.2 (xyz.1, xyz.2.1, sumZ xyz.2.2) +
          nf.2.2 (xyz.1, xyz.2.1, sumZ xyz.2.2 + 1)) := by
  simp [rawLocalPhaseBitABC, toRawAssignmentABC, mul_add, add_assoc, add_left_comm, add_comm]

noncomputable def rawBcSummandABC {a b c n : ℕ} [NeZero n]
    (nf : ABCAssignment a b c n) (x : XCoord a n) (yz : ASiteABC b c n) : F₂ :=
  nf.2.1 (x, sumY yz.1, yz.2)
    + nf.2.1 (x, sumY yz.1 + 1, yz.2)
    + nf.2.2 (x, yz.1, sumZ yz.2)
    + nf.2.2 (x, yz.1, sumZ yz.2 + 1)

lemma W_abc_raw_toRawAssignmentABC_eq_W_abc_real {a b c n : ℕ} [NeZero n]
    (nf : ABCAssignment a b c n) :
    W_abc_raw (a := a) (b := b) (c := c) (n := n) (toRawAssignmentABC nf) =
      W_abc_real (a := a) (b := b) (c := c) (n := n) nf := by
  classical
  unfold W_abc_raw W_abc_real alphaSignedABC alphaCoeffABC
  calc
    ∏ xyz : RawSiteABC a b c n,
        bitSign (rawLocalPhaseBitABC (a := a) (b := b) (c := c) (n := n) (toRawAssignmentABC nf) xyz)
        = ∏ yz : ASiteABC b c n, ∏ x : XCoord a n,
            bitSign (nf.1 yz * rawBcSummandABC (a := a) (b := b) (c := c) (n := n) nf x yz) := by
              rw [Fintype.prod_prod_type_right]
              simp_rw [rawLocalPhaseBitABC_toRawAssignmentABC, rawBcSummandABC]
    _ = ∏ yz : ASiteABC b c n,
          bitSign
            (∑ x : XCoord a n, nf.1 yz * rawBcSummandABC (a := a) (b := b) (c := c) (n := n) nf x yz) := by
          congr with yz
          simpa using
            prod_bitSign_eq_bitSign_sum (Finset.univ : Finset (XCoord a n))
              (fun x : XCoord a n => nf.1 yz * rawBcSummandABC (a := a) (b := b) (c := c) (n := n) nf x yz)
    _ = ∏ yz : ASiteABC b c n, bitSign (nf.1 yz * coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2 yz) := by
          congr with yz
          simp [coeffFromBC_abc_real, rawBcSummandABC, Finset.mul_sum]
    _ = bitSign
          (∑ yz : ASiteABC b c n, nf.1 yz * coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2 yz) := by
          simpa using
            prod_bitSign_eq_bitSign_sum (Finset.univ : Finset (ASiteABC b c n))
              (fun yz : ASiteABC b c n =>
                nf.1 yz * coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2 yz)

noncomputable def deltaABCraw_raw {a b c n : ℕ} [NeZero n] : ℤ :=
  ∑ S : RawValidAssignmentsABC a b c n, W_abc_raw (a := a) (b := b) (c := c) (n := n) S.1

lemma deltaABCraw_raw_eq_deltaABCraw_real {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_raw (a := a) (b := b) (c := c) (n := n) =
      deltaABCraw_real (a := a) (b := b) (c := c) (n := n) := by
  classical
  unfold deltaABCraw_raw deltaABCraw_real
  calc
    ∑ S : RawValidAssignmentsABC a b c n,
        W_abc_raw (a := a) (b := b) (c := c) (n := n) S.1
        = ∑ nf : ABCAssignment a b c n,
            W_abc_raw (a := a) (b := b) (c := c) (n := n) (toRawAssignmentABC nf) := by
              simpa using
                (((rawValidAssignmentsEquivABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc).symm.sum_comp
                  (fun S : RawValidAssignmentsABC a b c n =>
                    W_abc_raw (a := a) (b := b) (c := c) (n := n) S.1)).symm)
    _ = ∑ nf : ABCAssignment a b c n, W_abc_real (a := a) (b := b) (c := c) (n := n) nf := by
          congr with nf
          exact W_abc_raw_toRawAssignmentABC_eq_W_abc_real (a := a) (b := b) (c := c) (n := n) nf

noncomputable abbrev deltaABCraw_primitive {a b c n : ℕ} [NeZero n] : ℤ :=
  ∑ S : RawValidPrimitiveAssignmentsABC a b c n, W_abc_raw (a := a) (b := b) (c := c) (n := n) S.1

lemma deltaABCraw_primitive_eq_deltaABCraw_raw {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_primitive (a := a) (b := b) (c := c) (n := n) =
      deltaABCraw_raw (a := a) (b := b) (c := c) (n := n) := by
  classical
  unfold deltaABCraw_primitive deltaABCraw_raw
  calc
    ∑ S : RawValidPrimitiveAssignmentsABC a b c n,
        W_abc_raw (a := a) (b := b) (c := c) (n := n) S.1
        =
          ∑ S : RawValidAssignmentsABC a b c n,
            W_abc_raw (a := a) (b := b) (c := c) (n := n)
              ((rawValidPrimitiveAssignmentsEquivRawValidAssignments
                (a := a) (b := b) (c := c) (n := n) hb hc).symm S).1 := by
              simpa using
                (((rawValidPrimitiveAssignmentsEquivRawValidAssignments
                  (a := a) (b := b) (c := c) (n := n) hb hc).symm.sum_comp
                    (fun S : RawValidPrimitiveAssignmentsABC a b c n =>
                      W_abc_raw (a := a) (b := b) (c := c) (n := n) S.1)).symm)
    _ = ∑ S : RawValidAssignmentsABC a b c n,
          W_abc_raw (a := a) (b := b) (c := c) (n := n) S.1 := by
            rfl

lemma deltaABCraw_primitive_eq_deltaABCraw_real {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_primitive (a := a) (b := b) (c := c) (n := n) =
      deltaABCraw_real (a := a) (b := b) (c := c) (n := n) := by
  rw [deltaABCraw_primitive_eq_deltaABCraw_raw (a := a) (b := b) (c := c) (n := n) hb hc]
  exact deltaABCraw_raw_eq_deltaABCraw_real (a := a) (b := b) (c := c) (n := n) hb hc

abbrev ProfileCompatABC (b c n : ℕ) [NeZero n] :=
  { fg : BProfileRawABC c n × CProfileRawABC b n //
      fg.1 ∈ BProfileAdmSubmoduleABC c n ∧
      fg.2 ∈ CProfileAdmSubmoduleABC b n ∧
      ∀ y : YCoord b n, ∀ z : ZCoord c n, fg.1 (sumY y) z = fg.2 y (sumZ z) }

noncomputable instance instFintypeProfileCompatABC (b c n : ℕ) [NeZero n] :
    Fintype (ProfileCompatABC b c n) := Fintype.ofFinite _

noncomputable def profileCompatABCToH {b c n : ℕ} [NeZero n]
    (hc : 0 < c) (fg : ProfileCompatABC b c n) : HRaw n :=
  fun p => fg.1.1 (p 0) (zOfSum (n := n) hc (p 1))

lemma profileCompatABC_b_eq_toH_sum {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (fg : ProfileCompatABC b c n)
    (s : ZMod n) (z : ZCoord c n) :
    fg.1.1 s z = profileCompatABCToH (n := n) hc fg (vec2 s (sumZ z)) := by
  have h1 := fg.2.2.2 (yOfSum (n := n) hb s) z
  have h2 := fg.2.2.2 (yOfSum (n := n) hb s) (zOfSum (n := n) hc (sumZ z))
  calc
    fg.1.1 s z = fg.1.2 (yOfSum (n := n) hb s) (sumZ z) := by
      simpa using h1
    _ = fg.1.1 s (zOfSum (n := n) hc (sumZ z)) := by
      symm
      simpa using h2
    _ = profileCompatABCToH (n := n) hc fg (vec2 s (sumZ z)) := by
      simp [profileCompatABCToH]

lemma profileCompatABC_c_eq_toH_sum {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (fg : ProfileCompatABC b c n)
    (y : YCoord b n) (r : ZMod n) :
    fg.1.2 y r = profileCompatABCToH (n := n) hc fg (vec2 (sumY y) r) := by
  have h1 := fg.2.2.2 y (zOfSum (n := n) hc r)
  calc
    fg.1.2 y r = fg.1.1 (sumY y) (zOfSum (n := n) hc r) := by
      symm
      simpa using h1
    _ = profileCompatABCToH (n := n) hc fg (vec2 (sumY y) r) := by
      simp [profileCompatABCToH]

lemma profileCompatABCToH_admissible {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (fg : ProfileCompatABC b c n) :
    (∀ t : ZMod n, rowSum (profileCompatABCToH (n := n) hc fg) t = 0) ∧
      (∀ s : ZMod n, colSum (profileCompatABCToH (n := n) hc fg) s = 0) := by
  constructor
  · intro t
    have hf :=
      (mem_BProfileAdmSubmoduleABC_iff (c := c) (n := n) fg.1.1).1 fg.2.1
        (zOfSum (n := n) hc t)
    simpa [rowSum, profileCompatABCToH, vec2] using hf
  · intro s
    have hg :=
      (mem_CProfileAdmSubmoduleABC_iff (b := b) (n := n) fg.1.2).1 fg.2.2.1
        (yOfSum (n := n) hb s)
    have hconvert :
        (∑ r : ZMod n, fg.1.2 (yOfSum (n := n) hb s) r) =
          colSum (profileCompatABCToH (n := n) hc fg) s := by
      calc
        (∑ r : ZMod n, fg.1.2 (yOfSum (n := n) hb s) r)
            = ∑ r : ZMod n, profileCompatABCToH (n := n) hc fg (vec2 s r) := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                simpa using
                  (profileCompatABC_c_eq_toH_sum (b := b) (c := c) (n := n) hb hc fg
                    (yOfSum (n := n) hb s) r)
        _ = colSum (profileCompatABCToH (n := n) hc fg) s := by
              simp [colSum]
    rw [← hconvert]
    exact hg

noncomputable def hToProfileCompatABC {b c n : ℕ} [NeZero n]
    (_hb : 0 < b) (_hc : 0 < c) (h : HAdmissible n) : ProfileCompatABC b c n := by
  refine ⟨(fun s z => (h : HRaw n) (vec2 s (sumZ z)),
    fun y r => (h : HRaw n) (vec2 (sumY y) r)), ?_, ?_, ?_⟩
  · rw [mem_BProfileAdmSubmoduleABC_iff]
    intro z
    have hs := h.2.1 (sumZ z)
    simpa [rowSum, vec2] using hs
  · rw [mem_CProfileAdmSubmoduleABC_iff]
    intro y
    have hs := h.2.2 (sumY y)
    simpa [colSum, vec2] using hs
  · intro y z
    rfl

noncomputable def profileCompatABC_equiv_HAdmissible {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    ProfileCompatABC b c n ≃ HAdmissible n where
  toFun fg := ⟨profileCompatABCToH (n := n) hc fg,
    profileCompatABCToH_admissible (b := b) (c := c) (n := n) hb hc fg⟩
  invFun h := hToProfileCompatABC (b := b) (c := c) (n := n) hb hc h
  left_inv fg := by
    apply Subtype.ext
    apply Prod.ext
    · funext s z
      simpa [hToProfileCompatABC] using
        (profileCompatABC_b_eq_toH_sum (b := b) (c := c) (n := n) hb hc fg s z).symm
    · funext y r
      simpa [hToProfileCompatABC] using
        (profileCompatABC_c_eq_toH_sum (b := b) (c := c) (n := n) hb hc fg y r).symm
  right_inv h := by
    apply Subtype.ext
    funext p
    simpa [profileCompatABCToH, hToProfileCompatABC, vec2]

theorem card_ProfileCompatABC_closed {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ProfileCompatABC b c n) = 2 ^ ((n - 1) ^ 2) := by
  rw [Fintype.card_congr (profileCompatABC_equiv_HAdmissible (b := b) (c := c) (n := n) hb hc)]
  exact card_HAdmissible_closed_abc (n := n)

noncomputable def xZeroABC {a n : ℕ} [NeZero n] : XCoord a n := fun _ => 0

noncomputable def BfieldABC_of_admissibleProfile {a c n : ℕ} [NeZero n]
    (f : BProfileRawABC c n) (_hf : f ∈ BProfileAdmSubmoduleABC c n) : BFieldABC a c n :=
  fun u =>
    if _ : u.1 ≠ xZeroABC (a := a) (n := n) then 0
    else
      ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm u.2.1), f ((ZMod.finEquiv n) i) u.2.2

lemma bKernelABC_real_BfieldABC_of_admissibleProfile {a c n : ℕ} [NeZero n]
    (f : BProfileRawABC c n) (hf : f ∈ BProfileAdmSubmoduleABC c n)
    (s : ZMod n) (z : ZCoord c n) :
    bKernelABC_real (a := a) (c := c) (n := n)
      (BfieldABC_of_admissibleProfile (a := a) (c := c) (n := n) f hf) s z = f s z := by
  classical
  unfold bKernelABC_real
  rw [Fintype.sum_eq_single (xZeroABC (a := a) (n := n))]
  ·
    have hB0 :
        BfieldABC_of_admissibleProfile (a := a) (c := c) (n := n) f hf
            (xZeroABC (a := a) (n := n), s, z)
          = ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm s), f ((ZMod.finEquiv n) i) z := by
      unfold BfieldABC_of_admissibleProfile
      simp [xZeroABC]
    have hB1 :
        BfieldABC_of_admissibleProfile (a := a) (c := c) (n := n) f hf
            (xZeroABC (a := a) (n := n), s + 1, z)
          = ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm (s + 1)), f ((ZMod.finEquiv n) i) z := by
      unfold BfieldABC_of_admissibleProfile
      simp [xZeroABC]
    rw [hB0, hB1]
    have hfslice : ∑ s' : ZMod n, f s' z = 0 :=
      (mem_BProfileAdmSubmoduleABC_iff (c := c) (n := n) f).1 hf z
    have hfFin : ∑ i : Fin n, f ((ZMod.finEquiv n) i) z = 0 := by
      simpa [← Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun s' => f s' z)] using hfslice
    have hsymm : (ZMod.finEquiv n).symm (s + 1) = (ZMod.finEquiv n).symm s + 1 := by
      rcases n with - | n
      · cases NeZero.ne 0 rfl
      simp [ZMod.finEquiv, RingEquiv.map_add, RingEquiv.map_one]
    rw [hsymm]
    simpa [Equiv.apply_symm_apply (ZMod.finEquiv n).toEquiv] using
      Fin_sum_Iio_add_sum_Iio_succ (n := n) (fun i : Fin n => f ((ZMod.finEquiv n) i) z)
        ((ZMod.finEquiv n).symm s) hfFin
  · intro p hp
    unfold BfieldABC_of_admissibleProfile
    simp [hp]

lemma BProfileAdmSubmoduleABC_le_range_bProfileLinearMap_abc_real {a c n : ℕ} [NeZero n] :
    BProfileAdmSubmoduleABC c n ≤ LinearMap.range (bProfileLinearMap_abc_real (a := a) (c := c) (n := n)) := by
  rintro f hf
  refine ⟨BfieldABC_of_admissibleProfile (a := a) (c := c) (n := n) f hf, ?_⟩
  ext s z
  simpa [bProfileLinearMap_abc_real] using
    bKernelABC_real_BfieldABC_of_admissibleProfile (a := a) (c := c) (n := n) f hf s z

lemma range_bProfileLinearMap_abc_real_eq_BProfileAdmSubmoduleABC {a c n : ℕ} [NeZero n] :
    LinearMap.range (bProfileLinearMap_abc_real (a := a) (c := c) (n := n)) =
      BProfileAdmSubmoduleABC c n :=
  le_antisymm
    (LinearMap.range_le_ker_iff.2
      (bProfileSumConstraint_comp_bProfileLinearMap_abc_real_eq_zero (a := a) (c := c) (n := n)))
    (BProfileAdmSubmoduleABC_le_range_bProfileLinearMap_abc_real (a := a) (c := c) (n := n))

noncomputable def CfieldABC_of_admissibleProfile {a b n : ℕ} [NeZero n]
    (f : CProfileRawABC b n) (_hf : f ∈ CProfileAdmSubmoduleABC b n) : CFieldABC a b n :=
  fun u =>
    if _ : u.1 ≠ xZeroABC (a := a) (n := n) then 0
    else
      ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm u.2.2), f u.2.1 ((ZMod.finEquiv n) i)

lemma cKernelABC_real_CfieldABC_of_admissibleProfile {a b n : ℕ} [NeZero n]
    (f : CProfileRawABC b n) (hf : f ∈ CProfileAdmSubmoduleABC b n)
    (y : YCoord b n) (r : ZMod n) :
    cKernelABC_real (a := a) (b := b) (n := n)
      (CfieldABC_of_admissibleProfile (a := a) (b := b) (n := n) f hf) y r = f y r := by
  classical
  unfold cKernelABC_real
  rw [Fintype.sum_eq_single (xZeroABC (a := a) (n := n))]
  ·
    have hC0 :
        CfieldABC_of_admissibleProfile (a := a) (b := b) (n := n) f hf
            (xZeroABC (a := a) (n := n), y, r)
          = ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm r), f y ((ZMod.finEquiv n) i) := by
      unfold CfieldABC_of_admissibleProfile
      simp [xZeroABC]
    have hC1 :
        CfieldABC_of_admissibleProfile (a := a) (b := b) (n := n) f hf
            (xZeroABC (a := a) (n := n), y, r + 1)
          = ∑ i ∈ Finset.Iio ((ZMod.finEquiv n).symm (r + 1)), f y ((ZMod.finEquiv n) i) := by
      unfold CfieldABC_of_admissibleProfile
      simp [xZeroABC]
    rw [hC0, hC1]
    have hfslice : ∑ r' : ZMod n, f y r' = 0 :=
      (mem_CProfileAdmSubmoduleABC_iff (b := b) (n := n) f).1 hf y
    have hfFin : ∑ i : Fin n, f y ((ZMod.finEquiv n) i) = 0 := by
      simpa [← Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun r' => f y r')] using hfslice
    have hsymm : (ZMod.finEquiv n).symm (r + 1) = (ZMod.finEquiv n).symm r + 1 := by
      rcases n with - | n
      · cases NeZero.ne 0 rfl
      simp [ZMod.finEquiv, RingEquiv.map_add, RingEquiv.map_one]
    rw [hsymm]
    simpa [Equiv.apply_symm_apply (ZMod.finEquiv n).toEquiv] using
      Fin_sum_Iio_add_sum_Iio_succ (n := n) (fun i : Fin n => f y ((ZMod.finEquiv n) i))
        ((ZMod.finEquiv n).symm r) hfFin
  · intro p hp
    unfold CfieldABC_of_admissibleProfile
    simp [hp]

lemma CProfileAdmSubmoduleABC_le_range_cProfileLinearMap_abc_real {a b n : ℕ} [NeZero n] :
    CProfileAdmSubmoduleABC b n ≤ LinearMap.range (cProfileLinearMap_abc_real (a := a) (b := b) (n := n)) := by
  rintro f hf
  refine ⟨CfieldABC_of_admissibleProfile (a := a) (b := b) (n := n) f hf, ?_⟩
  ext y r
  simpa [cProfileLinearMap_abc_real] using
    cKernelABC_real_CfieldABC_of_admissibleProfile (a := a) (b := b) (n := n) f hf y r

lemma range_cProfileLinearMap_abc_real_eq_CProfileAdmSubmoduleABC {a b n : ℕ} [NeZero n] :
    LinearMap.range (cProfileLinearMap_abc_real (a := a) (b := b) (n := n)) =
      CProfileAdmSubmoduleABC b n :=
  le_antisymm
    (LinearMap.range_le_ker_iff.2
      (cProfileSumConstraint_comp_cProfileLinearMap_abc_real_eq_zero (a := a) (b := b) (n := n)))
    (CProfileAdmSubmoduleABC_le_range_cProfileLinearMap_abc_real (a := a) (b := b) (n := n))

lemma finrank_range_bProfileLinearMap_abc_real {a c n : ℕ} [NeZero n] :
    Module.finrank F₂ (LinearMap.range (bProfileLinearMap_abc_real (a := a) (c := c) (n := n))) =
      n ^ (c + 1) - n ^ c := by
  rw [range_bProfileLinearMap_abc_real_eq_BProfileAdmSubmoduleABC]
  exact finrank_BProfileAdmSubmoduleABC (c := c) (n := n)

lemma finrank_range_cProfileLinearMap_abc_real {a b n : ℕ} [NeZero n] :
    Module.finrank F₂ (LinearMap.range (cProfileLinearMap_abc_real (a := a) (b := b) (n := n))) =
      n ^ (b + 1) - n ^ b := by
  rw [range_cProfileLinearMap_abc_real_eq_CProfileAdmSubmoduleABC]
  exact finrank_CProfileAdmSubmoduleABC (b := b) (n := n)

lemma finrank_ker_bProfileLinearMap_abc_real {a c n : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F₂ (LinearMap.ker (bProfileLinearMap_abc_real (a := a) (c := c) (n := n))) =
      n ^ (a + c) - (n ^ (c + 1) - n ^ c) := by
  classical
  let L := bProfileLinearMap_abc_real (a := a) (c := c) (n := n)
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hdom : Module.finrank F₂ (BFieldABC a c n) = n ^ (a + c) :=
    finrank_BFieldABC (a := a) (c := c) (n := n) ha
  have hrng :
      Module.finrank F₂ (LinearMap.range L) = n ^ (c + 1) - n ^ c :=
    finrank_range_bProfileLinearMap_abc_real (a := a) (c := c) (n := n)
  rw [hdom, hrng] at hsum
  have hle : n ^ (c + 1) - n ^ c ≤ n ^ (a + c) := by
    calc
      n ^ (c + 1) - n ^ c ≤ n ^ (c + 1) := Nat.sub_le _ _
      _ ≤ n ^ (a + c) := by
        have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
        have hac : c + 1 ≤ a + c := by omega
        exact Nat.pow_le_pow_right hn hac
  have hker :
      Module.finrank F₂ (LinearMap.ker L) = n ^ (a + c) - (n ^ (c + 1) - n ^ c) := by
    omega
  exact hker

lemma finrank_ker_cProfileLinearMap_abc_real {a b n : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F₂ (LinearMap.ker (cProfileLinearMap_abc_real (a := a) (b := b) (n := n))) =
      n ^ (a + b) - (n ^ (b + 1) - n ^ b) := by
  classical
  let L := cProfileLinearMap_abc_real (a := a) (b := b) (n := n)
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hdom : Module.finrank F₂ (CFieldABC a b n) = n ^ (a + b) :=
    finrank_CFieldABC (a := a) (b := b) (n := n) ha
  have hrng :
      Module.finrank F₂ (LinearMap.range L) = n ^ (b + 1) - n ^ b :=
    finrank_range_cProfileLinearMap_abc_real (a := a) (b := b) (n := n)
  rw [hdom, hrng] at hsum
  have hle : n ^ (b + 1) - n ^ b ≤ n ^ (a + b) := by
    calc
      n ^ (b + 1) - n ^ b ≤ n ^ (b + 1) := Nat.sub_le _ _
      _ ≤ n ^ (a + b) := by
        have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
        have hab : b + 1 ≤ a + b := by omega
        exact Nat.pow_le_pow_right hn hab
  have hker :
      Module.finrank F₂ (LinearMap.ker L) = n ^ (a + b) - (n ^ (b + 1) - n ^ b) := by
    omega
  exact hker

abbrev BProfileFiberABC_real {a c n : ℕ} [NeZero n] (f : BProfileRawABC c n) :=
  { B : BFieldABC a c n // bProfileLinearMap_abc_real (a := a) (c := c) (n := n) B = f }

abbrev CProfileFiberABC_real {a b n : ℕ} [NeZero n] (f : CProfileRawABC b n) :=
  { C : CFieldABC a b n // cProfileLinearMap_abc_real (a := a) (b := b) (n := n) C = f }

lemma exists_B_of_admissibleBProfileABC {a c n : ℕ} [NeZero n] (f : BProfileRawABC c n)
    (hf : f ∈ BProfileAdmSubmoduleABC c n) :
    ∃ B : BFieldABC a c n, bProfileLinearMap_abc_real (a := a) (c := c) (n := n) B = f := by
  exact (BProfileAdmSubmoduleABC_le_range_bProfileLinearMap_abc_real (a := a) (c := c) (n := n)) hf

lemma exists_C_of_admissibleCProfileABC {a b n : ℕ} [NeZero n] (f : CProfileRawABC b n)
    (hf : f ∈ CProfileAdmSubmoduleABC b n) :
    ∃ C : CFieldABC a b n, cProfileLinearMap_abc_real (a := a) (b := b) (n := n) C = f := by
  exact (CProfileAdmSubmoduleABC_le_range_cProfileLinearMap_abc_real (a := a) (b := b) (n := n)) hf

noncomputable def fiberEquivKer_bProfileABC_real {a c n : ℕ} [NeZero n] (B₀ : BFieldABC a c n) :
    { B : BFieldABC a c n // bProfileLinearMap_abc_real (a := a) (c := c) (n := n) B =
        bProfileLinearMap_abc_real (a := a) (c := c) (n := n) B₀ }
      ≃ ↥(LinearMap.ker (bProfileLinearMap_abc_real (a := a) (c := c) (n := n))) where
  toFun := fun ⟨B, hB⟩ =>
    ⟨B + B₀, LinearMap.mem_ker.mpr (by
      rw [LinearMap.map_add, hB]
      ext s z
      simp [Pi.add_apply, F2_add_self])⟩
  invFun := fun ⟨K, hK⟩ =>
    ⟨K + B₀, by
      rw [LinearMap.map_add, LinearMap.mem_ker.mp hK, zero_add]⟩
  left_inv := fun ⟨B, hB⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (B₀ u)]
    simp
  right_inv := fun ⟨K, hK⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (B₀ u)]
    simp

noncomputable def fiberEquivKer_cProfileABC_real {a b n : ℕ} [NeZero n] (C₀ : CFieldABC a b n) :
    { C : CFieldABC a b n // cProfileLinearMap_abc_real (a := a) (b := b) (n := n) C =
        cProfileLinearMap_abc_real (a := a) (b := b) (n := n) C₀ }
      ≃ ↥(LinearMap.ker (cProfileLinearMap_abc_real (a := a) (b := b) (n := n))) where
  toFun := fun ⟨C, hC⟩ =>
    ⟨C + C₀, LinearMap.mem_ker.mpr (by
      rw [LinearMap.map_add, hC]
      ext y r
      simp [Pi.add_apply, F2_add_self])⟩
  invFun := fun ⟨K, hK⟩ =>
    ⟨K + C₀, by
      rw [LinearMap.map_add, LinearMap.mem_ker.mp hK, zero_add]⟩
  left_inv := fun ⟨C, hC⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (C₀ u)]
    simp
  right_inv := fun ⟨K, hK⟩ => by
    refine Subtype.ext ?_
    ext u
    simp only [Pi.add_apply, add_assoc]
    rw [F2_add_self (C₀ u)]
    simp

lemma Nat.card_BProfileFiberABC_real_eq_two_pow_ker {a c n : ℕ} [NeZero n]
    (ha : 0 < a) (f : BProfileRawABC c n) (hf : f ∈ BProfileAdmSubmoduleABC c n) :
    Nat.card (BProfileFiberABC_real (a := a) (c := c) (n := n) f) =
      (2 : ℕ) ^ (n ^ (a + c) - (n ^ (c + 1) - n ^ c)) := by
  rcases exists_B_of_admissibleBProfileABC (a := a) (c := c) (n := n) f hf with ⟨B₀, hB₀⟩
  calc
    Nat.card (BProfileFiberABC_real (a := a) (c := c) (n := n) f)
        =
          Nat.card { B : BFieldABC a c n //
            bProfileLinearMap_abc_real (a := a) (c := c) (n := n) B =
              bProfileLinearMap_abc_real (a := a) (c := c) (n := n) B₀ } := by
          refine Nat.card_congr ?_
          refine
            { toFun := fun x => ⟨x.1, by simpa [hB₀] using x.2⟩
              invFun := fun x => ⟨x.1, by simpa [hB₀] using x.2⟩
              left_inv := by intro x; rfl
              right_inv := by intro x; rfl }
    _ = Nat.card (↥(LinearMap.ker (bProfileLinearMap_abc_real (a := a) (c := c) (n := n)))) := by
          exact Nat.card_congr (fiberEquivKer_bProfileABC_real (a := a) (c := c) (n := n) B₀)
    _ =
          (2 : ℕ) ^ (n ^ (a + c) - (n ^ (c + 1) - n ^ c)) := by
          rw [Module.natCard_eq_pow_finrank (K := F₂)
            (V := ↥(LinearMap.ker (bProfileLinearMap_abc_real (a := a) (c := c) (n := n))))]
          rw [Nat.card_eq_fintype_card, finrank_ker_bProfileLinearMap_abc_real (a := a) (c := c) (n := n) ha]
          simp [F₂]

lemma Nat.card_CProfileFiberABC_real_eq_two_pow_ker {a b n : ℕ} [NeZero n]
    (ha : 0 < a) (f : CProfileRawABC b n) (hf : f ∈ CProfileAdmSubmoduleABC b n) :
    Nat.card (CProfileFiberABC_real (a := a) (b := b) (n := n) f) =
      (2 : ℕ) ^ (n ^ (a + b) - (n ^ (b + 1) - n ^ b)) := by
  rcases exists_C_of_admissibleCProfileABC (a := a) (b := b) (n := n) f hf with ⟨C₀, hC₀⟩
  calc
    Nat.card (CProfileFiberABC_real (a := a) (b := b) (n := n) f)
        =
          Nat.card { C : CFieldABC a b n //
            cProfileLinearMap_abc_real (a := a) (b := b) (n := n) C =
              cProfileLinearMap_abc_real (a := a) (b := b) (n := n) C₀ } := by
          refine Nat.card_congr ?_
          refine
            { toFun := fun x => ⟨x.1, by simpa [hC₀] using x.2⟩
              invFun := fun x => ⟨x.1, by simpa [hC₀] using x.2⟩
              left_inv := by intro x; rfl
              right_inv := by intro x; rfl }
    _ = Nat.card (↥(LinearMap.ker (cProfileLinearMap_abc_real (a := a) (b := b) (n := n)))) := by
          exact Nat.card_congr (fiberEquivKer_cProfileABC_real (a := a) (b := b) (n := n) C₀)
    _ =
          (2 : ℕ) ^ (n ^ (a + b) - (n ^ (b + 1) - n ^ b)) := by
          rw [Module.natCard_eq_pow_finrank (K := F₂)
            (V := ↥(LinearMap.ker (cProfileLinearMap_abc_real (a := a) (b := b) (n := n))))]
          rw [Nat.card_eq_fintype_card, finrank_ker_cProfileLinearMap_abc_real (a := a) (b := b) (n := n) ha]
          simp [F₂]

abbrev SurvivingSigmaABC_real (a b c n : ℕ) [NeZero n] :=
  Σ fg : ProfileCompatABC b c n,
    BProfileFiberABC_real (a := a) (c := c) (n := n) fg.1.1 ×
      CProfileFiberABC_real (a := a) (b := b) (n := n) fg.1.2

noncomputable def survivingBC_abc_real_equiv_sigma {a b c n : ℕ} [NeZero n] :
    SurvivingBC_abc_real a b c n ≃ SurvivingSigmaABC_real a b c n where
  toFun := by
    intro p
    rcases p with ⟨⟨B, C⟩, hp⟩
    have hbadm :
        bProfileLinearMap_abc_real (a := a) (c := c) (n := n) B ∈ BProfileAdmSubmoduleABC c n := by
      rw [← range_bProfileLinearMap_abc_real_eq_BProfileAdmSubmoduleABC (a := a) (c := c) (n := n)]
      exact LinearMap.mem_range.2 ⟨B, rfl⟩
    have hcadm :
        cProfileLinearMap_abc_real (a := a) (b := b) (n := n) C ∈ CProfileAdmSubmoduleABC b n := by
      rw [← range_cProfileLinearMap_abc_real_eq_CProfileAdmSubmoduleABC (a := a) (b := b) (n := n)]
      exact LinearMap.mem_range.2 ⟨C, rfl⟩
    refine ⟨⟨(bProfileLinearMap_abc_real (a := a) (c := c) (n := n) B,
        cProfileLinearMap_abc_real (a := a) (b := b) (n := n) C), hbadm, hcadm, ?_⟩,
      ⟨⟨B, rfl⟩, ⟨C, rfl⟩⟩⟩
    have hzero := (coeffFromBC_abc_real_eq_zero_iff (a := a) (b := b) (c := c) (n := n) B C).1 hp
    intro y z
    simpa [bProfileLinearMap_abc_real, cProfileLinearMap_abc_real] using hzero (y, z)
  invFun := by
    intro x
    rcases x with ⟨⟨⟨f, g⟩, hfadm, hcadm, hq⟩, ⟨B, hB⟩, ⟨C, hC⟩⟩
    refine ⟨⟨B, C⟩, ?_⟩
    refine (coeffFromBC_abc_real_eq_zero_iff (a := a) (b := b) (c := c) (n := n) B C).2 ?_
    intro yz
    calc
      bKernelABC_real (a := a) (c := c) (n := n) B (sumY yz.1) yz.2
          = f (sumY yz.1) yz.2 := by simpa [bProfileLinearMap_abc_real] using congrFun (congrFun hB (sumY yz.1)) yz.2
      _ = g yz.1 (sumZ yz.2) := hq yz.1 yz.2
      _ = cKernelABC_real (a := a) (b := b) (n := n) C yz.1 (sumZ yz.2) := by
            simpa [cProfileLinearMap_abc_real] using (congrFun (congrFun hC yz.1) (sumZ yz.2)).symm
  left_inv := by
    intro p
    rcases p with ⟨⟨B, C⟩, hp⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨⟨f, g⟩, hfadm, hcadm, hq⟩, ⟨B, hB⟩, ⟨C, hC⟩⟩
    cases hB
    cases hC
    rfl

lemma Nat.card_survivingBC_abc_real_eq_card_sigma {a b c n : ℕ} [NeZero n] :
    Nat.card (SurvivingBC_abc_real a b c n) = Nat.card (SurvivingSigmaABC_real a b c n) :=
  Nat.card_congr (survivingBC_abc_real_equiv_sigma (a := a) (b := b) (c := c) (n := n))

lemma Nat.card_survivingSigmaABC_real_eq_sum_profileFiberProducts {a b c n : ℕ} [NeZero n] :
    Nat.card (SurvivingSigmaABC_real a b c n)
      = ∑ fg : ProfileCompatABC b c n,
          Nat.card (BProfileFiberABC_real (a := a) (c := c) (n := n) fg.1.1) *
            Nat.card (CProfileFiberABC_real (a := a) (b := b) (n := n) fg.1.2) := by
  simpa [SurvivingSigmaABC_real, Nat.card_prod] using
    (Nat.card_sigma
      (β := fun fg : ProfileCompatABC b c n =>
        BProfileFiberABC_real (a := a) (c := c) (n := n) fg.1.1 ×
          CProfileFiberABC_real (a := a) (b := b) (n := n) fg.1.2))

lemma Nat.card_profileFiberABC_real_product_constant {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (fg : ProfileCompatABC b c n) :
    Nat.card (BProfileFiberABC_real (a := a) (c := c) (n := n) fg.1.1) *
        Nat.card (CProfileFiberABC_real (a := a) (b := b) (n := n) fg.1.2)
      =
        (2 : ℕ) ^
          ((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
            (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) := by
  have hB :
      Nat.card (BProfileFiberABC_real (a := a) (c := c) (n := n) fg.1.1) =
        (2 : ℕ) ^ (n ^ (a + c) - (n ^ (c + 1) - n ^ c)) :=
    Nat.card_BProfileFiberABC_real_eq_two_pow_ker (a := a) (c := c) (n := n) ha fg.1.1 fg.2.1
  have hC :
      Nat.card (CProfileFiberABC_real (a := a) (b := b) (n := n) fg.1.2) =
        (2 : ℕ) ^ (n ^ (a + b) - (n ^ (b + 1) - n ^ b)) :=
    Nat.card_CProfileFiberABC_real_eq_two_pow_ker (a := a) (b := b) (n := n) ha fg.1.2 fg.2.2.1
  rw [hB, hC, ← Nat.pow_add]

lemma Nat.card_survivingSigmaABC_real_eq_card_profileCompat_mul_pow {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) :
    Nat.card (SurvivingSigmaABC_real a b c n)
      =
        Nat.card (ProfileCompatABC b c n) *
          (2 : ℕ) ^
            ((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
              (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) := by
  let k : ℕ :=
    (2 : ℕ) ^
      ((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
        (n ^ (a + b) - (n ^ (b + 1) - n ^ b)))
  rw [Nat.card_survivingSigmaABC_real_eq_sum_profileFiberProducts (a := a) (b := b) (c := c) (n := n)]
  simp_rw [Nat.card_profileFiberABC_real_product_constant (a := a) (b := b) (c := c) (n := n) ha]
  have hsum :
      (∑ _fg : ProfileCompatABC b c n, k) = Fintype.card (ProfileCompatABC b c n) * k := by
    simp [Finset.sum_const_nat]
  rw [hsum]
  rw [Nat.card_eq_fintype_card (α := ProfileCompatABC b c n)]

theorem Nat.card_survivingBC_abc_real_closed_via_sigma {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Nat.card (SurvivingBC_abc_real a b c n)
      =
        (2 : ℕ) ^
          (((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
              (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) +
            (n - 1) ^ 2) := by
  calc
    Nat.card (SurvivingBC_abc_real a b c n)
        = Nat.card (SurvivingSigmaABC_real a b c n) := by
            exact Nat.card_survivingBC_abc_real_eq_card_sigma (a := a) (b := b) (c := c) (n := n)
    _ =
          Nat.card (ProfileCompatABC b c n) *
            (2 : ℕ) ^
              ((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
                (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) := by
            exact Nat.card_survivingSigmaABC_real_eq_card_profileCompat_mul_pow
              (a := a) (b := b) (c := c) (n := n) ha
    _ =
          (2 : ℕ) ^ ((n - 1) ^ 2) *
            (2 : ℕ) ^
              ((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
                (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) := by
            rw [Nat.card_eq_fintype_card, card_ProfileCompatABC_closed (b := b) (c := c) (n := n) hb hc]
    _ =
          (2 : ℕ) ^
            (((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
                (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) +
              (n - 1) ^ 2) := by
            rw [Nat.mul_comm, ← Nat.pow_add]

theorem card_survivingBC_abc_real_closed {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (SurvivingBC_abc_real a b c n) = 2 ^ survivingExponentABC a b c n := by
  have hnat :
      Nat.card (SurvivingBC_abc_real a b c n) =
        (2 : ℕ) ^
          (((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
              (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) +
            (n - 1) ^ 2) :=
    Nat.card_survivingBC_abc_real_closed_via_sigma (a := a) (b := b) (c := c) (n := n) ha hb hc
  have hcard :
      Fintype.card (SurvivingBC_abc_real a b c n) =
        (2 : ℕ) ^
          (((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
              (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) +
            (n - 1) ^ 2) := by
    simpa [Nat.card_eq_fintype_card] using hnat
  rw [hcard]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : n ^ c ≤ n ^ (c + 1) := by
    rw [Nat.pow_succ]
    calc
      n ^ c = n ^ c * 1 := by simp
      _ ≤ n ^ c * n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hn)
  have h2 : n ^ b ≤ n ^ (b + 1) := by
    rw [Nat.pow_succ]
    calc
      n ^ b = n ^ b * 1 := by simp
      _ ≤ n ^ b * n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hn)
  have h3 : n ^ (c + 1) ≤ n ^ (a + c) := by
    have hac : c + 1 ≤ a + c := by omega
    exact Nat.pow_le_pow_right hn hac
  have h4 : n ^ (b + 1) ≤ n ^ (a + b) := by
    have hab : b + 1 ≤ a + b := by omega
    exact Nat.pow_le_pow_right hn hab
  have hs1 : n ^ (a + c) - (n ^ (c + 1) - n ^ c) = n ^ (a + c) - n ^ (c + 1) + n ^ c := by
    omega
  have hs2 : n ^ (a + b) - (n ^ (b + 1) - n ^ b) = n ^ (a + b) - n ^ (b + 1) + n ^ b := by
    omega
  rw [hs1, hs2]
  simp [survivingExponentABC, add_assoc, add_left_comm, add_comm]

theorem card_survivingBC_abc_real_closed_explicit {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (SurvivingBC_abc_real a b c n) =
      2 ^ (n ^ (a + c) + n ^ (a + b) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b + (n - 1) ^ 2) := by
  rw [card_survivingBC_abc_real_closed (a := a) (b := b) (c := c) (n := n) ha hb hc]
  rw [survivingExponentABC_eq_explicit (a := a) (b := b) (c := c) (n := n) ha]

theorem signed_imbalance_abc_real_closed {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_real (a := a) (b := b) (c := c) (n := n) =
      (2 : ℤ) ^ totalExponentABC a b c n := by
  have hcard :
      Fintype.card (SurvivingBC_abc_real a b c n) = 2 ^ survivingExponentABC a b c n :=
    card_survivingBC_abc_real_closed (a := a) (b := b) (c := c) (n := n) ha hb hc
  have hcardZ :
      (Fintype.card (SurvivingBC_abc_real a b c n) : ℤ) =
        (2 : ℤ) ^ survivingExponentABC a b c n := by
    exact_mod_cast hcard
  rw [deltaABCraw_real_eq_survivingBC_card, hcardZ]
  rw [← Int.pow_add]

theorem signed_imbalance_abc_real_closed_explicit {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_real (a := a) (b := b) (c := c) (n := n) =
      (2 : ℤ) ^ (n ^ (a + b) + n ^ (a + c) + n ^ (b + c) - n ^ (c + 1) - n ^ (b + 1) +
        n ^ c + n ^ b + (n - 1) ^ 2) := by
  rw [signed_imbalance_abc_real_closed (a := a) (b := b) (c := c) (n := n) ha hb hc]
  congr 1
  exact totalExponentABC_eq_explicit (a := a) (b := b) (c := c) (n := n) ha

theorem signed_imbalance_abc_primitive_closed {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_primitive (a := a) (b := b) (c := c) (n := n) =
      (2 : ℤ) ^ (n ^ (a + b) + n ^ (a + c) + n ^ (b + c) - n ^ (c + 1) - n ^ (b + 1) +
        n ^ c + n ^ b + (n - 1) ^ 2) := by
  calc
    deltaABCraw_primitive (a := a) (b := b) (c := c) (n := n)
        = deltaABCraw_real (a := a) (b := b) (c := c) (n := n) := by
            exact deltaABCraw_primitive_eq_deltaABCraw_real (a := a) (b := b) (c := c) (n := n) hb hc
    _ = (2 : ℤ) ^ (n ^ (a + b) + n ^ (a + c) + n ^ (b + c) - n ^ (c + 1) - n ^ (b + 1) +
          n ^ c + n ^ b + (n - 1) ^ 2) := by
            exact signed_imbalance_abc_real_closed_explicit
              (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem card_survivingBC_abc_real_closed_222 {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBC_abc_real 2 2 2 n) =
      2 ^ (2 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
  rw [card_survivingBC_abc_real_closed (a := 2) (b := 2) (c := 2) (n := n)
    (by decide) (by decide) (by decide)]
  congr 1
  exact surviving_exponent_222 (n := n)

theorem card_survivingBC_abc_real_regression_222 {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBC_abc_real 2 2 2 n) = Fintype.card (SurvivingBC n) := by
  rw [card_survivingBC_abc_real_closed_222, Fintype.card_survivingBC_closed_via_sigmaStrong]

theorem signed_imbalance_abc_real_closed_222 {n : ℕ} [NeZero n] :
    deltaABCraw_real (a := 2) (b := 2) (c := 2) (n := n) =
      (2 : ℤ) ^ (3 * n ^ 4 - 2 * n ^ 3 + 3 * n ^ 2 - 2 * n + 1) := by
  rw [signed_imbalance_abc_real_closed_explicit (a := 2) (b := 2) (c := 2) (n := n)
    (by decide) (by decide) (by decide)]
  congr 1
  exact total_exponent_222_explicit (n := n)

theorem signed_imbalance_abc_real_regression_222 {n : ℕ} [NeZero n] :
    deltaABCraw_real (a := 2) (b := 2) (c := 2) (n := n) = deltaNo13Raw n := by
  rw [signed_imbalance_abc_real_closed_222, signed_imbalance_no13_closed]

/-
Canonical honest public layer.

These are the objects to use for the faithful generalized No13 statement: raw valid assignments,
the real surviving kernel, and the raw signed sum. They sit on top of the completed honest route
without changing the legacy scaffold names above.
-/
abbrev ABCValidHonest {a b c n : ℕ} [NeZero n] (S : RawAssignmentABC a b c n) : Prop :=
  RawValidABC S

abbrev ABCValidAssignmentsHonest (a b c n : ℕ) [NeZero n] :=
  RawValidAssignmentsABC a b c n

abbrev ABCValidPrimitiveHonest {a b c n : ℕ} [NeZero n] (S : RawAssignmentABC a b c n) : Prop :=
  RawValidPrimitiveABC S

abbrev ABCValidPrimitiveAssignmentsHonest (a b c n : ℕ) [NeZero n] :=
  RawValidPrimitiveAssignmentsABC a b c n

abbrev SurvivingBC_abc_honest (a b c n : ℕ) [NeZero n] :=
  SurvivingBC_abc_real a b c n

noncomputable abbrev deltaABCraw_honest (a b c n : ℕ) [NeZero n] : ℤ :=
  deltaABCraw_raw (a := a) (b := b) (c := c) (n := n)

noncomputable abbrev deltaABCraw_primitive_honest (a b c n : ℕ) [NeZero n] : ℤ :=
  deltaABCraw_primitive (a := a) (b := b) (c := c) (n := n)

@[simp] theorem deltaABCraw_honest_eq_raw {a b c n : ℕ} [NeZero n] :
    deltaABCraw_honest a b c n = deltaABCraw_raw (a := a) (b := b) (c := c) (n := n) :=
  rfl

@[simp] theorem card_ABCValidAssignmentsHonest_eq_raw {a b c n : ℕ} [NeZero n] :
    Fintype.card (ABCValidAssignmentsHonest a b c n) =
      Fintype.card (RawValidAssignmentsABC a b c n) :=
  rfl

@[simp] theorem card_ABCValidPrimitiveAssignmentsHonest_eq_raw {a b c n : ℕ} [NeZero n] :
    Fintype.card (ABCValidPrimitiveAssignmentsHonest a b c n) =
      Fintype.card (RawValidPrimitiveAssignmentsABC a b c n) :=
  rfl

@[simp] theorem card_SurvivingBC_abc_honest_eq_real {a b c n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBC_abc_honest a b c n) =
      Fintype.card (SurvivingBC_abc_real a b c n) :=
  rfl

noncomputable def abcValidAssignmentsHonestEquivABCAssignment {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    ABCValidAssignmentsHonest a b c n ≃ ABCAssignment a b c n :=
  rawValidAssignmentsEquivABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc

noncomputable def abcValidPrimitiveAssignmentsHonestEquivABCAssignment {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    ABCValidPrimitiveAssignmentsHonest a b c n ≃ ABCAssignment a b c n :=
  rawValidPrimitiveAssignmentsEquivABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc

theorem card_validAssignments_abc_honest {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ABCValidAssignmentsHonest a b c n) =
      2 ^ (n ^ (b + c) + n ^ (a + c) + n ^ (a + b)) := by
  simpa using
    card_rawValidAssignmentsABC (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem card_validAssignments_abc_primitive_honest {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ABCValidPrimitiveAssignmentsHonest a b c n) =
      2 ^ (n ^ (b + c) + n ^ (a + c) + n ^ (a + b)) := by
  simpa using
    card_rawValidPrimitiveAssignmentsABC (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem deltaABCraw_honest_eq_real {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_honest a b c n = deltaABCraw_real (a := a) (b := b) (c := c) (n := n) := by
  simpa [deltaABCraw_honest] using
    deltaABCraw_raw_eq_deltaABCraw_real (a := a) (b := b) (c := c) (n := n) hb hc

theorem deltaABCraw_primitive_honest_eq_real {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_primitive_honest a b c n = deltaABCraw_real (a := a) (b := b) (c := c) (n := n) := by
  simpa [deltaABCraw_primitive_honest] using
    deltaABCraw_primitive_eq_deltaABCraw_real (a := a) (b := b) (c := c) (n := n) hb hc

theorem card_survivingBC_abc_honest_closed {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (SurvivingBC_abc_honest a b c n) =
      2 ^ (n ^ (a + c) + n ^ (a + b) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b +
        (n - 1) ^ 2) := by
  simpa [SurvivingBC_abc_honest] using
    card_survivingBC_abc_real_closed_explicit (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem signed_imbalance_abc_honest_closed {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_honest a b c n =
      (2 : ℤ) ^ (n ^ (a + b) + n ^ (a + c) + n ^ (b + c) - n ^ (c + 1) - n ^ (b + 1) +
        n ^ c + n ^ b + (n - 1) ^ 2) := by
  calc
    deltaABCraw_honest a b c n
        = deltaABCraw_real (a := a) (b := b) (c := c) (n := n) := by
            exact deltaABCraw_honest_eq_real (a := a) (b := b) (c := c) (n := n) hb hc
    _ = (2 : ℤ) ^ (n ^ (a + b) + n ^ (a + c) + n ^ (b + c) - n ^ (c + 1) - n ^ (b + 1) +
          n ^ c + n ^ b + (n - 1) ^ 2) := by
            exact signed_imbalance_abc_real_closed_explicit
              (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem signed_imbalance_abc_primitive_honest_closed {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_primitive_honest a b c n =
      (2 : ℤ) ^ (n ^ (a + b) + n ^ (a + c) + n ^ (b + c) - n ^ (c + 1) - n ^ (b + 1) +
        n ^ c + n ^ b + (n - 1) ^ 2) := by
  simpa [deltaABCraw_primitive_honest] using
    signed_imbalance_abc_primitive_closed (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem card_survivingBC_abc_honest_regression_222 {n : ℕ} [NeZero n] :
    Fintype.card (SurvivingBC_abc_honest 2 2 2 n) = Fintype.card (SurvivingBC n) := by
  simpa [SurvivingBC_abc_honest] using card_survivingBC_abc_real_regression_222 (n := n)

theorem signed_imbalance_abc_honest_regression_222 {n : ℕ} [NeZero n] :
    deltaABCraw_honest 2 2 2 n = deltaNo13Raw n := by
  calc
    deltaABCraw_honest 2 2 2 n
        = deltaABCraw_real (a := 2) (b := 2) (c := 2) (n := n) := by
            exact deltaABCraw_honest_eq_real (a := 2) (b := 2) (c := 2) (n := n)
              (by decide) (by decide)
    _ = deltaNo13Raw n := signed_imbalance_abc_real_regression_222 (n := n)

@[simp] lemma sumY_two {n : ℕ} [NeZero n] (y : YCoord 2 n) :
    sumY y = y 0 + y 1 := by
  simp [sumY, sumCoord]

@[simp] lemma sumZ_two {n : ℕ} [NeZero n] (z : ZCoord 2 n) :
    sumZ z = z 0 + z 1 := by
  simp [sumZ, sumCoord]

@[simp] lemma xCoord_two_eta {n : ℕ} (x : XCoord 2 n) : (fun _ : Fin 1 => x 0) = x := by
  ext i
  fin_cases i
  rfl

@[simp] lemma vec2_add_single_zero {n : ℕ} (a b : ZMod n) :
    vec2 a b + Pi.single 0 1 = vec2 (a + 1) b := by
  ext i
  fin_cases i <;> simp [vec2]

@[simp] lemma vec2_add_single_one {n : ℕ} (a b : ZMod n) :
    vec2 a b + Pi.single 1 1 = vec2 a (b + 1) := by
  ext i
  fin_cases i <;> simp [vec2]

@[simp] lemma vec5_add_e2 {n : ℕ} (a b c d e : ZMod n) :
    vec5 a b c d e + Pi.single 1 1 = vec5 a (b + 1) c d e := by
  ext i
  fin_cases i <;> simp [vec5]

@[simp] lemma vec5_add_e3 {n : ℕ} (a b c d e : ZMod n) :
    vec5 a b c d e + Pi.single 2 1 = vec5 a b (c + 1) d e := by
  ext i
  fin_cases i <;> simp [vec5]

@[simp] lemma vec5_add_e4 {n : ℕ} (a b c d e : ZMod n) :
    vec5 a b c d e + Pi.single 3 1 = vec5 a b c (d + 1) e := by
  ext i
  fin_cases i <;> simp [vec5]

@[simp] lemma vec5_add_e5 {n : ℕ} (a b c d e : ZMod n) :
    vec5 a b c d e + Pi.single 4 1 = vec5 a b c d (e + 1) := by
  ext i
  fin_cases i <;> simp [vec5]

noncomputable def rawSite222EquivT5 {n : ℕ} :
    RawSiteABC 2 2 2 n ≃ T5 n where
  toFun xyz := vec5 (xyz.1 0) (xyz.2.1 0) (xyz.2.1 1) (xyz.2.2 0) (xyz.2.2 1)
  invFun x := ((fun _ : Fin 1 => x 0), vec2 (x 1) (x 2), vec2 (x 3) (x 4))
  left_inv xyz := by
    rcases xyz with ⟨x, y, z⟩
    simp [xCoord_two_eta, vec2_eta]
  right_inv x := by
    simp [vec5_eta]

noncomputable def rawAssignmentABC222ToNo13Assignment {n : ℕ}
    (S : RawAssignmentABC 2 2 2 n) : No13Assignment n where
  alpha x := S.alpha ((rawSite222EquivT5 (n := n)).symm x)
  beta x := S.beta ((rawSite222EquivT5 (n := n)).symm x)
  gamma x := S.gamma ((rawSite222EquivT5 (n := n)).symm x)
  delta x := S.delta ((rawSite222EquivT5 (n := n)).symm x)
  eta x := S.eta ((rawSite222EquivT5 (n := n)).symm x)

noncomputable def no13AssignmentToRawAssignmentABC222 {n : ℕ}
    (S : No13Assignment n) : RawAssignmentABC 2 2 2 n where
  alpha xyz := S.alpha ((rawSite222EquivT5 (n := n)) xyz)
  beta xyz := S.beta ((rawSite222EquivT5 (n := n)) xyz)
  gamma xyz := S.gamma ((rawSite222EquivT5 (n := n)) xyz)
  delta xyz := S.delta ((rawSite222EquivT5 (n := n)) xyz)
  eta xyz := S.eta ((rawSite222EquivT5 (n := n)) xyz)

noncomputable def rawAssignmentABC222EquivNo13Assignment {n : ℕ} :
    RawAssignmentABC 2 2 2 n ≃ No13Assignment n where
  toFun := rawAssignmentABC222ToNo13Assignment
  invFun := no13AssignmentToRawAssignmentABC222
  left_inv S := by
    apply RawAssignmentABC.ext
    · funext xyz
      rcases xyz with ⟨x, y, z⟩
      simp [rawAssignmentABC222ToNo13Assignment, no13AssignmentToRawAssignmentABC222,
        rawSite222EquivT5, xCoord_two_eta, vec2_eta]
    · funext xyz
      rcases xyz with ⟨x, y, z⟩
      simp [rawAssignmentABC222ToNo13Assignment, no13AssignmentToRawAssignmentABC222,
        rawSite222EquivT5, xCoord_two_eta, vec2_eta]
    · funext xyz
      rcases xyz with ⟨x, y, z⟩
      simp [rawAssignmentABC222ToNo13Assignment, no13AssignmentToRawAssignmentABC222,
        rawSite222EquivT5, xCoord_two_eta, vec2_eta]
    · funext xyz
      rcases xyz with ⟨x, y, z⟩
      simp [rawAssignmentABC222ToNo13Assignment, no13AssignmentToRawAssignmentABC222,
        rawSite222EquivT5, xCoord_two_eta, vec2_eta]
    · funext xyz
      rcases xyz with ⟨x, y, z⟩
      simp [rawAssignmentABC222ToNo13Assignment, no13AssignmentToRawAssignmentABC222,
        rawSite222EquivT5, xCoord_two_eta, vec2_eta]
  right_inv S := by
    apply No13Assignment.ext
    · funext x
      simp [rawAssignmentABC222ToNo13Assignment, no13AssignmentToRawAssignmentABC222, rawSite222EquivT5]
    · funext x
      simp [rawAssignmentABC222ToNo13Assignment, no13AssignmentToRawAssignmentABC222, rawSite222EquivT5]
    · funext x
      simp [rawAssignmentABC222ToNo13Assignment, no13AssignmentToRawAssignmentABC222, rawSite222EquivT5]
    · funext x
      simp [rawAssignmentABC222ToNo13Assignment, no13AssignmentToRawAssignmentABC222, rawSite222EquivT5]
    · funext x
      simp [rawAssignmentABC222ToNo13Assignment, no13AssignmentToRawAssignmentABC222, rawSite222EquivT5]

lemma rawValidABC_222_to_No13Valid {n : ℕ} [NeZero n]
    (S : RawAssignmentABC 2 2 2 n) (hS : RawValidABC S) :
    No13Valid (rawAssignmentABC222ToNo13Assignment S) := by
  constructor
  · intro x
    simpa [rawAssignmentABC222ToNo13Assignment, rawSite222EquivT5, vec2] using
      hS.alpha_x_indep (fun _ : Fin 1 => x 0 + 1) (fun _ : Fin 1 => x 0) (vec2 (x 1) (x 2))
        (vec2 (x 3) (x 4))
  · intro x
    simpa [rawAssignmentABC222ToNo13Assignment, rawSite222EquivT5, vec2] using
      hS.gamma_beta_shift (fun _ : Fin 1 => x 0) (vec2 (x 1) (x 2)) (vec2 (x 3) (x 4)) 0
  · intro x
    simpa [rawAssignmentABC222ToNo13Assignment, rawSite222EquivT5, vec2] using
      hS.gamma_beta_shift (fun _ : Fin 1 => x 0) (vec2 (x 1) (x 2)) (vec2 (x 3) (x 4)) 1
  · intro x
    simpa [rawAssignmentABC222ToNo13Assignment, rawSite222EquivT5, vec2] using
      hS.eta_delta_shift (fun _ : Fin 1 => x 0) (vec2 (x 1) (x 2)) (vec2 (x 3) (x 4)) 0
  · intro x
    simpa [rawAssignmentABC222ToNo13Assignment, rawSite222EquivT5, vec2] using
      hS.eta_delta_shift (fun _ : Fin 1 => x 0) (vec2 (x 1) (x 2)) (vec2 (x 3) (x 4)) 1

lemma rawValidPrimitiveABC_222_to_No13Valid {n : ℕ} [NeZero n]
    (S : RawAssignmentABC 2 2 2 n) (hS : RawValidPrimitiveABC S) :
    No13Valid (rawAssignmentABC222ToNo13Assignment S) := by
  constructor
  · intro x
    simpa [rawAssignmentABC222ToNo13Assignment, rawSite222EquivT5, vec2] using
      hS.alpha_x_indep (fun _ : Fin 1 => x 0 + 1) (fun _ : Fin 1 => x 0) (vec2 (x 1) (x 2))
        (vec2 (x 3) (x 4))
  · intro x
    simpa [rawAssignmentABC222ToNo13Assignment, rawSite222EquivT5, vec2] using
      hS.gamma_beta_shift (fun _ : Fin 1 => x 0) (vec2 (x 1) (x 2)) (vec2 (x 3) (x 4)) 0
  · intro x
    simpa [rawAssignmentABC222ToNo13Assignment, rawSite222EquivT5, vec2] using
      hS.gamma_beta_shift (fun _ : Fin 1 => x 0) (vec2 (x 1) (x 2)) (vec2 (x 3) (x 4)) 1
  · intro x
    simpa [rawAssignmentABC222ToNo13Assignment, rawSite222EquivT5, vec2] using
      hS.eta_delta_shift (fun _ : Fin 1 => x 0) (vec2 (x 1) (x 2)) (vec2 (x 3) (x 4)) 0
  · intro x
    simpa [rawAssignmentABC222ToNo13Assignment, rawSite222EquivT5, vec2] using
      hS.eta_delta_shift (fun _ : Fin 1 => x 0) (vec2 (x 1) (x 2)) (vec2 (x 3) (x 4)) 1

lemma No13Valid_to_rawValidABC_222 {n : ℕ} [NeZero n]
    (S : No13Assignment n) (hS : No13Valid S) :
    RawValidABC (no13AssignmentToRawAssignmentABC222 S) := by
  constructor
  · intro x x' y z
    calc
      S.alpha ((rawSite222EquivT5 (n := n)) (x, y, z))
          = S.alpha (alphaCanonical (projA ((rawSite222EquivT5 (n := n)) (x, y, z)))) := by
        simpa [no13AssignmentToRawAssignmentABC222] using
          alpha_depends_only_projA S hS ((rawSite222EquivT5 (n := n)) (x, y, z))
      _ = S.alpha (alphaCanonical (projA ((rawSite222EquivT5 (n := n)) (x', y, z)))) := by
        simp [rawSite222EquivT5]
      _ = S.alpha ((rawSite222EquivT5 (n := n)) (x', y, z)) := by
        simpa [no13AssignmentToRawAssignmentABC222] using
          (alpha_depends_only_projA S hS ((rawSite222EquivT5 (n := n)) (x', y, z))).symm
  · intro x y y' z hyy
    rw [sumY_two, sumY_two] at hyy
    calc
      S.beta ((rawSite222EquivT5 (n := n)) (x, y, z))
          = S.beta (betaCanonical (projB ((rawSite222EquivT5 (n := n)) (x, y, z)))) := by
              exact beta_depends_only_projB S hS ((rawSite222EquivT5 (n := n)) (x, y, z))
      _ = S.beta (betaCanonical (projB ((rawSite222EquivT5 (n := n)) (x, y', z)))) := by
            simp [rawSite222EquivT5, hyy]
      _ = S.beta ((rawSite222EquivT5 (n := n)) (x, y', z)) := by
            exact (beta_depends_only_projB S hS ((rawSite222EquivT5 (n := n)) (x, y', z))).symm
  · intro x y z i
    fin_cases i
    · simpa [no13AssignmentToRawAssignmentABC222, rawSite222EquivT5, vec2] using
        hS.gamma_beta_e2 ((rawSite222EquivT5 (n := n)) (x, y, z))
    · simpa [no13AssignmentToRawAssignmentABC222, rawSite222EquivT5, vec2] using
        hS.gamma_beta_e3 ((rawSite222EquivT5 (n := n)) (x, y, z))
  · intro x y z z' hzz
    rw [sumZ_two, sumZ_two] at hzz
    calc
      S.delta ((rawSite222EquivT5 (n := n)) (x, y, z))
          = S.delta (deltaCanonical (projC ((rawSite222EquivT5 (n := n)) (x, y, z)))) := by
              exact delta_depends_only_projC S hS ((rawSite222EquivT5 (n := n)) (x, y, z))
      _ = S.delta (deltaCanonical (projC ((rawSite222EquivT5 (n := n)) (x, y, z')))) := by
            simp [rawSite222EquivT5, hzz]
      _ = S.delta ((rawSite222EquivT5 (n := n)) (x, y, z')) := by
            exact (delta_depends_only_projC S hS ((rawSite222EquivT5 (n := n)) (x, y, z'))).symm
  · intro x y z i
    fin_cases i
    · simpa [no13AssignmentToRawAssignmentABC222, rawSite222EquivT5, vec2] using
        hS.eta_delta_e4 ((rawSite222EquivT5 (n := n)) (x, y, z))
    · simpa [no13AssignmentToRawAssignmentABC222, rawSite222EquivT5, vec2] using
        hS.eta_delta_e5 ((rawSite222EquivT5 (n := n)) (x, y, z))

lemma No13Valid_to_rawValidPrimitiveABC_222 {n : ℕ} [NeZero n]
    (S : No13Assignment n) (hS : No13Valid S) :
    RawValidPrimitiveABC (no13AssignmentToRawAssignmentABC222 S) := by
  exact
    ⟨(No13Valid_to_rawValidABC_222 (n := n) S hS).alpha_x_indep,
      (No13Valid_to_rawValidABC_222 (n := n) S hS).gamma_beta_shift,
      (No13Valid_to_rawValidABC_222 (n := n) S hS).eta_delta_shift⟩

noncomputable def rawValidPrimitiveAssignmentsABC222EquivNo13ValidAssignments {n : ℕ} [NeZero n] :
    RawValidPrimitiveAssignmentsABC 2 2 2 n ≃ No13ValidAssignments n where
  toFun S := ⟨rawAssignmentABC222ToNo13Assignment S.1, rawValidPrimitiveABC_222_to_No13Valid S.1 S.2⟩
  invFun S := ⟨no13AssignmentToRawAssignmentABC222 S.1, No13Valid_to_rawValidPrimitiveABC_222 S.1 S.2⟩
  left_inv S := by
    apply Subtype.ext
    exact rawAssignmentABC222EquivNo13Assignment.left_inv S.1
  right_inv S := by
    apply Subtype.ext
    exact rawAssignmentABC222EquivNo13Assignment.right_inv S.1

noncomputable def rawValidAssignmentsABC222EquivNo13ValidAssignments {n : ℕ} [NeZero n] :
    RawValidAssignmentsABC 2 2 2 n ≃ No13ValidAssignments n where
  toFun S := ⟨rawAssignmentABC222ToNo13Assignment S.1, rawValidABC_222_to_No13Valid S.1 S.2⟩
  invFun S := ⟨no13AssignmentToRawAssignmentABC222 S.1, No13Valid_to_rawValidABC_222 S.1 S.2⟩
  left_inv S := by
    apply Subtype.ext
    exact rawAssignmentABC222EquivNo13Assignment.left_inv S.1
  right_inv S := by
    apply Subtype.ext
    exact rawAssignmentABC222EquivNo13Assignment.right_inv S.1

lemma rawLocalPhaseBitABC_no13AssignmentToRawAssignmentABC222 {n : ℕ} [NeZero n]
    (S : No13Assignment n) (xyz : RawSiteABC 2 2 2 n) :
    rawLocalPhaseBitABC (a := 2) (b := 2) (c := 2) (n := n)
        (no13AssignmentToRawAssignmentABC222 S) xyz =
      localPhaseBit S ((rawSite222EquivT5 (n := n)) xyz) := by
  simp [rawLocalPhaseBitABC, no13AssignmentToRawAssignmentABC222, localPhaseBit]

lemma W_abc_raw_no13AssignmentToRawAssignmentABC222_eq_W {n : ℕ} [NeZero n]
    (S : No13Assignment n) :
    W_abc_raw (a := 2) (b := 2) (c := 2) (n := n) (no13AssignmentToRawAssignmentABC222 S) = W S := by
  unfold W_abc_raw W
  calc
    ∏ xyz : RawSiteABC 2 2 2 n,
        bitSign
          (rawLocalPhaseBitABC (a := 2) (b := 2) (c := 2) (n := n)
            (no13AssignmentToRawAssignmentABC222 S) xyz)
        = ∏ xyz : RawSiteABC 2 2 2 n, bitSign (localPhaseBit S ((rawSite222EquivT5 (n := n)) xyz)) := by
            congr with xyz
    _ = ∏ x : T5 n, bitSign (localPhaseBit S x) := by
          simpa using (rawSite222EquivT5 (n := n)).prod_comp
            (fun x : T5 n => bitSign (localPhaseBit S x))

theorem signed_imbalance_abc_honest_regression_222_via_equiv {n : ℕ} [NeZero n] :
    deltaABCraw_honest 2 2 2 n = deltaNo13Raw n := by
  unfold deltaABCraw_honest deltaABCraw_raw deltaNo13Raw
  calc
    ∑ S : RawValidAssignmentsABC 2 2 2 n, W_abc_raw (a := 2) (b := 2) (c := 2) (n := n) S.1
        = ∑ S : No13ValidAssignments n,
            W_abc_raw (a := 2) (b := 2) (c := 2) (n := n)
              (no13AssignmentToRawAssignmentABC222 S.1) := by
              simpa using
                (((rawValidAssignmentsABC222EquivNo13ValidAssignments (n := n)).symm.sum_comp
                  (fun S : RawValidAssignmentsABC 2 2 2 n =>
                    W_abc_raw (a := 2) (b := 2) (c := 2) (n := n) S.1)).symm)
    _ = ∑ S : No13ValidAssignments n, W S.1 := by
          congr with S
          exact W_abc_raw_no13AssignmentToRawAssignmentABC222_eq_W (n := n) S.1

theorem card_validAssignments_abc_primitive_honest_regression_222 {n : ℕ} [NeZero n] :
    Fintype.card (ABCValidPrimitiveAssignmentsHonest 2 2 2 n) =
      Fintype.card (No13ValidAssignments n) := by
  exact Fintype.card_congr (rawValidPrimitiveAssignmentsABC222EquivNo13ValidAssignments (n := n))

theorem signed_imbalance_abc_primitive_honest_regression_222_via_equiv {n : ℕ} [NeZero n] :
    deltaABCraw_primitive_honest 2 2 2 n = deltaNo13Raw n := by
  unfold deltaABCraw_primitive_honest deltaABCraw_primitive deltaNo13Raw
  calc
    ∑ S : RawValidPrimitiveAssignmentsABC 2 2 2 n,
        W_abc_raw (a := 2) (b := 2) (c := 2) (n := n) S.1
        = ∑ S : No13ValidAssignments n,
            W_abc_raw (a := 2) (b := 2) (c := 2) (n := n)
              (no13AssignmentToRawAssignmentABC222 S.1) := by
              simpa using
                (((rawValidPrimitiveAssignmentsABC222EquivNo13ValidAssignments (n := n)).symm.sum_comp
                  (fun S : RawValidPrimitiveAssignmentsABC 2 2 2 n =>
                    W_abc_raw (a := 2) (b := 2) (c := 2) (n := n) S.1)).symm)
    _ = ∑ S : No13ValidAssignments n, W S.1 := by
          congr with S
          exact W_abc_raw_no13AssignmentToRawAssignmentABC222_eq_W (n := n) S.1

/-!
## Canonical finalized public API

These are the faithful public objects/theorems for the generalized No13 problem.
They use primitive raw validity on the assignment side, the honest surviving kernel,
and the raw signed sum.
-/

abbrev ABCValidFinal {a b c n : ℕ} [NeZero n] (S : RawAssignmentABC a b c n) : Prop :=
  ABCValidPrimitiveHonest S

abbrev ABCValidAssignmentsFinal (a b c n : ℕ) [NeZero n] :=
  ABCValidPrimitiveAssignmentsHonest a b c n

abbrev SurvivingBC_abc_final (a b c n : ℕ) [NeZero n] :=
  SurvivingBC_abc_honest a b c n

noncomputable abbrev deltaABCraw_final (a b c n : ℕ) [NeZero n] : ℤ :=
  deltaABCraw_primitive_honest (a := a) (b := b) (c := c) (n := n)

theorem card_validAssignments_abc_final {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ABCValidAssignmentsFinal a b c n) =
      2 ^ (n ^ (b + c) + n ^ (a + c) + n ^ (a + b)) := by
  simpa [ABCValidAssignmentsFinal] using
    card_validAssignments_abc_primitive_honest (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem card_survivingBC_abc_final_closed {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (SurvivingBC_abc_final a b c n) =
      2 ^ (n ^ (a + c) + n ^ (a + b) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b +
        (n - 1) ^ 2) := by
  simpa [SurvivingBC_abc_final] using
    card_survivingBC_abc_honest_closed (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem signed_imbalance_abc_final_closed {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    deltaABCraw_final a b c n =
      (2 : ℤ) ^ (n ^ (a + b) + n ^ (a + c) + n ^ (b + c) - n ^ (c + 1) - n ^ (b + 1) +
        n ^ c + n ^ b + (n - 1) ^ 2) := by
  simpa [deltaABCraw_final] using
    signed_imbalance_abc_primitive_honest_closed (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem signed_imbalance_abc_final_regression_222 {n : ℕ} [NeZero n] :
    deltaABCraw_final 2 2 2 n = deltaNo13Raw n := by
  simpa [deltaABCraw_final] using
    signed_imbalance_abc_primitive_honest_regression_222_via_equiv (n := n)

noncomputable def primitive_validity_regression_222 {n : ℕ} [NeZero n] :
    RawValidPrimitiveAssignmentsABC 2 2 2 n ≃ No13ValidAssignments n :=
  rawValidPrimitiveAssignmentsABC222EquivNo13ValidAssignments (n := n)

end No13Migration
