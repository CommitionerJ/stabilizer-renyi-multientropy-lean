import Mathlib

open scoped BigOperators

namespace No16

abbrev F := ZMod 2
abbrev I (n : ℕ) := ZMod n

abbrev AFun (n : ℕ) := I n → I n → I n → I n → F
abbrev BFun (n : ℕ) := I n → I n → I n → I n → F
abbrev CFun (n : ℕ) := I n → I n → I n → I n → F

abbrev Profile (n : ℕ) := I n → F
abbrev BCoef (n : ℕ) := I n → I n → I n → F
abbrev CCoef (n : ℕ) := I n → I n → I n → F

abbrev Quad (n : ℕ) := I n × I n × I n × I n
abbrev Quint (n : ℕ) := I n × I n × I n × I n × I n

lemma F_add_self (x : F) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod_step_const {n : ℕ} [NeZero n] {α : Type*} (g : I n → α)
    (h : ∀ s, g (s + 1) = g s) :
    ∀ s, g s = g 0 := by
  intro s
  have hNat : ∀ m : ℕ, g (m : I n) = g 0 := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m hm =>
        calc
          g ((m + 1 : ℕ) : I n) = g ((m : I n) + 1) := by simp
          _ = g (m : I n) := h _
          _ = g 0 := hm
  simpa [I, ZMod.natCast_val] using hNat s.val

lemma card_quad (n : ℕ) [NeZero n] : Fintype.card (Quad n) = n ^ 4 := by
  calc
    Fintype.card (Quad n) = n * n * n * n := by
      simp [Quad, I, ZMod.card, Nat.mul_assoc]
    _ = n ^ 4 := by ring

noncomputable def aFunEquivQuad (n : ℕ) : AFun n ≃ (Quad n → F) where
  toFun f := fun | ⟨u1, u2, u3, u4⟩ => f u1 u2 u3 u4
  invFun f := fun u1 u2 u3 u4 => f (u1, u2, u3, u4)
  left_inv f := by
    funext u1 u2 u3 u4
    rfl
  right_inv f := by
    funext u
    rcases u with ⟨u1, u2, u3, u4⟩
    rfl

noncomputable def bFunEquivQuad (n : ℕ) : BFun n ≃ (Quad n → F) :=
  aFunEquivQuad n

noncomputable def cFunEquivQuad (n : ℕ) : CFun n ≃ (Quad n → F) :=
  aFunEquivQuad n

noncomputable def bCoefEquivTriple (n : ℕ) : BCoef n ≃ (I n × I n × I n → F) where
  toFun f := fun | ⟨t, p, q'⟩ => f t p q'
  invFun f := fun t p q' => f (t, p, q')
  left_inv f := by
    funext t p q'
    rfl
  right_inv f := by
    funext u
    rcases u with ⟨t, p, q'⟩
    rfl

noncomputable def cCoefEquivTriple (n : ℕ) : CCoef n ≃ (I n × I n × I n → F) :=
  bCoefEquivTriple n

noncomputable instance aFunFintype (n : ℕ) [NeZero n] : Fintype (AFun n) := by
  infer_instance

noncomputable instance bFunFintype (n : ℕ) [NeZero n] : Fintype (BFun n) := by
  infer_instance

noncomputable instance cFunFintype (n : ℕ) [NeZero n] : Fintype (CFun n) := by
  infer_instance

noncomputable instance bCoefFintype (n : ℕ) [NeZero n] : Fintype (BCoef n) := by
  infer_instance

noncomputable instance cCoefFintype (n : ℕ) [NeZero n] : Fintype (CCoef n) := by
  infer_instance

lemma card_AFun (n : ℕ) [NeZero n] : Fintype.card (AFun n) = 2 ^ (n ^ 4) := by
  rw [Fintype.card_congr (aFunEquivQuad n), Fintype.card_fun, card_quad]
  simp [F]

lemma card_BFun (n : ℕ) [NeZero n] : Fintype.card (BFun n) = 2 ^ (n ^ 4) := by
  rw [Fintype.card_congr (bFunEquivQuad n), Fintype.card_fun, card_quad]
  simp [F]

lemma card_CFun (n : ℕ) [NeZero n] : Fintype.card (CFun n) = 2 ^ (n ^ 4) := by
  rw [Fintype.card_congr (cFunEquivQuad n), Fintype.card_fun, card_quad]
  simp [F]

lemma card_BCoef (n : ℕ) [NeZero n] : Fintype.card (BCoef n) = 2 ^ (n ^ 3) := by
  rw [Fintype.card_congr (bCoefEquivTriple n), Fintype.card_fun]
  have hs : n * (n * n) = n ^ 3 := by ring
  simpa [F, I, ZMod.card, hs]

lemma card_CCoef (n : ℕ) [NeZero n] : Fintype.card (CCoef n) = 2 ^ (n ^ 3) := by
  rw [Fintype.card_congr (cCoefEquivTriple n), Fintype.card_fun]
  have hs : n * (n * n) = n ^ 3 := by ring
  simpa [F, I, ZMod.card, hs]

end No16
