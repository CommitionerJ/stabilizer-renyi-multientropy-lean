import Mathlib

open scoped BigOperators

namespace Core4loop

abbrev F := ZMod 2
abbrev I (n : ℕ) := ZMod n

lemma F_add_self (x : F) : x + x = 0 := by
  fin_cases x <;> decide

lemma F_ne_zero_eq_one (x : F) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact False.elim (hx rfl)
  · rfl

lemma one_le_of_neZero {n : ℕ} [NeZero n] : 1 ≤ n := by
  exact Nat.succ_le_iff.mp (Nat.pos_iff_ne_zero.mpr (NeZero.ne n))

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

end Core4loop
