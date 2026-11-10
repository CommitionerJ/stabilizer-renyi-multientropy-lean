import Core4loop.Basic

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem sum_mul_ite_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → F) (a₀ : α) (C : F) :
    (∑ a : α, f a * (if a = a₀ then C else 0)) = f a₀ * C := by
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ ha
    have hif : (if a = a₀ then C else 0) = 0 := by
      simp [ha]
    rw [hif, mul_zero]
  · simp

theorem sum_ite_eq_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → F) (a₀ : α) (C : F) :
    (∑ a : α, (if a = a₀ then C else 0) * f a) = C * f a₀ := by
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ ha
    have hif : (if a = a₀ then C else 0) = 0 := by
      simp [ha]
    rw [hif, zero_mul]
  · simp

theorem sum_mul_ite_eq_comm
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → F) (a₀ : α) (C : F) :
    (∑ a : α, f a * (if a₀ = a then C else 0)) = f a₀ * C := by
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ ha
    have hne : a₀ ≠ a := fun h => ha h.symm
    have hif : (if a₀ = a then C else 0) = 0 := by
      simp [hne]
    rw [hif, mul_zero]
  · simp

theorem sum_ite_eq_mul_comm
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → F) (a₀ : α) (C : F) :
    (∑ a : α, (if a₀ = a then C else 0) * f a) = C * f a₀ := by
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ ha
    have hne : a₀ ≠ a := fun h => ha h.symm
    have hif : (if a₀ = a then C else 0) = 0 := by
      simp [hne]
    rw [hif, zero_mul]
  · simp

theorem sum_mul_sum_ite_eq
    {α Ω : Type*} [Fintype α] [DecidableEq α] [Fintype Ω]
    (K : α → F) (A : Ω → F) (target : Ω → α) :
    (∑ s : α, K s * ∑ ω : Ω, if s = target ω then A ω else 0)
      =
      ∑ ω : Ω, A ω * K (target ω) := by
  calc
    (∑ s : α, K s * ∑ ω : Ω, if s = target ω then A ω else 0)
        =
        ∑ s : α, ∑ ω : Ω, K s * (if s = target ω then A ω else 0) := by
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [Finset.mul_sum]
    _ =
        ∑ ω : Ω, ∑ s : α, K s * (if s = target ω then A ω else 0) := by
          rw [Finset.sum_comm]
    _ =
        ∑ ω : Ω, A ω * K (target ω) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [sum_mul_ite_eq]
          ring

theorem sum_mul_add_selector_weight
    {α Ω : Type*} [Fintype α] [DecidableEq α] [Fintype Ω]
    (K B : α → F) (A : Ω → F) (target : Ω → α) (w : F) :
    (∑ s : α, K s * ((∑ ω : Ω, if s = target ω then A ω else 0) + w * B s))
      =
      (∑ ω : Ω, A ω * K (target ω)) + w * ∑ s : α, B s * K s := by
  calc
    (∑ s : α, K s * ((∑ ω : Ω, if s = target ω then A ω else 0) + w * B s))
        =
        (∑ s : α, K s * ∑ ω : Ω, if s = target ω then A ω else 0)
          +
        ∑ s : α, K s * (w * B s) := by
          simp only [mul_add, Finset.sum_add_distrib]
    _ =
        (∑ ω : Ω, A ω * K (target ω))
          +
        ∑ s : α, w * (B s * K s) := by
          rw [sum_mul_sum_ite_eq]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro s _
          ring
    _ =
        (∑ ω : Ω, A ω * K (target ω)) + w * ∑ s : α, B s * K s := by
          rw [Finset.mul_sum]

theorem sum_mul_triple_ite_eq
    {α β γ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (K : α → β → γ → F) (a₀ : α) (b₀ : β) (c₀ : γ) (C : F) :
    (∑ b : β, ∑ c : γ, ∑ a : α,
      K a b c *
        (if b = b₀ then
          if c = c₀ then
            if a = a₀ then C else 0
          else 0
        else 0))
      =
      C * K a₀ b₀ c₀ := by
  rw [Finset.sum_eq_single b₀]
  · rw [Finset.sum_eq_single c₀]
    · simp
      ring
    · intro c _ hc
      refine Finset.sum_eq_zero ?_
      intro a _
      simp [hc]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero ?_
    intro c _
    refine Finset.sum_eq_zero ?_
    intro a _
    simp [hb]
  · simp

end

end TriangleLeaf
end Core4loop
