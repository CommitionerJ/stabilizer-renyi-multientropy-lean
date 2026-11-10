import Core4loop.TriangleCore.Basic

open scoped BigOperators

namespace Core4loop
namespace TriangleCore

lemma sum_triple_add {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (f g : α → β → γ → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, (f a b c + g a b c)) =
      (∑ a : α, ∑ b : β, ∑ c : γ, f a b c) +
        (∑ a : α, ∑ b : β, ∑ c : γ, g a b c) := by
  simp [Finset.sum_add_distrib]

noncomputable def triAlpha {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) (_p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) : F :=
  nf.A y z

noncomputable def triBeta {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) : F :=
  nf.B p (vecSum y) z

noncomputable def triGamma {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) : F :=
  nf.B p (vecSum y + 1) z

noncomputable def triDelta {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) : F :=
  nf.C p y (vecSum z)

noncomputable def triEta {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) : F :=
  nf.C p y (vecSum z + 1)

noncomputable def triLinearTerms {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) : F :=
  (triBeta nf p y z + triGamma nf p y z) +
    (triDelta nf p y z + triEta nf p y z)

noncomputable def triGraphPhase {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) : F :=
  let α := triAlpha nf p y z
  let β := triBeta nf p y z
  let γ := triGamma nf p y z
  let δ := triDelta nf p y z
  let η := triEta nf p y z
  α * (β + γ + δ + η) + β * δ + γ * η

noncomputable def triNo16Phase {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) : F :=
  triLinearTerms nf p y z + triGraphPhase nf p y z

lemma tri_beta_gamma_sum_zero
    {r s t n : ℕ} [NeZero n] (hs : 0 < s)
    (nf : TriNF n r s t) :
    (∑ p : TriPVec n r, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
      (triBeta nf p y z + triGamma nf p y z)) = 0 := by
  have hpoint :
      ∀ p : TriPVec n r, ∀ z : TriZVec n t,
        (∑ y : TriYVec n s, (triBeta nf p y z + triGamma nf p y z)) = 0 := by
    intro p z
    simpa [triBeta, triGamma, TriYVec] using
      (sum_cyclic_difference_over_vecSum_zero
        (n := n) (k := s) hs (fun sy : I n => nf.B p sy z))
  calc
    (∑ p : TriPVec n r, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
      (triBeta nf p y z + triGamma nf p y z))
        = ∑ p : TriPVec n r, ∑ z : TriZVec n t, ∑ y : TriYVec n s,
            (triBeta nf p y z + triGamma nf p y z) := by
            refine Finset.sum_congr rfl ?_
            intro p _
            rw [Finset.sum_comm]
    _ = 0 := by
      simp [hpoint]

lemma tri_delta_eta_sum_zero
    {r s t n : ℕ} [NeZero n] (ht : 0 < t)
    (nf : TriNF n r s t) :
    (∑ p : TriPVec n r, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
      (triDelta nf p y z + triEta nf p y z)) = 0 := by
  have hpoint :
      ∀ p : TriPVec n r, ∀ y : TriYVec n s,
        (∑ z : TriZVec n t, (triDelta nf p y z + triEta nf p y z)) = 0 := by
    intro p y
    simpa [triDelta, triEta, TriZVec] using
      (sum_cyclic_difference_over_vecSum_zero
        (n := n) (k := t) ht (fun sz : I n => nf.C p y sz))
  simp [hpoint]

lemma tri_linear_terms_sum_zero
    {r s t n : ℕ} [NeZero n]
    (hs : 0 < s) (ht : 0 < t)
    (nf : TriNF n r s t) :
    (∑ p : TriPVec n r, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
      triLinearTerms nf p y z) = 0 := by
  unfold triLinearTerms
  rw [sum_triple_add
    (f := fun p y z => triBeta nf p y z + triGamma nf p y z)
    (g := fun p y z => triDelta nf p y z + triEta nf p y z)]
  simp only [tri_beta_gamma_sum_zero (n := n) (r := r) (s := s) (t := t) hs nf,
    tri_delta_eta_sum_zero (n := n) (r := r) (s := s) (t := t) ht nf, add_zero]

noncomputable def triGraphExponent {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) : F :=
  ∑ p : TriPVec n r, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
    triGraphPhase nf p y z

noncomputable def triNo16Exponent {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) : F :=
  ∑ p : TriPVec n r, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
    triNo16Phase nf p y z

lemma triGraphExponent_eq_triNo16Exponent
    {r s t n : ℕ} [NeZero n]
    (hs : 0 < s) (ht : 0 < t)
    (nf : TriNF n r s t) :
    triGraphExponent nf = triNo16Exponent nf := by
  unfold triGraphExponent triNo16Exponent triNo16Phase
  symm
  rw [sum_triple_add
    (f := fun p y z => triLinearTerms nf p y z)
    (g := fun p y z => triGraphPhase nf p y z)]
  rw [tri_linear_terms_sum_zero (n := n) (r := r) (s := s) (t := t) hs ht nf]
  simp

noncomputable def DeltaTriangleCore (r s t n : ℕ) [NeZero n] : ℤ :=
  ∑ nf : TriNF n r s t, bitSign (triGraphExponent nf)

end TriangleCore
end Core4loop
