import Core4loop.Vec

open scoped BigOperators

namespace Core4loop

def bitSign (b : F) : ℤ := if b = 0 then 1 else -1

lemma bitSign_zero : bitSign (0 : F) = 1 := by
  simp [bitSign]

lemma bitSign_one : bitSign (1 : F) = -1 := by
  decide

lemma bitSign_add (a b : F) : bitSign (a + b) = bitSign a * bitSign b := by
  fin_cases a <;> fin_cases b <;> decide

lemma bitSign_add_one (a : F) : bitSign (a + 1) = -bitSign a := by
  fin_cases a <;> decide

noncomputable def coeffApply {ι : Type*} [Fintype ι]
    (c f : ι → F) : F :=
  ∑ i : ι, f i * c i

noncomputable def signedCoeffSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → F) : ℤ :=
  ∑ f : ι → F, bitSign (coeffApply c f)

noncomputable def toggleAt {ι : Type*} [DecidableEq ι]
    (i0 : ι) (f : ι → F) : ι → F :=
  fun i => f i + if i = i0 then 1 else 0

noncomputable def toggleAtEquiv {ι : Type*} [DecidableEq ι]
    (i0 : ι) : (ι → F) ≃ (ι → F) where
  toFun := toggleAt i0
  invFun := toggleAt i0
  left_inv f := by
    funext i
    by_cases h : i = i0
    · subst h
      simp only [toggleAt, ↓reduceIte, add_assoc, F_add_self, add_zero]
    · simp only [toggleAt, h, ↓reduceIte, add_zero]
  right_inv f := by
    funext i
    by_cases h : i = i0
    · subst h
      simp only [toggleAt, ↓reduceIte, add_assoc, F_add_self, add_zero]
    · simp only [toggleAt, h, ↓reduceIte, add_zero]

lemma coeffApply_toggleAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c f : ι → F) (i0 : ι) :
    coeffApply c (toggleAt i0 f) = coeffApply c f + c i0 := by
  classical
  unfold coeffApply toggleAt
  have hterm :
      (∑ i : ι, (if i = i0 then (1 : F) else 0) * c i) = c i0 := by
    rw [Finset.sum_eq_single i0]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  calc
    (∑ i : ι, (f i + if i = i0 then 1 else 0) * c i)
        = ∑ i : ι, (f i * c i + (if i = i0 then 1 else 0) * c i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
    _ = (∑ i : ι, f i * c i) + ∑ i : ι, (if i = i0 then 1 else 0) * c i := by
            rw [Finset.sum_add_distrib]
    _ = (∑ i : ι, f i * c i) + c i0 := by
            rw [hterm]

lemma signedCoeff_toggleAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c f : ι → F) (i0 : ι) (hc : c i0 = 1) :
    bitSign (coeffApply c (toggleAt i0 f)) = -bitSign (coeffApply c f) := by
  rw [coeffApply_toggleAt, hc, bitSign_add_one]

lemma signedCoeffSum_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    signedCoeffSum (0 : ι → F) = (2 : ℤ) ^ Fintype.card ι := by
  classical
  unfold signedCoeffSum coeffApply
  calc
    (∑ f : ι → F, bitSign (∑ i : ι, f i * (0 : ι → F) i))
        = ∑ _f : ι → F, (1 : ℤ) := by
            simp [bitSign_zero]
    _ = (Fintype.card (ι → F) : ℤ) := by
            simp
    _ = (2 : ℤ) ^ Fintype.card ι := by
            rw [Fintype.card_fun]
            simp [F]

theorem signedCoeffSum_formula
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → F) :
    signedCoeffSum c =
      if c = 0 then (2 : ℤ) ^ Fintype.card ι else 0 := by
  classical
  by_cases hc : c = 0
  · simp [hc, signedCoeffSum_zero]
  · have hne : ∃ i0 : ι, c i0 ≠ 0 := by
      by_contra hforall
      apply hc
      funext i
      by_contra hi
      exact hforall ⟨i, hi⟩
    rcases hne with ⟨i0, hi0⟩
    have hci0 : c i0 = 1 := F_ne_zero_eq_one _ hi0
    have hsum : signedCoeffSum c = -signedCoeffSum c := by
      unfold signedCoeffSum
      calc
        (∑ f : ι → F, bitSign (coeffApply c f))
            = ∑ f : ι → F, bitSign (coeffApply c (toggleAt i0 f)) := by
                simpa using
                  (((toggleAtEquiv i0).sum_comp
                    (fun f : ι → F => bitSign (coeffApply c f))).symm)
        _ = ∑ f : ι → F, -bitSign (coeffApply c f) := by
                refine Finset.sum_congr rfl ?_
                intro f _
                exact signedCoeff_toggleAt c f i0 hci0
        _ = -∑ f : ι → F, bitSign (coeffApply c f) := by
                simp
    have hz : signedCoeffSum c = 0 := by
      linarith
    simp [hc, hz]

lemma pair_elim_F (L M : F) :
    (∑ u : F, ∑ v : F, bitSign (u * v + u * L + v * M))
      = 2 * bitSign (L * M) := by
  fin_cases L <;> fin_cases M <;> decide

end Core4loop
