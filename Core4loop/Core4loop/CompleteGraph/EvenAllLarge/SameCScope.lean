import Core4loop.CompleteGraph.EvenAllLarge.FiberNormalization
import Core4loop.CompleteGraph.EvenAllLarge.Projection

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

/-! The exact obstruction to a universal same-C section. -/

def K4BaseSameCFunctional
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) : Prop :=
  K4DACoeffEquation sigma C ∧
    K4SBCoeffEquation sigma C ∧ K4SWCoeffEquation sigma C

def K4BaseSameCIndexed
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) : Prop :=
  K4DACoeffEquation sigma C ∧
    K4SBIndexedEquation sigma C ∧ K4SWIndexedEquation sigma C

theorem k4Base_sameCFunctional_iff_sameCIndexed
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    K4BaseSameCFunctional sigma C ↔ K4BaseSameCIndexed sigma C := by
  unfold K4BaseSameCFunctional K4BaseSameCIndexed
  rw [and_congr_right_iff]
  intro _hD
  exact k4Base_Sfunctional_iff_indexed sigma C

theorem k4Base_exists_sameCFunctional_iff_mem_ker_baseCross
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) :
    (∃ C : CFun4 n 1 b d, K4BaseSameCFunctional sigma C) ↔
      sigma ∈ LinearMap.ker
        (k4EvenPBaseCross
          (n := n) (b := b) (c := c) (d := d)) := by
  rw [← range_k4EvenPBaseProjection_eq_ker_baseCross]
  constructor
  · rintro ⟨C, hC⟩
    have hz :
        (sigma, k4BaseCFunDotDual C) ∈
          K4EvenPBaseMultiplierSolution n b c d :=
      (k4Base_multiplier_same_coefficient_iff sigma C).mpr hC
    refine ⟨⟨(sigma, k4BaseCFunDotDual C), hz⟩, ?_⟩
    rfl
  · rintro ⟨z, hz⟩
    let C : CFun4 n 1 b d := k4BaseLambdaRead z.1.2
    have hsame :
        (z.1.1, k4BaseCFunDotDual C) ∈
          K4EvenPBaseMultiplierSolution n b c d := by
      simp [C]
    have hC : K4BaseSameCFunctional z.1.1 C :=
      (k4Base_multiplier_same_coefficient_iff z.1.1 C).mp hsame
    have hsigma : z.1.1 = sigma := by
      simpa [k4EvenPBaseProjection] using hz
    exact ⟨C, hsigma ▸ hC⟩

theorem k4Base_forall_exists_sameCFunctional_iff_baseCross_eq_zero
    {n b c d : Nat} [NeZero n] :
    (∀ sigma : K4EvenPLeft n b c d,
      ∃ C : CFun4 n 1 b d, K4BaseSameCFunctional sigma C) ↔
      k4EvenPBaseCross (n := n) (b := b) (c := c) (d := d) = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro sigma
    exact LinearMap.mem_ker.mp
      ((k4Base_exists_sameCFunctional_iff_mem_ker_baseCross sigma).mp
        (h sigma))
  · intro h sigma
    apply (k4Base_exists_sameCFunctional_iff_mem_ker_baseCross sigma).mpr
    apply LinearMap.mem_ker.mpr
    rw [h]
    rfl

theorem k4Base_exists_sameCIndexed_iff_mem_ker_baseCross
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) :
    (∃ C : CFun4 n 1 b d, K4BaseSameCIndexed sigma C) ↔
      sigma ∈ LinearMap.ker
        (k4EvenPBaseCross
          (n := n) (b := b) (c := c) (d := d)) := by
  rw [← k4Base_exists_sameCFunctional_iff_mem_ker_baseCross sigma]
  constructor <;> rintro ⟨C, hC⟩
  · exact ⟨C, (k4Base_sameCFunctional_iff_sameCIndexed sigma C).mpr hC⟩
  · exact ⟨C, (k4Base_sameCFunctional_iff_sameCIndexed sigma C).mp hC⟩

theorem k4Base_forall_exists_sameCIndexed_iff_baseCross_eq_zero
    {n b c d : Nat} [NeZero n] :
    (∀ sigma : K4EvenPLeft n b c d,
      ∃ C : CFun4 n 1 b d, K4BaseSameCIndexed sigma C) ↔
      k4EvenPBaseCross (n := n) (b := b) (c := c) (d := d) = 0 := by
  rw [← k4Base_forall_exists_sameCFunctional_iff_baseCross_eq_zero]
  constructor
  · intro h sigma
    rcases h sigma with ⟨C, hC⟩
    exact ⟨C, (k4Base_sameCFunctional_iff_sameCIndexed sigma C).mpr hC⟩
  · intro h sigma
    rcases h sigma with ⟨C, hC⟩
    exact ⟨C, (k4Base_sameCFunctional_iff_sameCIndexed sigma C).mp hC⟩

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
