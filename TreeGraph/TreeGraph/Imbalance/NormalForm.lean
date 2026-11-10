import TreeGraph.Imbalance.BranchTransfer

namespace TreeGraph
namespace Imbalance

noncomputable def signedCharacterSum
    (Ω : Type) [Fintype Ω] (phase : Ω → F2) : ℤ :=
  ∑ ω : Ω, chi (phase ω)

theorem signedCharacterSum_congr_equiv
    {Ω Ω' : Type} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (phase : Ω → F2) (phase' : Ω' → F2)
    (hphase : ∀ ω, phase ω = phase' (e ω)) :
    signedCharacterSum Ω phase = signedCharacterSum Ω' phase' := by
  unfold signedCharacterSum
  exact Fintype.sum_equiv e
    (fun ω => chi (phase ω))
    (fun ω' => chi (phase' ω'))
    (by
      intro ω
      simp [hphase ω])

theorem signedCharacterSum_congr_equiv_symm
    {Ω Ω' : Type} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (phase : Ω → F2) (phase' : Ω' → F2)
    (hphase : ∀ ω', phase (e.symm ω') = phase' ω') :
    signedCharacterSum Ω phase = signedCharacterSum Ω' phase' := by
  refine signedCharacterSum_congr_equiv e phase phase' ?_
  intro ω
  have h := hphase (e ω)
  simpa using h

theorem signedCharacterSum_congr
    {Ω : Type} [Fintype Ω] (phase phase' : Ω → F2)
    (hphase : ∀ ω, phase ω = phase' ω) :
    signedCharacterSum Ω phase = signedCharacterSum Ω phase' := by
  exact signedCharacterSum_congr_equiv (Equiv.refl Ω) phase phase'
    (by intro ω; exact hphase ω)

theorem signedCharacterSum_zero
    (Ω : Type) [Fintype Ω] :
    signedCharacterSum Ω (fun _ => (0 : F2)) =
      (Fintype.card Ω : ℤ) := by
  unfold signedCharacterSum
  simp

theorem phaseSum_eq_of_equiv
    {Raw Normal : Type} [Fintype Raw] [Fintype Normal]
    (e : Raw ≃ Normal) (rawPhase : Raw → F2) (normalPhase : Normal → F2)
    (hphase : ∀ A, rawPhase A = normalPhase (e A)) :
    (∑ A : Raw, chi (rawPhase A)) =
      ∑ F : Normal, chi (normalPhase F) := by
  exact signedCharacterSum_congr_equiv e rawPhase normalPhase hphase

theorem phaseSum_eq_of_equiv_symm
    {Raw Normal : Type} [Fintype Raw] [Fintype Normal]
    (e : Raw ≃ Normal) (rawPhase : Raw → F2) (normalPhase : Normal → F2)
    (hphase : ∀ F, rawPhase (e.symm F) = normalPhase F) :
    (∑ A : Raw, chi (rawPhase A)) =
      ∑ F : Normal, chi (normalPhase F) := by
  exact signedCharacterSum_congr_equiv_symm e rawPhase normalPhase hphase

structure PhaseBridge (Raw Normal : Type)
    [Fintype Raw] [Fintype Normal] where
  toEquiv : Raw ≃ Normal
  rawPhase : Raw → F2
  normalPhase : Normal → F2
  phase_preserved : ∀ A, rawPhase A = normalPhase (toEquiv A)

namespace PhaseBridge

noncomputable def rawSum
    {Raw Normal : Type} [Fintype Raw] [Fintype Normal]
    (B : PhaseBridge Raw Normal) : ℤ :=
  ∑ A : Raw, chi (B.rawPhase A)

noncomputable def normalSum
    {Raw Normal : Type} [Fintype Raw] [Fintype Normal]
    (B : PhaseBridge Raw Normal) : ℤ :=
  ∑ F : Normal, chi (B.normalPhase F)

theorem sum_eq
    {Raw Normal : Type} [Fintype Raw] [Fintype Normal]
    (B : PhaseBridge Raw Normal) :
    B.rawSum = B.normalSum := by
  exact phaseSum_eq_of_equiv B.toEquiv B.rawPhase B.normalPhase
    B.phase_preserved

end PhaseBridge

noncomputable def linearSignedSum
    (W : Type) [AddCommGroup W] [Module F2 W] [Fintype W]
    (ell : W →ₗ[F2] F2) : ℤ :=
  signedCharacterSum W ell

theorem linearSignedSum_zero_card
    (W : Type) [AddCommGroup W] [Module F2 W] [Fintype W] :
    linearSignedSum W (0 : W →ₗ[F2] F2) =
      (Fintype.card W : ℤ) := by
  unfold linearSignedSum
  exact signedCharacterSum_zero W

theorem linearSignedSum_congr
    {W : Type} [AddCommGroup W] [Module F2 W] [Fintype W]
    (ell ell' : W →ₗ[F2] F2)
    (hphase : ∀ w, ell w = ell' w) :
    linearSignedSum W ell = linearSignedSum W ell' := by
  unfold linearSignedSum
  exact signedCharacterSum_congr ell ell' hphase

theorem linearSignedSum_congr_linearEquiv
    {W W' : Type} [AddCommGroup W] [Module F2 W] [Fintype W]
    [AddCommGroup W'] [Module F2 W'] [Fintype W']
    (e : W ≃ₗ[F2] W') (ell : W →ₗ[F2] F2) (ell' : W' →ₗ[F2] F2)
    (hphase : ∀ w, ell w = ell' (e w)) :
    linearSignedSum W ell = linearSignedSum W' ell' := by
  unfold linearSignedSum
  exact signedCharacterSum_congr_equiv e.toEquiv ell ell' hphase

theorem linearSignedSum_comp_linearEquiv
    {W W' : Type} [AddCommGroup W] [Module F2 W] [Fintype W]
    [AddCommGroup W'] [Module F2 W'] [Fintype W']
    (e : W ≃ₗ[F2] W') (ell' : W' →ₗ[F2] F2) :
    linearSignedSum W (ell'.comp e.toLinearMap) =
      linearSignedSum W' ell' := by
  exact linearSignedSum_congr_linearEquiv e
    (ell'.comp e.toLinearMap) ell' (by intro w; rfl)

theorem linearSignedSum_eq
    (W : Type) [AddCommGroup W] [Module F2 W] [Fintype W]
    [FiniteDimensional F2 W]
    (ell : W →ₗ[F2] F2) :
    linearSignedSum W ell =
      if ell = 0 then (2 : ℤ) ^ Module.finrank F2 W else 0 := by
  unfold linearSignedSum signedCharacterSum
  exact char_sum_linear ell

noncomputable def allowedSignedSum
    {V : Type} [AddCommGroup V] [Module F2 V]
    (K : Submodule F2 V) [Fintype K]
    (ell : K →ₗ[F2] F2) : ℤ :=
  linearSignedSum K ell

theorem allowedSignedSum_zero_card
    {V : Type} [AddCommGroup V] [Module F2 V]
    (K : Submodule F2 V) [Fintype K] :
    allowedSignedSum K 0 = (Fintype.card K : ℤ) := by
  unfold allowedSignedSum
  exact linearSignedSum_zero_card K

theorem allowedSignedSum_congr
    {V : Type} [AddCommGroup V] [Module F2 V]
    (K : Submodule F2 V) [Fintype K]
    (ell ell' : K →ₗ[F2] F2)
    (hphase : ∀ k, ell k = ell' k) :
    allowedSignedSum K ell = allowedSignedSum K ell' := by
  unfold allowedSignedSum
  exact linearSignedSum_congr ell ell' hphase

theorem allowedSignedSum_congr_linearEquiv
    {V V' : Type} [AddCommGroup V] [Module F2 V]
    [AddCommGroup V'] [Module F2 V']
    (K : Submodule F2 V) [Fintype K]
    (K' : Submodule F2 V') [Fintype K']
    (e : K ≃ₗ[F2] K') (ell : K →ₗ[F2] F2) (ell' : K' →ₗ[F2] F2)
    (hphase : ∀ k, ell k = ell' (e k)) :
    allowedSignedSum K ell = allowedSignedSum K' ell' := by
  unfold allowedSignedSum
  exact linearSignedSum_congr_linearEquiv e ell ell' hphase

theorem allowedSignedSum_comp_linearEquiv
    {V V' : Type} [AddCommGroup V] [Module F2 V]
    [AddCommGroup V'] [Module F2 V']
    (K : Submodule F2 V) [Fintype K]
    (K' : Submodule F2 V') [Fintype K']
    (e : K ≃ₗ[F2] K') (ell' : K' →ₗ[F2] F2) :
    allowedSignedSum K (ell'.comp e.toLinearMap) =
      allowedSignedSum K' ell' := by
  exact allowedSignedSum_congr_linearEquiv K K' e
    (ell'.comp e.toLinearMap) ell' (by intro k; rfl)

theorem allowedSignedSum_eq
    {V : Type} [AddCommGroup V] [Module F2 V]
    (K : Submodule F2 V) [Fintype K] [FiniteDimensional F2 K]
    (ell : K →ₗ[F2] F2) :
    allowedSignedSum K ell =
      if ell = 0 then (2 : ℤ) ^ Module.finrank F2 K else 0 := by
  unfold allowedSignedSum
  exact linearSignedSum_eq K ell

theorem allowedSignedSum_zero
    {V : Type} [AddCommGroup V] [Module F2 V]
    (K : Submodule F2 V) [Fintype K] [FiniteDimensional F2 K] :
    allowedSignedSum K 0 = (2 : ℤ) ^ Module.finrank F2 K := by
  rw [allowedSignedSum_eq]
  simp

theorem finalRootAllowed_zero_sum_node
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hcs : ∀ C ∈ cs, RTree.PositiveWeights C) :
    allowedSignedSum (independentAllowed (childSliceFactors n cs hcs)) 0 =
      (2 : ℤ) ^ YdimCandidate n (RTree.node a cs) := by
  rw [allowedSignedSum_zero]
  rw [finrank_independentAllowed]
  rw [factorDimProduct_childSliceFactors_node]

theorem finalRootAllowed_zero_sum_node_Ydim
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (hcs : ∀ C ∈ cs, RTree.PositiveWeights C) :
    allowedSignedSum (independentAllowed (childSliceFactors n cs hcs)) 0 =
      (2 : ℤ) ^ Ydim n (RTree.node a cs) hT := by
  rw [finalRootAllowed_zero_sum_node]
  rw [Ydim_eq_YdimCandidate]

end Imbalance
end TreeGraph
