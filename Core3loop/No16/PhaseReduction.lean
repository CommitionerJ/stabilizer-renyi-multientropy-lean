import No16.NormalForm

open scoped BigOperators

namespace No16

def eps (x y z : F) : F := 1 + x + y + z + x * y + x * z + y * z

def phi {n : ℕ} (s : Assignment n) (u1 u2 u3 u4 u5 : I n) : F :=
  eps (s.alpha u1 u2 u3 u4 u5) (s.beta u1 u2 u3 u4 u5) (s.delta u1 u2 u3 u4 u5) +
    eps (s.alpha u1 u2 u3 u4 u5) (s.gamma u1 u2 u3 u4 u5) (s.eta u1 u2 u3 u4 u5)

theorem phi_expanded {n : ℕ} (s : Assignment n) (u1 u2 u3 u4 u5 : I n) :
    phi s u1 u2 u3 u4 u5 =
      s.beta u1 u2 u3 u4 u5 + s.gamma u1 u2 u3 u4 u5
        + s.delta u1 u2 u3 u4 u5 + s.eta u1 u2 u3 u4 u5
        + s.alpha u1 u2 u3 u4 u5 *
            (s.beta u1 u2 u3 u4 u5 + s.gamma u1 u2 u3 u4 u5
              + s.delta u1 u2 u3 u4 u5 + s.eta u1 u2 u3 u4 u5)
        + s.beta u1 u2 u3 u4 u5 * s.delta u1 u2 u3 u4 u5
        + s.gamma u1 u2 u3 u4 u5 * s.eta u1 u2 u3 u4 u5 := by
  unfold phi eps
  ring_nf
  have h2 : (2 : F) = 0 := by decide
  simp [h2]

def bitSign (b : F) : ℤ := if b = 0 then 1 else -1

lemma bitSign_zero : bitSign (0 : F) = 1 := by
  simp [bitSign]

lemma bitSign_add (a b : F) : bitSign (a + b) = bitSign a * bitSign b := by
  fin_cases a <;> fin_cases b <;> decide

lemma bitSign_add_one (a : F) : bitSign (a + 1) = -bitSign a := by
  fin_cases a <;> decide

def phiQ {n : ℕ} (s : Assignment n) (u : Quint n) : F :=
  phi s u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2

noncomputable def phaseExponent {n : ℕ} [NeZero n] (s : Assignment n) : F :=
  ∑ u : Quint n, phiQ s u

noncomputable def Delta16Raw (n : ℕ) [NeZero n] : ℤ :=
  ∑ s : ValidAssignments n, bitSign (phaseExponent s.1)

noncomputable abbrev Delta16 (n : ℕ) [NeZero n] : ℤ := Delta16Raw n

lemma Delta16Raw_eq_sum_normalForm {n : ℕ} [NeZero n] :
    Delta16Raw n = ∑ nf : NFData n, bitSign (phaseExponent nf.toAssignment) := by
  unfold Delta16Raw
  simpa using
    (((validEquivNormalForm n).symm.sum_comp
      (fun s : ValidAssignments n => bitSign (phaseExponent s.1))).symm)

def linBC {n : ℕ} (B : BFun n) (C : CFun n) (u : Quint n) : F :=
  B u.1 (u.2.1 + u.2.2.1) u.2.2.2.1 u.2.2.2.2
    + B u.1 (u.2.1 + u.2.2.1 + 1) u.2.2.2.1 u.2.2.2.2
    + C u.1 u.2.1 u.2.2.1 (u.2.2.2.1 + u.2.2.2.2)
    + C u.1 u.2.1 u.2.2.1 (u.2.2.2.1 + u.2.2.2.2 + 1)

def pairBC {n : ℕ} (B : BFun n) (C : CFun n) (u : Quint n) : F :=
  B u.1 (u.2.1 + u.2.2.1) u.2.2.2.1 u.2.2.2.2 *
      C u.1 u.2.1 u.2.2.1 (u.2.2.2.1 + u.2.2.2.2)
    + B u.1 (u.2.1 + u.2.2.1 + 1) u.2.2.2.1 u.2.2.2.2 *
      C u.1 u.2.1 u.2.2.1 (u.2.2.2.1 + u.2.2.2.2 + 1)

noncomputable def kappa {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) : AFun n :=
  fun u2 u3 u4 u5 =>
    (∑ u1 : I n, (B u1 (u2 + u3) u4 u5 + B u1 (u2 + u3 + 1) u4 u5)) +
      (∑ u1 : I n, (C u1 u2 u3 (u4 + u5) + C u1 u2 u3 (u4 + u5 + 1)))

noncomputable def Qraw {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) : F :=
  ∑ u : Quint n,
    (linBC B C u + pairBC B C u)

noncomputable def quadApply {n : ℕ} (A : AFun n) (u : Quad n) : F := (aFunEquivQuad n A) u

noncomputable def alphaCoeff {n : ℕ} [NeZero n] (c A : AFun n) : F :=
  ∑ u : Quad n, quadApply A u * quadApply c u

noncomputable def alphaSigned {n : ℕ} [NeZero n] (c A : AFun n) : ℤ :=
  bitSign (alphaCoeff c A)

noncomputable def toggleAtA {n : ℕ} [NeZero n] (u0 : Quad n) (A : AFun n) : AFun n :=
  (aFunEquivQuad n).symm fun u => quadApply A u + if u = u0 then 1 else 0

noncomputable def toggleEquivA {n : ℕ} [NeZero n] (u0 : Quad n) : AFun n ≃ AFun n where
  toFun := toggleAtA u0
  invFun := toggleAtA u0
  left_inv A := by
    apply (aFunEquivQuad n).injective
    funext u
    by_cases h : u = u0
    · have h11 : (1 : F) + 1 = 0 := by decide
      simpa [toggleAtA, quadApply, h, add_assoc] using h11
    · simp [toggleAtA, quadApply, h]
  right_inv A := by
    apply (aFunEquivQuad n).injective
    funext u
    by_cases h : u = u0
    · have h11 : (1 : F) + 1 = 0 := by decide
      simpa [toggleAtA, quadApply, h, add_assoc] using h11
    · simp [toggleAtA, quadApply, h]

lemma F_ne_zero_eq_one (a : F) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (ha rfl)
  · rfl

lemma alphaCoeff_toggleAtA {n : ℕ} [NeZero n] (c A : AFun n) (u0 : Quad n) :
    alphaCoeff c (toggleAtA u0 A) = alphaCoeff c A + quadApply c u0 := by
  classical
  unfold alphaCoeff toggleAtA quadApply
  simp_rw [Equiv.apply_symm_apply]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hs : ∑ u : Quad n, (if u = u0 then 1 else 0) * (aFunEquivQuad n c) u = (aFunEquivQuad n c) u0 := by
    classical
    rw [Finset.sum_eq_single u0]
    · simp
    · intro u _ hu
      simp [hu]
    · simp
  simpa [quadApply] using hs

lemma alphaSigned_toggleAtA {n : ℕ} [NeZero n] (c A : AFun n) (u0 : Quad n)
    (hc : quadApply c u0 = 1) :
    alphaSigned c (toggleAtA u0 A) = -alphaSigned c A := by
  unfold alphaSigned
  rw [alphaCoeff_toggleAtA, hc, bitSign_add_one]

noncomputable def alphaSignedSum {n : ℕ} [NeZero n] (c : AFun n) : ℤ :=
  ∑ A : AFun n, alphaSigned c A

lemma alphaSignedSum_zero {n : ℕ} [NeZero n] :
    alphaSignedSum (n := n) 0 = (2 : ℤ) ^ (n ^ 4) := by
  unfold alphaSignedSum alphaSigned alphaCoeff quadApply
  have hcard : (((Fintype.card (AFun n)) : ℕ) : ℤ) = (2 : ℤ) ^ (n ^ 4) := by
    rw [card_AFun]
    norm_num
  calc
    (∑ A : AFun n, bitSign (∑ u : Quad n, (aFunEquivQuad n A) u * (aFunEquivQuad n (0 : AFun n)) u))
        = ∑ A : AFun n, (1 : ℤ) := by
            congr with A
            have hzero :
                (∑ u : Quad n, (aFunEquivQuad n A) u * (aFunEquivQuad n (0 : AFun n)) u) = 0 := by
              simp [aFunEquivQuad]
            rw [hzero, bitSign_zero]
    _ = Fintype.card (AFun n) := by simp
    _ = (2 : ℤ) ^ (n ^ 4) := hcard

theorem alphaSignedSum_formula {n : ℕ} [NeZero n] (c : AFun n) :
    alphaSignedSum c = if c = 0 then (2 : ℤ) ^ (n ^ 4) else 0 := by
  classical
  by_cases hc : c = 0
  · simp [hc, alphaSignedSum_zero]
  · have hne : ∃ u0 : Quad n, quadApply c u0 ≠ 0 := by
      by_contra hforall
      apply hc
      funext u1 u2 u3 u4
      have h0 := not_exists.mp hforall (u1, u2, u3, u4)
      exact by simpa [quadApply] using h0
    rcases hne with ⟨u0, hu0⟩
    have hcu0 : quadApply c u0 = 1 := F_ne_zero_eq_one _ hu0
    have hs : alphaSignedSum c = -alphaSignedSum c := by
      unfold alphaSignedSum
      calc
        ∑ A : AFun n, alphaSigned c A
            = ∑ A : AFun n, alphaSigned c (toggleAtA u0 A) := by
                simpa using
                  (((toggleEquivA (n := n) u0).sum_comp
                    (fun A : AFun n => alphaSigned c A)).symm)
        _ = ∑ A : AFun n, -alphaSigned c A := by
              congr with A
              exact alphaSigned_toggleAtA c A u0 hcu0
        _ = -∑ A : AFun n, alphaSigned c A := by
              simp
    have hz : alphaSignedSum c = 0 := by linarith
    simp [hc, hz]

lemma phi_toAssignment {n : ℕ} (nf : NFData n) (u1 u2 u3 u4 u5 : I n) :
    phi nf.toAssignment u1 u2 u3 u4 u5 =
      (nf.B u1 (u2 + u3) u4 u5 + nf.B u1 (u2 + u3 + 1) u4 u5
        + nf.C u1 u2 u3 (u4 + u5) + nf.C u1 u2 u3 (u4 + u5 + 1))
      + nf.A u2 u3 u4 u5 *
          (nf.B u1 (u2 + u3) u4 u5 + nf.B u1 (u2 + u3 + 1) u4 u5
            + nf.C u1 u2 u3 (u4 + u5) + nf.C u1 u2 u3 (u4 + u5 + 1))
      + nf.B u1 (u2 + u3) u4 u5 * nf.C u1 u2 u3 (u4 + u5)
      + nf.B u1 (u2 + u3 + 1) u4 u5 * nf.C u1 u2 u3 (u4 + u5 + 1) := by
  rw [phi_expanded]
  simp [NFData.toAssignment, add_assoc, add_left_comm, add_comm]

set_option maxHeartbeats 800000 in
lemma phiQ_toAssignment {n : ℕ} (nf : NFData n) (u : Quint n) :
    phiQ nf.toAssignment u =
      linBC nf.B nf.C u + quadApply nf.A u.2 * linBC nf.B nf.C u + pairBC nf.B nf.C u := by
  rcases u with ⟨u1, u2, u3, u4, u5⟩
  unfold phiQ
  rw [phi_expanded]
  simp [phiQ, linBC, pairBC, quadApply, NFData.toAssignment, add_assoc, add_left_comm, add_comm]
  ac_rfl

set_option maxHeartbeats 800000 in
lemma alphaCoeff_kappa_eq_sum {n : ℕ} [NeZero n] (nf : NFData n) :
    alphaCoeff (kappa nf.B nf.C) nf.A =
      ∑ u : Quint n, quadApply nf.A u.2 * linBC nf.B nf.C u := by
  unfold alphaCoeff quadApply kappa linBC
  conv_rhs => rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl ?_
  intro q hq
  rcases q with ⟨u2, u3, u4, u5⟩
  simp [aFunEquivQuad]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x hx
  ring

lemma phaseExponent_toAssignment_split {n : ℕ} [NeZero n] (nf : NFData n) :
    phaseExponent nf.toAssignment = alphaCoeff (kappa nf.B nf.C) nf.A + Qraw nf.B nf.C := by
  unfold phaseExponent Qraw
  rw [show (∑ u : Quint n, phiQ nf.toAssignment u)
      = ∑ u : Quint n,
          (linBC nf.B nf.C u + quadApply nf.A u.2 * linBC nf.B nf.C u + pairBC nf.B nf.C u) by
        refine Finset.sum_congr rfl ?_
        intro u hu
        exact phiQ_toAssignment nf u]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← alphaCoeff_kappa_eq_sum]
  calc
    ∑ x, linBC nf.B nf.C x + alphaCoeff (kappa nf.B nf.C) nf.A + ∑ x, pairBC nf.B nf.C x
        = alphaCoeff (kappa nf.B nf.C) nf.A + (∑ x, linBC nf.B nf.C x) + ∑ x, pairBC nf.B nf.C x := by
            ac_rfl
    _ = alphaCoeff (kappa nf.B nf.C) nf.A + ((∑ x, linBC nf.B nf.C x) + ∑ x, pairBC nf.B nf.C x) := by
          ac_rfl
    _ = alphaCoeff (kappa nf.B nf.C) nf.A + ∑ u, (linBC nf.B nf.C u + pairBC nf.B nf.C u) := by
          congr 1
          rw [← Finset.sum_add_distrib]

lemma bitSign_phaseExponent_toAssignment {n : ℕ} [NeZero n] (nf : NFData n) :
    bitSign (phaseExponent nf.toAssignment) =
      alphaSigned (kappa nf.B nf.C) nf.A * bitSign (Qraw nf.B nf.C) := by
  rw [phaseExponent_toAssignment_split]
  simp [alphaSigned, bitSign_add, mul_comm]

lemma sum_phase_over_A {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) :
    ∑ A : AFun n, bitSign (phaseExponent (NFData.toAssignment ⟨A, B, C⟩))
      = if kappa B C = 0 then (2 : ℤ) ^ (n ^ 4) * bitSign (Qraw B C) else 0 := by
  calc
    ∑ A : AFun n, bitSign (phaseExponent (NFData.toAssignment ⟨A, B, C⟩))
        = ∑ A : AFun n, alphaSigned (kappa B C) A * bitSign (Qraw B C) := by
            congr with A
            simpa using (bitSign_phaseExponent_toAssignment (nf := ⟨A, B, C⟩))
    _ = alphaSignedSum (kappa B C) * bitSign (Qraw B C) := by
          unfold alphaSignedSum
          rw [← Finset.sum_mul]
    _ = if kappa B C = 0 then (2 : ℤ) ^ (n ^ 4) * bitSign (Qraw B C) else 0 := by
          by_cases hk : kappa B C = 0 <;> simp [alphaSignedSum_formula, hk]

abbrev SurvivingBC (n : ℕ) [NeZero n] :=
  { p : BFun n × CFun n // kappa p.1 p.2 = 0 }

lemma Delta16Raw_eq_sum_indicator {n : ℕ} [NeZero n] :
    Delta16Raw n
      = ∑ q : BFun n × CFun n,
          if kappa q.1 q.2 = 0 then (2 : ℤ) ^ (n ^ 4) * bitSign (Qraw q.1 q.2) else 0 := by
  rw [Delta16Raw_eq_sum_normalForm]
  calc
    ∑ nf : NFData n, bitSign (phaseExponent nf.toAssignment)
        = ∑ p : AFun n × (BFun n × CFun n),
            bitSign (phaseExponent ((nfDataEquivProd n).symm p).toAssignment) := by
              simpa using
                (((nfDataEquivProd n).symm.sum_comp
                  (fun nf : NFData n => bitSign (phaseExponent nf.toAssignment))).symm)
    _ = ∑ q : BFun n × CFun n,
          ∑ A : AFun n, bitSign (phaseExponent ((nfDataEquivProd n).symm (A, q)).toAssignment) := by
            rw [Fintype.sum_prod_type_right]
    _ = ∑ q : BFun n × CFun n,
          if kappa q.1 q.2 = 0 then (2 : ℤ) ^ (n ^ 4) * bitSign (Qraw q.1 q.2) else 0 := by
            congr with q
            simpa [nfDataEquivProd] using sum_phase_over_A (n := n) q.1 q.2

lemma delta_after_A {n : ℕ} [NeZero n] :
    Delta16 n =
      (2 : ℤ) ^ (n ^ 4) * ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2) := by
  classical
  unfold Delta16
  rw [Delta16Raw_eq_sum_indicator]
  rw [← Finset.sum_filter]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_subtype_eq_sum_filter]
  simpa [SurvivingBC]

/-!
The next theorems in this file should express `phaseExponent` in the affine form
`alphaCoeff (kappa B C) A + Qraw B C` and then sum over all `A : AFun n`.
That part is the current next implementation target.
-/

end No16
