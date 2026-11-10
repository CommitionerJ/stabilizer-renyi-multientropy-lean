import Core3loop.NormalForm
import Core3loop.Reference.No13_abc_general

open scoped BigOperators

namespace Core3loop

noncomputable def coeffFromBC_abc {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) : AFieldABC b c n :=
  No13Migration.coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B C

noncomputable def coeffFromBCLinearMap_abc {a b c n : ℕ} [NeZero n] :
    (BFieldABC a c n × CFieldABC a b n) →ₗ[F] AFieldABC b c n :=
  No13Migration.coeffFromBCLinearMap_abc_real (a := a) (b := b) (c := c) (n := n)

def eps (x y z : F) : F :=
  1 + x + y + z + x * y + x * z + y * z

def localPhaseBitABC {a b c n : ℕ} (S : AssignmentABC a b c n) (u : Site a b c n) : F :=
  eps (S.alpha u) (S.beta u) (S.delta u) + eps (S.alpha u) (S.gamma u) (S.eta u)

theorem localPhase_expanded {a b c n : ℕ} (S : AssignmentABC a b c n) (u : Site a b c n) :
    localPhaseBitABC S u =
      S.beta u + S.gamma u + S.delta u + S.eta u
        + S.alpha u * (S.beta u + S.gamma u + S.delta u + S.eta u)
        + S.beta u * S.delta u + S.gamma u * S.eta u := by
  unfold localPhaseBitABC eps
  ring_nf
  have h2 : (2 : F) = 0 := by decide
  simp [h2]

noncomputable def phaseExponentABC {a b c n : ℕ} [NeZero n] (S : AssignmentABC a b c n) : F :=
  ∑ u : Site a b c n, localPhaseBitABC S u

noncomputable def W_abc_raw {a b c n : ℕ} [NeZero n] (S : AssignmentABC a b c n) : ℤ :=
  bitSign (phaseExponentABC S)

noncomputable def DeltaABC (a b c n : ℕ) [NeZero n] : ℤ :=
  ∑ s : ValidAssignmentsABC a b c n, W_abc_raw s.1

lemma W_abc_raw_eq_prod_bitSign {a b c n : ℕ} [NeZero n] (S : AssignmentABC a b c n) :
    W_abc_raw S = ∏ u : Site a b c n, bitSign (localPhaseBitABC S u) := by
  unfold W_abc_raw phaseExponentABC
  symm
  exact No13Migration.prod_bitSign_eq_bitSign_sum
    (Finset.univ : Finset (Site a b c n)) (localPhaseBitABC S)

lemma DeltaABC_eq_sum_normalForm {a b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    DeltaABC a b c n = ∑ nf : ABCNormalForm a b c n, W_abc_raw (toAssignmentABC nf) := by
  unfold DeltaABC
  simpa using
    (((validAssignmentsEquivNormalForm (a := a) (b := b) (c := c) (n := n) hb hc).symm.sum_comp
      (fun s : ValidAssignmentsABC a b c n => W_abc_raw s.1)).symm)

noncomputable def linBC_abc {a b c n : ℕ} [NeZero n] (B : BFieldABC a c n) (C : CFieldABC a b n)
    (u : Site a b c n) : F :=
  B (u.1, sumY u.2.1, u.2.2)
    + B (u.1, sumY u.2.1 + 1, u.2.2)
    + C (u.1, u.2.1, sumZ u.2.2)
    + C (u.1, u.2.1, sumZ u.2.2 + 1)

noncomputable def pairBC_abc {a b c n : ℕ} [NeZero n] (B : BFieldABC a c n) (C : CFieldABC a b n)
    (u : Site a b c n) : F :=
  B (u.1, sumY u.2.1, u.2.2) * C (u.1, u.2.1, sumZ u.2.2)
    + B (u.1, sumY u.2.1 + 1, u.2.2) * C (u.1, u.2.1, sumZ u.2.2 + 1)

noncomputable def QrawABC {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) : F :=
  ∑ u : Site a b c n, (linBC_abc B C u + pairBC_abc B C u)

noncomputable def QpairABC {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) : F :=
  ∑ u : Site a b c n, pairBC_abc B C u

abbrev SurvivingBC (a b c n : ℕ) [NeZero n] :=
  { bc : BFieldABC a c n × CFieldABC a b n // coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) bc.1 bc.2 = 0 }

set_option maxHeartbeats 4000000 in
-- Elaborating the substituted phase term over the normal-form assignment is expensive in this file.
lemma localPhaseBit_toAssignmentABC {a b c n : ℕ} [NeZero n]
    (nf : ABCNormalForm a b c n) (u : Site a b c n) :
    localPhaseBitABC (toAssignmentABC nf) u =
      linBC_abc nf.2.1 nf.2.2 u
        + nf.1 (u.2.1, u.2.2) * linBC_abc nf.2.1 nf.2.2 u
        + pairBC_abc nf.2.1 nf.2.2 u := by
  rw [localPhase_expanded]
  rw [show
      (toAssignmentABC nf).alpha u *
          ((toAssignmentABC nf).beta u + (toAssignmentABC nf).gamma u +
            (toAssignmentABC nf).delta u + (toAssignmentABC nf).eta u) =
        No13Migration.rawLocalPhaseBitABC (a := a) (b := b) (c := c) (n := n)
          (toAssignmentABC nf) u by
      rfl]
  rw [No13Migration.rawLocalPhaseBitABC_toRawAssignmentABC (a := a) (b := b) (c := c) (n := n) nf u]
  rcases u with ⟨x, y, z⟩
  rcases nf with ⟨A, B, C⟩
  simp [toAssignmentABC, No13Migration.toRawAssignmentABC, linBC_abc, pairBC_abc,
    add_assoc, add_left_comm, add_comm]

lemma alphaCoeffABC_coeffFromBC_eq_sum {a b c n : ℕ} [NeZero n] (nf : ABCNormalForm a b c n) :
    No13Migration.alphaCoeffABC (b := b) (c := c) (n := n)
        (coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2) nf.1
      =
        ∑ u : Site a b c n, nf.1 (u.2.1, u.2.2) * linBC_abc nf.2.1 nf.2.2 u := by
  rcases nf with ⟨A, B, C⟩
  unfold No13Migration.alphaCoeffABC coeffFromBC_abc No13Migration.coeffFromBC_abc_real
  calc
    ∑ yz : YCoord b n × ZCoord c n,
        A yz *
          ∑ x : XCoord a n,
            (B (x, sumY yz.1, yz.2) +
              B (x, sumY yz.1 + 1, yz.2) +
              C (x, yz.1, sumZ yz.2) +
              C (x, yz.1, sumZ yz.2 + 1))
      =
        ∑ yz : YCoord b n × ZCoord c n,
          ∑ x : XCoord a n,
            A yz *
              (B (x, sumY yz.1, yz.2) +
                B (x, sumY yz.1 + 1, yz.2) +
                C (x, yz.1, sumZ yz.2) +
                C (x, yz.1, sumZ yz.2 + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro yz hyz
          rw [Finset.mul_sum]
    _ =
        ∑ yz : YCoord b n × ZCoord c n,
          ∑ x : XCoord a n,
            A yz * linBC_abc B C (x, yz.1, yz.2) := by
          rfl
    _ = ∑ u : Site a b c n, A (u.2.1, u.2.2) * linBC_abc B C u := by
          simpa [Site] using
            (Fintype.sum_prod_type_right
              (f := fun u : XCoord a n × (YCoord b n × ZCoord c n) =>
                A (u.2.1, u.2.2) * linBC_abc B C u)).symm

lemma phaseExponentABC_toAssignment_split {a b c n : ℕ} [NeZero n]
    (nf : ABCNormalForm a b c n) :
    phaseExponentABC (toAssignmentABC nf) =
      No13Migration.alphaCoeffABC (b := b) (c := c) (n := n)
        (coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2) nf.1
      + QrawABC nf.2.1 nf.2.2 := by
  unfold phaseExponentABC QrawABC
  simp_rw [localPhaseBit_toAssignmentABC]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← alphaCoeffABC_coeffFromBC_eq_sum]
  calc
    ∑ x, linBC_abc nf.2.1 nf.2.2 x
        + No13Migration.alphaCoeffABC (b := b) (c := c) (n := n)
            (coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2) nf.1
        + ∑ x, pairBC_abc nf.2.1 nf.2.2 x
        =
      No13Migration.alphaCoeffABC (b := b) (c := c) (n := n)
          (coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2) nf.1
        + (∑ x, linBC_abc nf.2.1 nf.2.2 x) + ∑ x, pairBC_abc nf.2.1 nf.2.2 x := by
            ac_rfl
    _ =
      No13Migration.alphaCoeffABC (b := b) (c := c) (n := n)
          (coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2) nf.1
        + ((∑ x, linBC_abc nf.2.1 nf.2.2 x) + ∑ x, pairBC_abc nf.2.1 nf.2.2 x) := by
            ac_rfl
    _ =
      No13Migration.alphaCoeffABC (b := b) (c := c) (n := n)
          (coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2) nf.1
        + ∑ u : Site a b c n, (linBC_abc nf.2.1 nf.2.2 u + pairBC_abc nf.2.1 nf.2.2 u) := by
            congr 1
            rw [← Finset.sum_add_distrib]

lemma bitSign_phaseExponentABC_toAssignment {a b c n : ℕ} [NeZero n]
    (nf : ABCNormalForm a b c n) :
    bitSign (phaseExponentABC (toAssignmentABC nf)) =
      No13Migration.alphaSignedABC (b := b) (c := c) (n := n)
          (coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2) nf.1
        * bitSign (QrawABC nf.2.1 nf.2.2) := by
  rw [phaseExponentABC_toAssignment_split]
  simpa [No13Migration.alphaSignedABC] using
    No13Migration.bitSign_add
      (No13Migration.alphaCoeffABC (b := b) (c := c) (n := n)
        (coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) nf.2.1 nf.2.2) nf.1)
      (QrawABC nf.2.1 nf.2.2)

lemma sum_phase_over_A {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) :
    ∑ A : AFieldABC b c n, W_abc_raw (toAssignmentABC (A, B, C))
      =
        if coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) B C = 0 then
          (2 : ℤ) ^ (n ^ (b + c)) * bitSign (QrawABC B C)
        else
          0 := by
  calc
    ∑ A : AFieldABC b c n, W_abc_raw (toAssignmentABC (A, B, C))
        = ∑ A : AFieldABC b c n,
            No13Migration.alphaSignedABC (b := b) (c := c) (n := n)
                (coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) B C) A
              * bitSign (QrawABC B C) := by
                congr with A
                unfold W_abc_raw
                simpa using bitSign_phaseExponentABC_toAssignment (a := a) (b := b) (c := c)
                  (n := n) (nf := (A, B, C))
    _ =
      No13Migration.alphaSignedSumABC (b := b) (c := c) (n := n)
          (coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) B C)
        * bitSign (QrawABC B C) := by
          unfold No13Migration.alphaSignedSumABC
          rw [← Finset.sum_mul]
    _ =
      if coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) B C = 0 then
        (2 : ℤ) ^ (n ^ (b + c)) * bitSign (QrawABC B C)
      else
        0 := by
          by_cases hk : coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) B C = 0 <;>
            simp [No13Migration.alphaSignedSumABC_formula, hk]

lemma DeltaABC_eq_sum_indicator {a b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    DeltaABC a b c n
      =
        ∑ q : BFieldABC a c n × CFieldABC a b n,
          if coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) q.1 q.2 = 0 then
            (2 : ℤ) ^ (n ^ (b + c)) * bitSign (QrawABC q.1 q.2)
          else
            0 := by
  rw [DeltaABC_eq_sum_normalForm (a := a) (b := b) (c := c) (n := n) hb hc]
  calc
    ∑ nf : ABCNormalForm a b c n, W_abc_raw (toAssignmentABC nf)
        =
          ∑ p : AFieldABC b c n × (BFieldABC a c n × CFieldABC a b n),
            W_abc_raw (toAssignmentABC p) := by
              rfl
    _ =
      ∑ q : BFieldABC a c n × CFieldABC a b n,
        ∑ A : AFieldABC b c n, W_abc_raw (toAssignmentABC (A, q.1, q.2)) := by
          rw [Fintype.sum_prod_type_right]
    _ =
      ∑ q : BFieldABC a c n × CFieldABC a b n,
        if coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) q.1 q.2 = 0 then
          (2 : ℤ) ^ (n ^ (b + c)) * bitSign (QrawABC q.1 q.2)
        else
          0 := by
            congr with q
            simpa using sum_phase_over_A (a := a) (b := b) (c := c) (n := n) q.1 q.2

theorem DeltaABC_after_A_raw {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c)) * ∑ bc : SurvivingBC a b c n, bitSign (QrawABC bc.1.1 bc.1.2) := by
  classical
  rw [DeltaABC_eq_sum_indicator (a := a) (b := b) (c := c) (n := n) hb hc]
  rw [← Finset.sum_filter]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_subtype_eq_sum_filter]
  simp [SurvivingBC]

lemma sum_linBC_eq_zero_of_surviving {a b c n : ℕ} [NeZero n]
    {B : BFieldABC a c n} {C : CFieldABC a b n}
    (hk : coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) B C = 0) :
    (∑ u : Site a b c n, linBC_abc B C u) = 0 := by
  calc
    (∑ u : Site a b c n, linBC_abc B C u)
        = ∑ yz : YCoord b n × ZCoord c n,
            coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) B C yz := by
              rw [Fintype.sum_prod_type_right]
              refine Finset.sum_congr rfl ?_
              intro yz hyz
              rcases yz with ⟨y, z⟩
              rfl
    _ = ∑ yz : YCoord b n × ZCoord c n, (0 : F) := by simpa [hk]
    _ = 0 := by simp

theorem QrawABC_eq_QpairABC_of_surviving {a b c n : ℕ} [NeZero n]
    {B : BFieldABC a c n} {C : CFieldABC a b n}
    (hk : coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) B C = 0) :
    QrawABC B C = QpairABC B C := by
  unfold QrawABC QpairABC
  rw [Finset.sum_add_distrib, sum_linBC_eq_zero_of_surviving hk, zero_add]

theorem DeltaABC_after_A {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c)) * ∑ bc : SurvivingBC a b c n, bitSign (QpairABC bc.1.1 bc.1.2) := by
  classical
  rw [DeltaABC_after_A_raw (a := a) (b := b) (c := c) (n := n) ha hb hc]
  congr 2
  funext bc
  simp [QrawABC_eq_QpairABC_of_surviving (a := a) (b := b) (c := c) (n := n) bc.2]

theorem card_survivingBC_closed {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (SurvivingBC a b c n) =
      2 ^ (n ^ (a + c) + n ^ (a + b) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b +
        (n - 1) ^ 2) := by
  simpa [SurvivingBC, coeffFromBC_abc] using
    No13Migration.card_survivingBC_abc_honest_closed (a := a) (b := b) (c := c) (n := n)
      ha hb hc

lemma abs_bitSign_eq_one (x : F) : |bitSign x| = 1 := by
  fin_cases x <;> decide

theorem DeltaABC_abs_le_closed {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    |DeltaABC a b c n| ≤
      (2 : ℤ) ^ (n ^ (b + c) +
        (n ^ (a + c) + n ^ (a + b) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b +
          (n - 1) ^ 2)) := by
  classical
  rw [DeltaABC_after_A (a := a) (b := b) (c := c) (n := n) ha hb hc]
  let S : ℤ := ∑ bc : SurvivingBC a b c n, bitSign (QpairABC bc.1.1 bc.1.2)
  have hpow_nonneg : 0 ≤ (2 : ℤ) ^ (n ^ (b + c)) := by
    exact pow_nonneg (by decide : 0 ≤ (2 : ℤ)) _
  have hsum :
      |S| ≤ (Fintype.card (SurvivingBC a b c n) : ℤ) := by
    calc
      |S| ≤ ∑ bc : SurvivingBC a b c n, |bitSign (QpairABC bc.1.1 bc.1.2)| := by
        simpa [S] using
          (Finset.abs_sum_le_sum_abs
            (s := (Finset.univ : Finset (SurvivingBC a b c n)))
            (f := fun bc : SurvivingBC a b c n => bitSign (QpairABC bc.1.1 bc.1.2)))
      _ = ∑ _bc : SurvivingBC a b c n, (1 : ℤ) := by
            refine Finset.sum_congr rfl ?_
            intro bc hbc
            exact abs_bitSign_eq_one (QpairABC bc.1.1 bc.1.2)
      _ = (Fintype.card (SurvivingBC a b c n) : ℤ) := by simp
  have hmul :
      (2 : ℤ) ^ (n ^ (b + c)) * |S| ≤
        (2 : ℤ) ^ (n ^ (b + c)) * (Fintype.card (SurvivingBC a b c n) : ℤ) := by
    exact mul_le_mul_of_nonneg_left hsum hpow_nonneg
  have hcardZ :
      (Fintype.card (SurvivingBC a b c n) : ℤ) =
        (2 : ℤ) ^ (n ^ (a + c) + n ^ (a + b) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b +
          (n - 1) ^ 2) := by
    rw [card_survivingBC_closed (a := a) (b := b) (c := c) (n := n) ha hb hc]
    simpa using
      (Nat.cast_pow (R := ℤ) 2
        (n ^ (a + c) + n ^ (a + b) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b +
          (n - 1) ^ 2))
  calc
    |(2 : ℤ) ^ (n ^ (b + c)) * S| = (2 : ℤ) ^ (n ^ (b + c)) * |S| := by
      rw [abs_mul, abs_of_nonneg hpow_nonneg]
    _ ≤ (2 : ℤ) ^ (n ^ (b + c)) * (Fintype.card (SurvivingBC a b c n) : ℤ) := hmul
    _ = (2 : ℤ) ^ (n ^ (b + c)) *
          (2 : ℤ) ^ (n ^ (a + c) + n ^ (a + b) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b +
            (n - 1) ^ 2) := by
            rw [hcardZ]
    _ = (2 : ℤ) ^ (n ^ (b + c) +
          (n ^ (a + c) + n ^ (a + b) - n ^ (c + 1) - n ^ (b + 1) + n ^ c + n ^ b +
            (n - 1) ^ 2)) := by
            rw [← pow_add]

end Core3loop
