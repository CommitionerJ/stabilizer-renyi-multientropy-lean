import No16.Basic

namespace No16

abbrev SiteFun (n : ℕ) := I n → I n → I n → I n → I n → F

structure Assignment (n : ℕ) where
  alpha : SiteFun n
  beta  : SiteFun n
  gamma : SiteFun n
  delta : SiteFun n
  eta   : SiteFun n

structure Valid {n : ℕ} (s : Assignment n) : Prop where
  alpha_e1 : ∀ u1 u2 u3 u4 u5, s.alpha (u1 + 1) u2 u3 u4 u5 = s.alpha u1 u2 u3 u4 u5
  gamma_beta_e2 : ∀ u1 u2 u3 u4 u5, s.gamma u1 u2 u3 u4 u5 = s.beta u1 (u2 + 1) u3 u4 u5
  gamma_beta_e3 : ∀ u1 u2 u3 u4 u5, s.gamma u1 u2 u3 u4 u5 = s.beta u1 u2 (u3 + 1) u4 u5
  eta_delta_e4 : ∀ u1 u2 u3 u4 u5, s.eta u1 u2 u3 u4 u5 = s.delta u1 u2 u3 (u4 + 1) u5
  eta_delta_e5 : ∀ u1 u2 u3 u4 u5, s.eta u1 u2 u3 u4 u5 = s.delta u1 u2 u3 u4 (u5 + 1)

abbrev ValidAssignments (n : ℕ) := { s : Assignment n // Valid s }

structure NFData (n : ℕ) where
  A : AFun n
  B : BFun n
  C : CFun n

@[ext] theorem Assignment.ext {n : ℕ} {s t : Assignment n}
    (hα : s.alpha = t.alpha) (hβ : s.beta = t.beta) (hγ : s.gamma = t.gamma)
    (hδ : s.delta = t.delta) (hη : s.eta = t.eta) : s = t := by
  cases s
  cases t
  simp_all

@[ext] theorem NFData.ext {n : ℕ} {s t : NFData n}
    (hA : s.A = t.A) (hB : s.B = t.B) (hC : s.C = t.C) : s = t := by
  cases s
  cases t
  simp_all

noncomputable def siteFunEquivQuint (n : ℕ) : SiteFun n ≃ (Quint n → F) where
  toFun f := fun | ⟨u1, u2, u3, u4, u5⟩ => f u1 u2 u3 u4 u5
  invFun f := fun u1 u2 u3 u4 u5 => f (u1, u2, u3, u4, u5)
  left_inv f := by
    funext u1 u2 u3 u4 u5
    rfl
  right_inv f := by
    funext u
    rcases u with ⟨u1, u2, u3, u4, u5⟩
    rfl

noncomputable instance siteFunFintype (n : ℕ) [NeZero n] : Fintype (SiteFun n) := by
  exact Fintype.ofEquiv (Quint n → F) (siteFunEquivQuint n).symm

noncomputable instance assignmentProdFintype (n : ℕ) [NeZero n] :
    Fintype (SiteFun n × (SiteFun n × (SiteFun n × (SiteFun n × SiteFun n)))) := by
  infer_instance

noncomputable instance nfProdFintype (n : ℕ) [NeZero n] :
    Fintype (AFun n × (BFun n × CFun n)) := by
  let _ : Fintype (AFun n) := inferInstance
  let _ : Fintype (BFun n) := inferInstance
  let _ : Fintype (CFun n) := inferInstance
  infer_instance

noncomputable def assignmentEquivProd (n : ℕ) :
    Assignment n ≃
      (SiteFun n × (SiteFun n × (SiteFun n × (SiteFun n × SiteFun n)))) where
  toFun s := ⟨s.alpha, ⟨s.beta, s.gamma, s.delta, s.eta⟩⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def nfDataEquivProd (n : ℕ) : NFData n ≃ (AFun n × (BFun n × CFun n)) where
  toFun nf := ⟨nf.A, ⟨nf.B, nf.C⟩⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance assignmentFintype (n : ℕ) [NeZero n] : Fintype (Assignment n) :=
  Fintype.ofEquiv _ (assignmentEquivProd n).symm

noncomputable instance nfDataFintype (n : ℕ) [NeZero n] : Fintype (NFData n) :=
  Fintype.ofEquiv _ (nfDataEquivProd n).symm

noncomputable instance validAssignmentsFintype (n : ℕ) [NeZero n] :
    Fintype (ValidAssignments n) := by
  classical
  infer_instance

def NFData.toAssignment {n : ℕ} (nf : NFData n) : Assignment n where
  alpha _u1 u2 u3 u4 u5 := nf.A u2 u3 u4 u5
  beta  u1 u2 u3 u4 u5 := nf.B u1 (u2 + u3) u4 u5
  gamma u1 u2 u3 u4 u5 := nf.B u1 (u2 + u3 + 1) u4 u5
  delta u1 u2 u3 u4 u5 := nf.C u1 u2 u3 (u4 + u5)
  eta   u1 u2 u3 u4 u5 := nf.C u1 u2 u3 (u4 + u5 + 1)

lemma valid_toAssignment {n : ℕ} (nf : NFData n) : Valid nf.toAssignment := by
  constructor
  · intro u1 u2 u3 u4 u5
    simp [NFData.toAssignment]
  · intro u1 u2 u3 u4 u5
    simp [NFData.toAssignment, add_assoc, add_left_comm, add_comm]
  · intro u1 u2 u3 u4 u5
    simp [NFData.toAssignment, add_assoc]
  · intro u1 u2 u3 u4 u5
    simp [NFData.toAssignment, add_assoc, add_left_comm, add_comm]
  · intro u1 u2 u3 u4 u5
    simp [NFData.toAssignment, add_assoc]

noncomputable def Assignment.toNF {n : ℕ} (s : Assignment n) (_hs : Valid s) : NFData n where
  A u2 u3 u4 u5 := s.alpha 0 u2 u3 u4 u5
  B u1 t u4 u5 := s.beta u1 0 t u4 u5
  C u1 u2 u3 r := s.delta u1 u2 u3 0 r

lemma alpha_depends_only_tail {n : ℕ} [NeZero n] (s : Assignment n) (hs : Valid s)
    (u1 u2 u3 u4 u5 : I n) :
    s.alpha u1 u2 u3 u4 u5 = s.alpha 0 u2 u3 u4 u5 := by
  let g : I n → F := fun t => s.alpha (u1 + t) u2 u3 u4 u5
  have hg : ∀ t, g (t + 1) = g t := by
    intro t
    simpa [g, add_assoc] using hs.alpha_e1 (u1 + t) u2 u3 u4 u5
  have hconst := zmod_step_const (n := n) g hg (-u1)
  dsimp [g] at hconst
  calc
    s.alpha u1 u2 u3 u4 u5 = g 0 := by simp [g]
    _ = g (-u1) := hconst.symm
    _ = s.alpha 0 u2 u3 u4 u5 := by simp [g]

lemma beta_depends_only_sum23 {n : ℕ} [NeZero n] (s : Assignment n) (hs : Valid s)
    (u1 u2 u3 u4 u5 : I n) :
    s.beta u1 u2 u3 u4 u5 = s.beta u1 0 (u2 + u3) u4 u5 := by
  let g : I n → F := fun t => s.beta u1 (u2 + t) (u3 - t) u4 u5
  have hg : ∀ t, g (t + 1) = g t := by
    intro t
    calc
      g (t + 1) = s.gamma u1 (u2 + t) (u3 - (t + 1)) u4 u5 := by
        rw [hs.gamma_beta_e2 u1 (u2 + t) (u3 - (t + 1)) u4 u5]
        simp [g, add_assoc, add_comm, sub_eq_add_neg]
      _ = s.beta u1 (u2 + t) ((u3 - (t + 1)) + 1) u4 u5 := by
        rw [hs.gamma_beta_e3 u1 (u2 + t) (u3 - (t + 1)) u4 u5]
      _ = g t := by
        simp [g, add_left_comm, add_comm, sub_eq_add_neg]
  have hconst := zmod_step_const (n := n) g hg (-u2)
  dsimp [g] at hconst
  calc
    s.beta u1 u2 u3 u4 u5 = g 0 := by simp [g]
    _ = g (-u2) := hconst.symm
    _ = s.beta u1 0 (u2 + u3) u4 u5 := by
      simp [g, add_comm, sub_eq_add_neg]

lemma delta_depends_only_sum45 {n : ℕ} [NeZero n] (s : Assignment n) (hs : Valid s)
    (u1 u2 u3 u4 u5 : I n) :
    s.delta u1 u2 u3 u4 u5 = s.delta u1 u2 u3 0 (u4 + u5) := by
  let g : I n → F := fun t => s.delta u1 u2 u3 (u4 + t) (u5 - t)
  have hg : ∀ t, g (t + 1) = g t := by
    intro t
    calc
      g (t + 1) = s.eta u1 u2 u3 (u4 + t) (u5 - (t + 1)) := by
        rw [hs.eta_delta_e4 u1 u2 u3 (u4 + t) (u5 - (t + 1))]
        simp [g, add_assoc, add_comm, sub_eq_add_neg]
      _ = s.delta u1 u2 u3 (u4 + t) ((u5 - (t + 1)) + 1) := by
        rw [hs.eta_delta_e5 u1 u2 u3 (u4 + t) (u5 - (t + 1))]
      _ = g t := by
        simp [g, add_left_comm, add_comm, sub_eq_add_neg]
  have hconst := zmod_step_const (n := n) g hg (-u4)
  dsimp [g] at hconst
  calc
    s.delta u1 u2 u3 u4 u5 = g 0 := by simp [g]
    _ = g (-u4) := hconst.symm
    _ = s.delta u1 u2 u3 0 (u4 + u5) := by
      simp [g, add_comm, sub_eq_add_neg]

lemma toNF_toAssignment {n : ℕ} (nf : NFData n) :
    (nf.toAssignment).toNF (valid_toAssignment nf) = nf := by
  apply NFData.ext
  · funext u1 u2 u3 u4
    rfl
  · funext u1 u2 u3 u4
    simp [Assignment.toNF, NFData.toAssignment]
  · funext u1 u2 u3 u4
    simp [Assignment.toNF, NFData.toAssignment]

lemma toAssignment_toNF {n : ℕ} [NeZero n] (s : Assignment n) (hs : Valid s) :
    (s.toNF hs).toAssignment = s := by
  apply Assignment.ext
  · funext u1 u2 u3 u4 u5
    simpa [Assignment.toNF, NFData.toAssignment] using
      (alpha_depends_only_tail s hs u1 u2 u3 u4 u5).symm
  · funext u1 u2 u3 u4 u5
    simpa [Assignment.toNF, NFData.toAssignment] using
      (beta_depends_only_sum23 s hs u1 u2 u3 u4 u5).symm
  · funext u1 u2 u3 u4 u5
    calc
      (s.toNF hs).toAssignment.gamma u1 u2 u3 u4 u5
          = s.beta u1 0 (u2 + (u3 + 1)) u4 u5 := by
              simp [Assignment.toNF, NFData.toAssignment, add_assoc]
      _ = s.beta u1 (u2 + 1) u3 u4 u5 := by
              simpa [add_assoc, add_left_comm, add_comm] using
                (beta_depends_only_sum23 s hs u1 (u2 + 1) u3 u4 u5).symm
      _ = s.gamma u1 u2 u3 u4 u5 := (hs.gamma_beta_e2 u1 u2 u3 u4 u5).symm
  · funext u1 u2 u3 u4 u5
    simpa [Assignment.toNF, NFData.toAssignment] using
      (delta_depends_only_sum45 s hs u1 u2 u3 u4 u5).symm
  · funext u1 u2 u3 u4 u5
    calc
      (s.toNF hs).toAssignment.eta u1 u2 u3 u4 u5
          = s.delta u1 u2 u3 0 (u4 + (u5 + 1)) := by
              simp [Assignment.toNF, NFData.toAssignment, add_assoc]
      _ = s.delta u1 u2 u3 (u4 + 1) u5 := by
              simpa [add_assoc, add_left_comm, add_comm] using
                (delta_depends_only_sum45 s hs u1 u2 u3 (u4 + 1) u5).symm
      _ = s.eta u1 u2 u3 u4 u5 := (hs.eta_delta_e4 u1 u2 u3 u4 u5).symm

noncomputable def validEquivNormalForm (n : ℕ) [NeZero n] :
    ValidAssignments n ≃ NFData n where
  toFun s := s.1.toNF s.2
  invFun nf := ⟨nf.toAssignment, valid_toAssignment nf⟩
  left_inv s := by
    apply Subtype.ext
    exact toAssignment_toNF s.1 s.2
  right_inv nf := toNF_toAssignment nf

noncomputable def valid_equiv_normalForm (n : ℕ) [NeZero n] :
    ValidAssignments n ≃ NFData n :=
  validEquivNormalForm n

theorem card_valid_assignments {n : ℕ} [NeZero n] :
    Fintype.card (ValidAssignments n) = 2 ^ (3 * n ^ 4) := by
  rw [Fintype.card_congr (valid_equiv_normalForm n)]
  rw [Fintype.card_congr (nfDataEquivProd n)]
  rw [Fintype.card_prod, Fintype.card_prod]
  rw [card_AFun]
  calc
    2 ^ (n ^ 4) * (2 ^ (n ^ 4) * 2 ^ (n ^ 4))
        = 2 ^ (n ^ 4) * 2 ^ (n ^ 4 + n ^ 4) := by rw [← pow_add]
    _ = 2 ^ (n ^ 4 + (n ^ 4 + n ^ 4)) := by rw [← pow_add]
    _ = 2 ^ (3 * n ^ 4) := by ring_nf

end No16
