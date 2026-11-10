import Core3loop.ProfileEvenSurviving
import Core3loop.EvenCase

open scoped BigOperators

namespace Core3loop

noncomputable def addRightScalarCCoefEquiv {b n : ℕ} [NeZero n]
    (ccoef : ScalarCCoef b n) : ScalarCCoef b n ≃ ScalarCCoef b n where
  toFun := fun c₂ => c₂ + ccoef
  invFun := fun c₂ => c₂ + ccoef
  left_inv := by
    intro c₂
    funext y r
    calc
      (c₂ + ccoef + ccoef) y r = c₂ y r + (ccoef y r + ccoef y r) := by
        simp [Pi.add_apply, add_assoc, add_left_comm, add_comm]
      _ = c₂ y r := by
        simp [F_add_self]
  right_inv := by
    intro c₂
    funext y r
    calc
      (c₂ + ccoef + ccoef) y r = c₂ y r + (ccoef y r + ccoef y r) := by
        simp [Pi.add_apply, add_assoc, add_left_comm, add_comm]
      _ = c₂ y r := by
        simp [F_add_self]

lemma sum_evenVisibleSignABC_eq_sum_evenVisibleWeight {b c n : ℕ} [NeZero n] :
    ∑ d : EvenVisibleDataABC b c n, evenVisibleSignABC (b := b) (c := c) (n := n) d =
      ∑ bc : ScalarVisibleCompat b c n,
        ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
          bitSign
            (qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
              qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) := by
  classical
  calc
    ∑ d : EvenVisibleDataABC b c n, evenVisibleSignABC (b := b) (c := c) (n := n) d
      =
        ∑ x : ((ScalarVisibleCompat b c n × ScalarBCoef c n) × ScalarCCoef b n),
          evenVisibleSignABC (b := b) (c := c) (n := n)
            ((evenVisibleDataABCEquivTuple (b := b) (c := c) (n := n)).symm x) := by
              simpa using
                (Equiv.sum_comp (evenVisibleDataABCEquivTuple (b := b) (c := c) (n := n))
                  (fun x : ((ScalarVisibleCompat b c n × ScalarBCoef c n) × ScalarCCoef b n) =>
                    evenVisibleSignABC (b := b) (c := c) (n := n)
                      ((evenVisibleDataABCEquivTuple (b := b) (c := c) (n := n)).symm x)))
    _ =
        ∑ p : ScalarVisibleCompat b c n × ScalarBCoef c n, ∑ c₂ : ScalarCCoef b n,
          bitSign
            (qScalar (b := b) (c := c) (n := n) p.1.bcoef p.1.ccoef +
              qScalar (b := b) (c := c) (n := n) p.1.bcoef c₂ +
              qScalar (b := b) (c := c) (n := n) p.2 p.1.ccoef) := by
              simpa [evenVisibleDataABCEquivTuple, evenVisibleSignABC, qEvenABC] using
                (Fintype.sum_prod_type'
                  (f := fun p : ScalarVisibleCompat b c n × ScalarBCoef c n =>
                    fun c₂ : ScalarCCoef b n =>
                      bitSign
                        (qScalar (b := b) (c := c) (n := n) p.1.bcoef p.1.ccoef +
                          qScalar (b := b) (c := c) (n := n) p.1.bcoef c₂ +
                          qScalar (b := b) (c := c) (n := n) p.2 p.1.ccoef)))
    _ =
        ∑ bc : ScalarVisibleCompat b c n, ∑ b₂ : ScalarBCoef c n, ∑ c₂ : ScalarCCoef b n,
          bitSign
            (qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef +
              qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
              qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) := by
              simpa using
                (Fintype.sum_prod_type'
                  (f := fun bc : ScalarVisibleCompat b c n =>
                    fun b₂ : ScalarBCoef c n =>
                      ∑ c₂ : ScalarCCoef b n,
                        bitSign
                          (qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef +
                            qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
                            qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef)))
    _ =
        ∑ bc : ScalarVisibleCompat b c n, ∑ b₂ : ScalarBCoef c n, ∑ c₂ : ScalarCCoef b n,
          bitSign
            (qScalar (b := b) (c := c) (n := n) bc.bcoef (bc.ccoef + c₂) +
              qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) := by
              refine Finset.sum_congr rfl ?_
              intro bc hbc
              refine Finset.sum_congr rfl ?_
              intro b₂ hb₂
              refine Finset.sum_congr rfl ?_
              intro c₂ hc₂
              rw [qScalar_add_right (b := b) (c := c) (n := n) bc.bcoef bc.ccoef c₂]
    _ =
        ∑ bc : ScalarVisibleCompat b c n, ∑ b₂ : ScalarBCoef c n, ∑ c₂ : ScalarCCoef b n,
          bitSign
            (qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
              qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) := by
              refine Finset.sum_congr rfl ?_
              intro bc hbc
              refine Finset.sum_congr rfl ?_
              intro b₂ hb₂
              simpa [add_comm, add_left_comm, add_assoc] using
                (Equiv.sum_comp (addRightScalarCCoefEquiv (b := b) (n := n) bc.ccoef)
                  (fun c₂ : ScalarCCoef b n =>
                    bitSign
                      (qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
                        qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef)))
    _ =
        ∑ bc : ScalarVisibleCompat b c n,
          ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
            bitSign
              (qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
                qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) := by
              refine Finset.sum_congr rfl ?_
              intro bc hbc
              rw [Finset.sum_comm]

theorem sum_evenVisibleSignABC_eq_closed_form_all_ge_two {b c n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    ∑ d : EvenVisibleDataABC b c n, evenVisibleSignABC (b := b) (c := c) (n := n) d =
      (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3) := by
  rw [sum_evenVisibleSignABC_eq_sum_evenVisibleWeight (b := b) (c := c) (n := n)]
  exact sum_evenVisible_eq_kernel_visible_closed_form_all_ge_two
    (b := b) (c := c) (n := n) hn hb2 hc2

theorem sum_evenVisibleSignABC_eq_closed_form_min_eq_one {b c n : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c) (hdeg : b = 1 ∨ c = 1) :
    ∑ d : EvenVisibleDataABC b c n, evenVisibleSignABC (b := b) (c := c) (n := n) d =
      (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1) := by
  rw [sum_evenVisibleSignABC_eq_sum_evenVisibleWeight (b := b) (c := c) (n := n)]
  exact sum_evenVisible_eq_kernel_visible_closed_form_min_eq_one
    (b := b) (c := c) (n := n) hn hb hc hdeg

lemma sum_evenDataSignABC_eq_visible_mul_tail {a b c n : ℕ} [NeZero n] :
    ∑ d : EvenSurvivingDataABC a b c n, evenDataSignABC (a := a) (b := b) (c := c) (n := n) d =
      (∑ vis : EvenVisibleDataABC b c n, evenVisibleSignABC (b := b) (c := c) (n := n) vis) *
        ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
          evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
  classical
  calc
    ∑ d : EvenSurvivingDataABC a b c n, evenDataSignABC (a := a) (b := b) (c := c) (n := n) d
      =
        ∑ x : ((EvenVisibleDataABC b c n × EvenTailBModelABC a c n) × EvenTailCModelABC a b n),
          evenDataSignABC (a := a) (b := b) (c := c) (n := n)
            ((evenSurvivingDataABCEquivTuple (a := a) (b := b) (c := c) (n := n)).symm x) := by
              simpa using
                (Equiv.sum_comp (evenSurvivingDataABCEquivTuple (a := a) (b := b) (c := c) (n := n))
                  (fun x : ((EvenVisibleDataABC b c n × EvenTailBModelABC a c n) ×
                      EvenTailCModelABC a b n) =>
                    evenDataSignABC (a := a) (b := b) (c := c) (n := n)
                      ((evenSurvivingDataABCEquivTuple
                        (a := a) (b := b) (c := c) (n := n)).symm x)))
    _ =
        ∑ x : ((EvenVisibleDataABC b c n × EvenTailBModelABC a c n) × EvenTailCModelABC a b n),
          evenVisibleSignABC (b := b) (c := c) (n := n) x.1.1 *
            evenTailSignABC (a := a) (b := b) (c := c) (n := n) x.1.2 x.2 := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rcases x with ⟨⟨vis, XB⟩, YC⟩
              simpa [evenSurvivingDataABCEquivTuple] using
                evenDataSignABC_eq_mul (a := a) (b := b) (c := c) (n := n)
                  ⟨vis, XB, YC⟩
    _ =
        ∑ p : EvenVisibleDataABC b c n × EvenTailBModelABC a c n,
          ∑ YC : EvenTailCModelABC a b n,
            evenVisibleSignABC (b := b) (c := c) (n := n) p.1 *
              evenTailSignABC (a := a) (b := b) (c := c) (n := n) p.2 YC := by
              simpa using
                (Fintype.sum_prod_type'
                  (f := fun p : EvenVisibleDataABC b c n × EvenTailBModelABC a c n =>
                    fun YC : EvenTailCModelABC a b n =>
                      evenVisibleSignABC (b := b) (c := c) (n := n) p.1 *
                        evenTailSignABC (a := a) (b := b) (c := c) (n := n) p.2 YC))
    _ =
        ∑ vis : EvenVisibleDataABC b c n, ∑ XB : EvenTailBModelABC a c n,
          ∑ YC : EvenTailCModelABC a b n,
            evenVisibleSignABC (b := b) (c := c) (n := n) vis *
              evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
              simpa using
                (Fintype.sum_prod_type'
                  (f := fun vis : EvenVisibleDataABC b c n =>
                    fun XB : EvenTailBModelABC a c n =>
                      ∑ YC : EvenTailCModelABC a b n,
                        evenVisibleSignABC (b := b) (c := c) (n := n) vis *
                          evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC))
    _ =
        ∑ vis : EvenVisibleDataABC b c n,
          evenVisibleSignABC (b := b) (c := c) (n := n) vis *
            ∑ XB : EvenTailBModelABC a c n, ∑ YC : EvenTailCModelABC a b n,
              evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
              refine Finset.sum_congr rfl ?_
              intro vis hvis
              calc
                ∑ XB : EvenTailBModelABC a c n, ∑ YC : EvenTailCModelABC a b n,
                    evenVisibleSignABC (b := b) (c := c) (n := n) vis *
                      evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC
                  =
                    ∑ XB : EvenTailBModelABC a c n,
                      evenVisibleSignABC (b := b) (c := c) (n := n) vis *
                        ∑ YC : EvenTailCModelABC a b n,
                          evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
                            refine Finset.sum_congr rfl ?_
                            intro XB hXB
                            rw [← Finset.mul_sum]
                _ =
                    evenVisibleSignABC (b := b) (c := c) (n := n) vis *
                      ∑ XB : EvenTailBModelABC a c n, ∑ YC : EvenTailCModelABC a b n,
                        evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
                          rw [← Finset.mul_sum]
    _ =
        (∑ vis : EvenVisibleDataABC b c n, evenVisibleSignABC (b := b) (c := c) (n := n) vis) *
          ∑ XB : EvenTailBModelABC a c n, ∑ YC : EvenTailCModelABC a b n,
            evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
              rw [Finset.sum_mul]
    _ =
        (∑ vis : EvenVisibleDataABC b c n, evenVisibleSignABC (b := b) (c := c) (n := n) vis) *
          ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
            evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
              congr 1
              rw [Finset.sum_comm]

theorem DeltaABC_eq_evenVisibleFactor_mul_tailSum_of_even_all_ge_two
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3) *
        ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
          evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
  rw [DeltaABC_after_A (a := a) (b := b) (c := c) (n := n) ha hb hc]
  rw [sum_survivingBC_eq_sum_evenDataABC_of_even (a := a) (b := b) (c := c) (n := n) hn ha2]
  rw [sum_evenDataSignABC_eq_visible_mul_tail (a := a) (b := b) (c := c) (n := n)]
  rw [sum_evenVisibleSignABC_eq_closed_form_all_ge_two (b := b) (c := c) (n := n) hn hb2 hc2]
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
  have hn2 : 2 ≤ n := by
    obtain ⟨m, hm⟩ := hn
    have hmpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm0
      apply NeZero.ne n
      simp [hm, hm0]
    omega
  have hbpow : n ^ 2 ≤ n ^ b := by
    exact Nat.pow_le_pow_right hn1 hb2
  have hcpow : n ^ 2 ≤ n ^ c := by
    exact Nat.pow_le_pow_right hn1 hc2
  have hquad : 4 * n ≤ n ^ 2 + n ^ 2 := by
    have h2n_sq : 2 * n ≤ n ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right n hn2
    calc
      4 * n = 2 * n + 2 * n := by omega
      _ ≤ n ^ 2 + n ^ 2 := add_le_add h2n_sq h2n_sq
  have htwo : n ^ 2 + n ^ 2 ≤ n ^ b + n ^ c := by
    simpa [two_mul] using (show 2 * n ^ 2 ≤ n ^ b + n ^ c by omega)
  have hbound0 : 4 * n ≤ n ^ b + n ^ c + n ^ 2 := by
    exact le_trans (le_trans hquad htwo) (Nat.le_add_right _ _)
  have hbound :
      4 * n ≤ n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 := by
    exact le_trans hbound0 (by omega)
  have hexp :
      n ^ (b + c) + (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3) =
        n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3 := by
    calc
      n ^ (b + c) + (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3)
          = n ^ (b + c) +
              ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n) + 3) := by
                rfl
      _ = (n ^ (b + c) +
            (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n)) + 3 := by
              ac_rfl
      _ = ((n ^ (b + c) +
            (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2)) - 4 * n) + 3 := by
              rw [← Nat.add_sub_assoc hbound]
      _ = n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3 := by
              ac_rfl
  calc
    (2 : ℤ) ^ (n ^ (b + c)) *
        ((2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3) *
          ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
            evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC)
      =
        (((2 : ℤ) ^ (n ^ (b + c))) *
          (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3)) *
          ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
            evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
              ac_rfl
    _ =
        (2 : ℤ) ^ (n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3) *
          ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
            evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
              rw [← pow_add, hexp]

theorem DeltaABC_eq_evenVisibleFactor_mul_tailSum_of_even_min_eq_one
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : Even n) (ha2 : 2 ≤ a) (hdeg : b = 1 ∨ c = 1) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1) *
        ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
          evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
  rw [DeltaABC_after_A (a := a) (b := b) (c := c) (n := n) ha hb hc]
  rw [sum_survivingBC_eq_sum_evenDataABC_of_even (a := a) (b := b) (c := c) (n := n) hn ha2]
  rw [sum_evenDataSignABC_eq_visible_mul_tail (a := a) (b := b) (c := c) (n := n)]
  rw [sum_evenVisibleSignABC_eq_closed_form_min_eq_one
    (b := b) (c := c) (n := n) hn hb hc hdeg]
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hnpos
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt hb
  have hB_ge_n : n ≤ n ^ b := by
    simpa [pow_one] using Nat.pow_le_pow_right hn1 hb1
  have hbound :
      n ≤ n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c := by
    exact le_trans hB_ge_n (by omega)
  have hexp :
      n ^ (b + c) + (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1) =
        n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1 := by
    omega
  calc
    (2 : ℤ) ^ (n ^ (b + c)) *
        ((2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1) *
          ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
            evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC)
      =
        (((2 : ℤ) ^ (n ^ (b + c))) *
          (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1)) *
          ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
            evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
              ac_rfl
    _ =
        (2 : ℤ) ^ (n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1) *
          ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
            evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC := by
              rw [← pow_add, hexp]

end Core3loop
