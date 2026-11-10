import No16.OddCase
import No16.EvenCase

namespace No16

theorem N_valid_formula {n : ℕ} [NeZero n] :
    Fintype.card (ValidAssignments n) = 2 ^ (3 * n ^ 4) :=
  card_valid_assignments

theorem Delta16_odd_factorized_of_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    ∃ m : ℕ,
      n = 2 * m + 1 ∧
        Delta16 n =
          (∑ bc : OddVisibleData n, oddVisibleSign bc) *
            (2 : ℤ) ^ (n ^ 4 + ordinaryPairExponent n * m) := by
  rcases hn with ⟨m, rfl⟩
  refine ⟨m, rfl, ?_⟩
  simpa using Delta16_odd_factorized m

theorem Delta16_odd_hspace_factorized_of_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    ∃ m : ℕ,
      n = 2 * m + 1 ∧
        Delta16 n =
          ((2 : ℤ) ^ (n ^ 2 + n ^ 2) * ∑ h : HSpace (n := n), oddHSign h) *
            (2 : ℤ) ^ (n ^ 4 + ordinaryPairExponent n * m) := by
  rcases hn with ⟨m, rfl⟩
  refine ⟨m, rfl, ?_⟩
  simpa using Delta16_odd_hspace_factorized m

theorem Delta16_odd_closed_of_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    ∃ m : ℕ,
      n = 2 * m + 1 ∧
        Delta16 n =
          (2 : ℤ) ^ ((3 * n ^ 2 + 1 - 2 * n) + (n ^ 4 + ordinaryPairExponent n * m)) := by
  rcases hn with ⟨m, rfl⟩
  refine ⟨m, rfl, ?_⟩
  rw [Delta16_odd_factorized (m := m)]
  rw [sum_oddVisible_eq_closed_form_of_odd (n := 2 * m + 1) (by exact ⟨m, by omega⟩)]
  rw [← pow_add]

theorem Delta16_odd_closed_unsimplified_of_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    Delta16 n =
      (2 : ℤ) ^
        ((3 * n ^ 2 + 1 - 2 * n) +
          (n ^ 4 + ordinaryPairExponent n * ((n - 1) / 2))) := by
  rcases hn with ⟨m, rfl⟩
  rw [Delta16_odd_factorized (m := m)]
  rw [sum_oddVisible_eq_closed_form_of_odd (n := 2 * m + 1) (by exact ⟨m, by omega⟩)]
  rw [← pow_add]
  congr
  simp

theorem Delta16_even_factorized_of_even {n : ℕ} [NeZero n] (hn : Even n) :
    Delta16 n =
      (2 : ℤ) ^ (n ^ 4) *
        (((2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n)) *
          (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1))))) :=
  Delta16_even_special_factorized_closed_tail hn

theorem Delta16_even_le_closed_form_of_even {n : ℕ} [NeZero n] (hn : Even n) :
    Delta16 n ≤
      (2 : ℤ) ^ (n ^ 4) *
        ((2 : ℤ) ^ (2 * n ^ 3 + (3 * n ^ 2 + 3 - 4 * n)) *
          (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1))))) :=
  Delta16_even_special_le_closed_form hn

theorem Delta16_even_closed_unsimplified_of_even {n : ℕ} [NeZero n] (hn : Even n) :
    Delta16 n =
      (2 : ℤ) ^
        (n ^ 4 + ((n ^ 3 + n ^ 3) + (3 * n ^ 2 + 3 - 4 * n)) +
          (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1))))) := by
  rw [Delta16_even_factorized_of_even hn]
  rw [fintypeCard_evenVisibleKernelData_compact (n := n) hn]
  calc
    (2 : ℤ) ^ (n ^ 4) *
        (((2 : ℤ) ^ (n ^ 3 + n ^ 3) * (2 : ℤ) ^ (3 * n ^ 2 + 3 - 4 * n)) *
          (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1)))))
        =
      (2 : ℤ) ^ (n ^ 4) *
        ((2 : ℤ) ^ ((n ^ 3 + n ^ 3) + (3 * n ^ 2 + 3 - 4 * n)) *
          (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1))))) := by
            rw [← pow_add]
    _ =
      (2 : ℤ) ^ (n ^ 4) *
        (2 : ℤ) ^
          (((n ^ 3 + n ^ 3) + (3 * n ^ 2 + 3 - 4 * n)) +
            (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1))))) := by
              rw [← pow_add]
    _ = (2 : ℤ) ^
        (n ^ 4 + ((n ^ 3 + n ^ 3) + (3 * n ^ 2 + 3 - 4 * n)) +
          (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1))))) := by
            simpa [add_assoc] using
              (show (2 : ℤ) ^ (n ^ 4) *
                  (2 : ℤ) ^
                    (((n ^ 3 + n ^ 3) + (3 * n ^ 2 + 3 - 4 * n)) +
                      (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1)))))
                    =
                (2 : ℤ) ^
                  (n ^ 4 +
                    (((n ^ 3 + n ^ 3) + (3 * n ^ 2 + 3 - 4 * n)) +
                      (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1))))) ) by
                    rw [← pow_add])

def oddDeltaExponent (n : ℕ) : ℕ :=
  3 * n ^ 4 + 5 * n ^ 2 + 1 - (3 * n ^ 3 + 3 * n)

def evenDeltaExponent (n : ℕ) : ℕ :=
  3 * n ^ 4 + 6 * n ^ 2 + 3 - (3 * n ^ 3 + 6 * n)

theorem Delta16_odd_closed_standard_of_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    Delta16 n = (2 : ℤ) ^ oddDeltaExponent n := by
  rw [Delta16_odd_closed_unsimplified_of_odd hn]
  congr 1
  rcases hn with ⟨m, rfl⟩
  have hdiv : ((2 * m + 1 - 1) / 2) = m := by omega
  rw [hdiv]
  have hsq : (2 * m + 1) ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by ring_nf
  have hcube : (2 * m + 1) ^ 3 = 8 * m ^ 3 + 12 * m ^ 2 + 6 * m + 1 := by ring_nf
  have hquart : (2 * m + 1) ^ 4 = 16 * m ^ 4 + 32 * m ^ 3 + 24 * m ^ 2 + 8 * m + 1 := by ring_nf
  have hsquare :
      3 * (2 * m + 1) ^ 2 + 1 - 2 * (2 * m + 1) =
        12 * m ^ 2 + 8 * m + 2 := by
    rw [hsq]
    ring_nf
    have h :
        4 + m * 12 + m ^ 2 * 12 =
          (2 + m * 8 + m ^ 2 * 12) + (2 + m * 4) := by
      ring_nf
    rw [h, Nat.add_sub_cancel_right]
  have hcubeodd :
      (2 * m + 1) ^ 3 - (2 * m + 1) * ((2 * m + 1) - 1) =
        8 * m ^ 3 + 8 * m ^ 2 + 4 * m + 1 := by
    have hpred : (2 * m + 1) - 1 = 2 * m := by omega
    rw [hpred, hcube]
    ring_nf
    have h :
        1 + m * 6 + m ^ 2 * 12 + m ^ 3 * 8 =
          (1 + m * 4 + m ^ 2 * 8 + m ^ 3 * 8) + (m * 2 + m ^ 2 * 4) := by
      ring_nf
    rw [h, Nat.add_sub_cancel_right]
  have hord :
      ordinaryPairExponent (2 * m + 1) =
        32 * m ^ 3 + 40 * m ^ 2 + 20 * m + 4 := by
    rw [ordinaryPairExponent, hcubeodd, hcube]
    ring_nf
  have hoddexp :
      oddDeltaExponent (2 * m + 1) =
        48 * m ^ 4 + 72 * m ^ 3 + 56 * m ^ 2 + 20 * m + 3 := by
    unfold oddDeltaExponent
    rw [hquart, hcube, hsq]
    ring_nf
    have h :
        9 + m * 44 + m ^ 2 * 92 + m ^ 3 * 96 + m ^ 4 * 48 =
          (3 + m * 20 + m ^ 2 * 56 + m ^ 3 * 72 + m ^ 4 * 48) +
            (6 + m * 24 + m ^ 2 * 36 + m ^ 3 * 24) := by
      ring_nf
    rw [h, Nat.add_sub_cancel_right]
  rw [hsquare, hquart, hord, hoddexp]
  ring_nf

theorem Delta16_even_closed_standard_of_even {n : ℕ} [NeZero n] (hn : Even n) :
    Delta16 n = (2 : ℤ) ^ evenDeltaExponent n := by
  rw [Delta16_even_closed_unsimplified_of_even hn]
  congr 1
  rcases hn with ⟨m, rfl⟩
  have hm : m ≠ 0 := by
    intro hm0
    subst hm0
    exact (NeZero.ne (n := 0)) rfl
  rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨k, rfl⟩
  have htwo : k.succ + k.succ = 2 * k + 2 := by omega
  have hpred : 2 * k + 2 - 1 = 2 * k + 1 := by omega
  have hsub3 : 2 * k + 2 - 2 = 2 * k := by omega
  have hsq : (2 * k + 2) ^ 2 = 4 * k ^ 2 + 8 * k + 4 := by ring_nf
  have hcube : (2 * k + 2) ^ 3 = 8 * k ^ 3 + 24 * k ^ 2 + 24 * k + 8 := by ring_nf
  have hquart : (2 * k + 2) ^ 4 = 16 * k ^ 4 + 64 * k ^ 3 + 96 * k ^ 2 + 64 * k + 16 := by ring_nf
  have hsub1 :
      3 * (2 * k + 2) ^ 2 + 3 - 4 * (2 * k + 2) =
        12 * k ^ 2 + 16 * k + 7 := by
    rw [hsq]
    ring_nf
    have h :
        15 + k * 24 + k ^ 2 * 12 =
          (7 + k * 16 + k ^ 2 * 12) + (8 + k * 8) := by
      ring_nf
    rw [h, Nat.add_sub_cancel_right]
  have hsub2 :
      (2 * k + 2) ^ 3 - (2 * k + 2) * (2 * k + 2 - 1) =
        8 * k ^ 3 + 20 * k ^ 2 + 18 * k + 6 := by
    rw [hcube, hpred]
    ring_nf
    have h :
        8 + k * 24 + k ^ 2 * 24 + k ^ 3 * 8 =
          (6 + k * 18 + k ^ 2 * 20 + k ^ 3 * 8) + (2 + k * 6 + k ^ 2 * 4) := by
      ring_nf
    rw [h, Nat.add_sub_cancel_right]
  have hord :
      ordinaryPairExponent (2 * k + 2) =
        32 * k ^ 3 + 88 * k ^ 2 + 84 * k + 28 := by
    rw [ordinaryPairExponent, hsub2, hcube]
    ring_nf
  have hevenexp :
      evenDeltaExponent (2 * k + 2) =
        48 * k ^ 4 + 168 * k ^ 3 + 240 * k ^ 2 + 156 * k + 39 := by
    unfold evenDeltaExponent
    rw [hquart, hcube, hsq]
    ring_nf
    have h :
        75 + k * 240 + k ^ 2 * 312 + k ^ 3 * 192 + k ^ 4 * 48 =
          (39 + k * 156 + k ^ 2 * 240 + k ^ 3 * 168 + k ^ 4 * 48) +
            (36 + k * 84 + k ^ 2 * 72 + k ^ 3 * 24) := by
      ring_nf
    rw [h, Nat.add_sub_cancel_right]
  rw [htwo, hsub1, hsub2, hsub3, hquart, hcube, hevenexp]
  ring_nf

theorem Delta16_factorized_by_parity {n : ℕ} [NeZero n] :
    (∃ m : ℕ,
      n = 2 * m + 1 ∧
        Delta16 n =
          (∑ bc : OddVisibleData n, oddVisibleSign bc) *
            (2 : ℤ) ^ (n ^ 4 + ordinaryPairExponent n * m)) ∨
      (Even n ∧
        Delta16 n =
          (2 : ℤ) ^ (n ^ 4) *
            (((2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n)) *
              (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1)))))) := by
  rcases Nat.even_or_odd n with hn | hn
  · right
    exact ⟨hn, Delta16_even_factorized_of_even hn⟩
  · left
    exact Delta16_odd_factorized_of_odd hn

theorem Delta16_closed_unsimplified_by_parity {n : ℕ} [NeZero n] :
    (Odd n ∧
      Delta16 n =
        (2 : ℤ) ^
          ((3 * n ^ 2 + 1 - 2 * n) +
            (n ^ 4 + ordinaryPairExponent n * ((n - 1) / 2)))) ∨
      (Even n ∧
        Delta16 n =
          (2 : ℤ) ^
            (n ^ 4 + ((n ^ 3 + n ^ 3) + (3 * n ^ 2 + 3 - 4 * n)) +
              (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1)))))) := by
  rcases Nat.even_or_odd n with hn | hn
  · right
    exact ⟨hn, Delta16_even_closed_unsimplified_of_even hn⟩
  · left
    exact ⟨hn, Delta16_odd_closed_unsimplified_of_odd hn⟩

theorem Delta16_closed_by_parity {n : ℕ} [NeZero n] :
    Delta16 n =
      if Odd n then
        (2 : ℤ) ^ oddDeltaExponent n
      else
        (2 : ℤ) ^ evenDeltaExponent n := by
  by_cases hn : Odd n
  · simp [hn, Delta16_odd_closed_standard_of_odd hn]
  · have hne : Even n := by
      rcases Nat.even_or_odd n with he | ho
      · exact he
      · exact False.elim (hn ho)
    simp [hn, Delta16_even_closed_standard_of_even hne]

end No16
