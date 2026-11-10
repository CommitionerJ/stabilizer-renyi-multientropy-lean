import Core3loop.Exponents
import Core3loop.ProfileEvenKernel

namespace Core3loop

theorem evenSpecialDeltaExponent_eq_visible_plus_tail_of_even
    {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    evenSpecialDeltaExponent a b c n =
      n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3 +
        ordinaryPairExponentABC b c n * evenTailPairCountABC a n := by
  rw [← evenTailClosedExponent_eq_ordinaryPairExponent_mul_pairCount
    (a := a) (b := b) (c := c) (n := n) hn ha2 hb]
  rcases exists_profileCard_eq_two_mul_add_two_of_even (a := a) (n := n) hn ha2 with ⟨m, hm⟩
  let A := ProfileCard a n
  let B := n ^ b
  let C := n ^ c
  let P := n ^ (b + c)
  let NB := n ^ (b + 1)
  let NC := n ^ (c + 1)
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hnpos
  have hn2 : 2 ≤ n := by
    rcases hn with ⟨k, hk⟩
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hk0
      apply NeZero.ne n
      simp [hk, hk0]
    omega
  have ha1 : 1 ≤ a - 1 := by omega
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt hb
  have hc1 : 1 ≤ c := Nat.succ_le_of_lt hc
  have hA_ge_n : n ≤ A := by
    dsimp [A, ProfileCard]
    simpa [pow_one] using Nat.pow_le_pow_right hn1 ha1
  have hB_ge_n : n ≤ B := by
    dsimp [B]
    simpa [pow_one] using Nat.pow_le_pow_right hn1 hb1
  have hC_ge_n : n ≤ C := by
    dsimp [C]
    simpa [pow_one] using Nat.pow_le_pow_right hn1 hc1
  have hNB : NB = (n - 1) * B + B := by
    dsimp [NB, B]
    have hpred : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hnpos
    calc
      n ^ (b + 1) = n ^ b * n := by rw [Nat.pow_add, pow_one]
      _ = n * n ^ b := by rw [Nat.mul_comm]
      _ = (n - 1 + 1) * n ^ b := by
            nth_rewrite 1 [← hpred]
            rfl
      _ = (n - 1) * n ^ b + n ^ b := by rw [Nat.add_mul, one_mul]
  have hNC : NC = (n - 1) * C + C := by
    dsimp [NC, C]
    have hpred : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hnpos
    calc
      n ^ (c + 1) = n ^ c * n := by rw [Nat.pow_add, pow_one]
      _ = n * n ^ c := by rw [Nat.mul_comm]
      _ = (n - 1 + 1) * n ^ c := by
            nth_rewrite 1 [← hpred]
            rfl
      _ = (n - 1) * n ^ c + n ^ c := by rw [Nat.add_mul, one_mul]
  have hpowa : n ^ a = A * n := by
    calc
      n ^ a = n ^ ((a - 1) + 1) := by
                congr
                omega
      _ = n ^ (a - 1) * n := by rw [Nat.pow_add, pow_one]
      _ = A * n := by simp [A, ProfileCard]
  have hpowab : n ^ (a + b) = A * NB := by
    dsimp [A, NB, ProfileCard]
    have hsplit : a + b = (a - 1) + (b + 1) := by omega
    rw [hsplit, Nat.pow_add]
  have hpowac : n ^ (a + c) = A * NC := by
    dsimp [A, NC, ProfileCard]
    have hsplit : a + c = (a - 1) + (c + 1) := by omega
    rw [hsplit, Nat.pow_add]
  have hnm1_le_B : n - 1 ≤ B := le_trans (Nat.sub_le _ _) hB_ge_n
  have hNB_ge : n * (n - 1) ≤ NB := by
    calc
      n * (n - 1) ≤ n * B := Nat.mul_le_mul_left _ hnm1_le_B
      _ = NB := by
            dsimp [NB, B]
            rw [Nat.pow_add, pow_one, Nat.mul_comm]
  have hsquare_ge_two_n : 2 * n ≤ n ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right n hn2
  have hvisible_base_ge : 4 * n ≤ B + C + n ^ 2 := by
    omega
  have hcore_even :
      NB + NC =
        (n - 1) * (B + C - n + 3) + (B + C + n ^ 2 - 4 * n + 3) := by
    by_cases hn_eq : n = 2
    · subst n
      rw [hNB, hNC]
      omega
    · have hn3 : 3 ≤ n := by omega
      by_cases hn_eq3 : n = 3
      · subst n
        rw [hNB, hNC]
        omega
      · have hn4 : 4 ≤ n := by omega
        have hsplitBC :
            (n - 1) * B + (n - 1) * C =
              (n - 1) * (B + C - n + 3) + (n - 1) * (n - 3) := by
          calc
            (n - 1) * B + (n - 1) * C = (n - 1) * (B + C) := by
              rw [Nat.mul_add]
            _ = (n - 1) * ((B + C - n + 3) + (n - 3)) := by
              have hsplit : B + C = (B + C - n + 3) + (n - 3) := by
                omega
              exact congrArg (fun t : ℕ => (n - 1) * t) hsplit
            _ = (n - 1) * (B + C - n + 3) + (n - 1) * (n - 3) := by
              rw [Nat.mul_add]
        have hquad :
            (n - 1) * (n - 3) + (B + C) = B + C + n ^ 2 - 4 * n + 3 := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn4
          have h1 : 4 + k - 1 = 3 + k := by omega
          have h3 : 4 + k - 3 = 1 + k := by omega
          rw [h1, h3]
          rw [show (4 + k) ^ 2 = 16 + 8 * k + k ^ 2 by ring_nf]
          ring_nf
          omega
        calc
          NB + NC = ((n - 1) * B + B) + ((n - 1) * C + C) := by
            rw [hNB, hNC]
          _ = ((n - 1) * B + (n - 1) * C) + (B + C) := by
            ac_rfl
          _ = ((n - 1) * (B + C - n + 3) + (n - 1) * (n - 3)) + (B + C) := by
            rw [hsplitBC]
          _ = (n - 1) * (B + C - n + 3) + ((n - 1) * (n - 3) + (B + C)) := by
            ac_rfl
          _ = (n - 1) * (B + C - n + 3) + (B + C + n ^ 2 - 4 * n + 3) := by
            rw [hquad]
  have hcore_two :
      2 * NB + 2 * NC =
        (n - 1) * (B + C - n + 3) + (NB + NC + B + C + n ^ 2 - 4 * n + 3) := by
    have hvisible_assoc :
        NB + NC + (B + C + n ^ 2 - 4 * n + 3) =
          NB + NC + B + C + n ^ 2 - 4 * n + 3 := by
      omega
    calc
      2 * NB + 2 * NC = (NB + NC) + (NB + NC) := by
        omega
      _ = (NB + NC) +
          ((n - 1) * (B + C - n + 3) + (B + C + n ^ 2 - 4 * n + 3)) := by
        rw [hcore_even]
      _ = (n - 1) * (B + C - n + 3) +
          (NB + NC + (B + C + n ^ 2 - 4 * n + 3)) := by
        ac_rfl
      _ = (n - 1) * (B + C - n + 3) +
          (NB + NC + B + C + n ^ 2 - 4 * n + 3) := by
        rw [hvisible_assoc]
  have hpair_add :
      (2 * m) * NB + (2 * m) * NC =
        (2 * m) * (n * (n - 1)) + ((2 * m) * NC + (2 * m) * (NB - n * (n - 1))) := by
    have hsplit : NB = n * (n - 1) + (NB - n * (n - 1)) := by
      omega
    calc
      (2 * m) * NB + (2 * m) * NC =
          (2 * m) * (n * (n - 1) + (NB - n * (n - 1))) + (2 * m) * NC := by
            exact congrArg (fun t : ℕ => (2 * m) * t + (2 * m) * NC) hsplit
      _ = ((2 * m) * (n * (n - 1)) + (2 * m) * (NB - n * (n - 1))) +
          (2 * m) * NC := by
            rw [Nat.mul_add]
      _ = (2 * m) * (n * (n - 1)) + ((2 * m) * NC + (2 * m) * (NB - n * (n - 1))) := by
            ac_rfl
  have hinside :
      (2 * m + 2) * n + B + C - 3 * n + 3 =
        2 * m * n + (B + C - n + 3) := by
    rw [Nat.add_mul]
    omega
  have hsub_add :
      (n - 1) * ((2 * m + 2) * n + B + C - 3 * n + 3) =
        (2 * m) * (n * (n - 1)) + (n - 1) * (B + C - n + 3) := by
    rw [hinside, Nat.mul_add]
    have hmul : (n - 1) * (2 * m * n) = (2 * m) * (n * (n - 1)) := by
      ac_rfl
    rw [hmul]
  have hfront_add :
      (2 * m + 2) * NB + (2 * m + 2) * NC + P =
        (n - 1) * ((2 * m + 2) * n + B + C - 3 * n + 3) +
          (P + NB + NC + B + C + n ^ 2 - 4 * n + 3 +
            ((2 * m) * NC + (2 * m) * (NB - n * (n - 1)))) := by
    have hmoveP :
        (NB + NC + B + C + n ^ 2 - 4 * n + 3) + P =
          P + NB + NC + B + C + n ^ 2 - 4 * n + 3 := by
      have hle : 4 * n ≤ NB + NC + B + C + n ^ 2 := by
        omega
      omega
    calc
      (2 * m + 2) * NB + (2 * m + 2) * NC + P =
          ((2 * m) * NB + 2 * NB) + ((2 * m) * NC + 2 * NC) + P := by
            rw [Nat.add_mul, Nat.add_mul]
      _ = ((2 * m) * NB + (2 * m) * NC) + (2 * NB + 2 * NC) + P := by
            ac_rfl
      _ = ((2 * m) * (n * (n - 1)) + ((2 * m) * NC + (2 * m) * (NB - n * (n - 1)))) +
          ((n - 1) * (B + C - n + 3) + (NB + NC + B + C + n ^ 2 - 4 * n + 3)) + P := by
            rw [hpair_add, hcore_two]
      _ = (n - 1) * ((2 * m + 2) * n + B + C - 3 * n + 3) +
          (P + NB + NC + B + C + n ^ 2 - 4 * n + 3 +
            ((2 * m) * NC + (2 * m) * (NB - n * (n - 1)))) := by
            rw [hsub_add]
            rw [← hmoveP]
            ac_rfl
  have hfront :
      (2 * m + 2) * NB + (2 * m + 2) * NC + P -
          (n - 1) * ((2 * m + 2) * n + B + C - 3 * n + 3) =
        P + NB + NC + B + C + n ^ 2 - 4 * n + 3 +
          ((2 * m) * NC + (2 * m) * (NB - n * (n - 1))) := by
    have hle :
        (n - 1) * ((2 * m + 2) * n + B + C - 3 * n + 3) ≤
          (2 * m + 2) * NB + (2 * m + 2) * NC + P := by
      exact Nat.le.intro hfront_add.symm
    have hfront_add' :
        (2 * m + 2) * NB + (2 * m + 2) * NC + P =
          (P + NB + NC + B + C + n ^ 2 - 4 * n + 3 +
            ((2 * m) * NC + (2 * m) * (NB - n * (n - 1)))) +
          (n - 1) * ((2 * m + 2) * n + B + C - 3 * n + 3) := by
      rw [hfront_add]
      ac_rfl
    exact (Nat.sub_eq_iff_eq_add hle).2 hfront_add'
  have hA : A = 2 * m + 2 := by simpa [A] using hm
  have hdim : n ^ (a - 1) - 2 = 2 * m := by
    have hA' : n ^ (a - 1) = 2 * m + 2 := by
      simpa [A, ProfileCard] using hm
    omega
  unfold evenSpecialDeltaExponent
  rw [show n ^ (b + c) = P by rfl,
    show n ^ (b + 1) = NB by rfl,
    show n ^ (c + 1) = NC by rfl,
    show n ^ b = B by rfl,
    show n ^ c = C by rfl,
    hpowab, hpowac, hpowa, hA, hdim]
  change
      (2 * m + 2) * NB + (2 * m + 2) * NC + P -
          (n - 1) * ((2 * m + 2) * n + B + C - 3 * n + 3) =
        P + NB + NC + B + C + n ^ 2 - 4 * n + 3 +
          ((2 * m) * NC + (2 * m) * (NB - n * (n - 1)))
  exact hfront

theorem genericDeltaExponent_eq_even_min_visible_plus_tail_of_even
    {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    genericDeltaExponent a b c n =
      n ^ (b + c) + n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1 +
        ordinaryPairExponentABC b c n * evenTailPairCountABC a n := by
  rcases exists_profileCard_eq_two_mul_add_two_of_even (a := a) (n := n) hn ha2 with ⟨m, hm⟩
  let A := ProfileCard a n
  let B := n ^ b
  let C := n ^ c
  let P := n ^ (b + c)
  let NB := n ^ (b + 1)
  let NC := n ^ (c + 1)
  have hpowa : n ^ a = A * n := by
    calc
      n ^ a = n ^ ((a - 1) + 1) := by
        congr
        omega
      _ = n ^ (a - 1) * n := by rw [Nat.pow_add, pow_one]
      _ = A * n := by rfl
  have hpowab : n ^ (a + b) = A * NB := by
    dsimp [A, NB, ProfileCard]
    have hsplit : a + b = (a - 1) + (b + 1) := by omega
    rw [hsplit, Nat.pow_add]
  have hpowac : n ^ (a + c) = A * NC := by
    dsimp [A, NC, ProfileCard]
    have hsplit : a + c = (a - 1) + (c + 1) := by omega
    rw [hsplit, Nat.pow_add]
  have hA : A = 2 * m + 2 := by simpa [A] using hm
  have hcount : evenTailPairCountABC a n = m := by
    exact evenTailPairCountABC_eq_of_even_witness (a := a) (n := n) hm
  have hNB : NB = n * B := by
    dsimp [NB, B]
    rw [Nat.pow_add, pow_one, Nat.mul_comm]
  have hNC : NC = n * C := by
    dsimp [NC, C]
    rw [Nat.pow_add, pow_one, Nat.mul_comm]
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt hb
  have hB_ge_n : n ≤ B := by
    dsimp [B]
    simpa [pow_one] using Nat.pow_le_pow_right hnpos hb1
  have htail_nonneg : n * (n - 1) ≤ NB + NC := by
    have hpredB : n - 1 ≤ B := le_trans (Nat.sub_le _ _) hB_ge_n
    calc
      n * (n - 1) ≤ n * B := Nat.mul_le_mul_left n hpredB
      _ = NB := by rw [hNB]
      _ ≤ NB + NC := Nat.le_add_right _ _
  unfold genericDeltaExponent ordinaryPairExponentABC
  rw [show n ^ (b + c) = P by rfl,
    show n ^ (b + 1) = NB by rfl,
    show n ^ (c + 1) = NC by rfl,
    show n ^ b = B by rfl,
    show n ^ c = C by rfl,
    hpowab, hpowac, hpowa, hA, hcount]
  change
      (2 * m + 2) * NB + (2 * m + 2) * NC + P -
          (n - 1) * ((2 * m + 2) * n + B + C - 2 * n + 1) =
        P + NB + NC + B + C - n + 1 +
          2 * (NB + NC - n * (n - 1)) * m
  have htail_nonneg' : n * (n - 1) ≤ n * B + n * C := by
    simpa [hNB, hNC] using htail_nonneg
  have hB_pos : 1 ≤ B := le_trans (Nat.succ_le_of_lt hnpos) hB_ge_n
  have hvisible_nonneg : n ≤ n * B + n * C + B + C := by
    calc
      n ≤ n * B := by simpa using Nat.mul_le_mul_left n hB_pos
      _ ≤ n * B + n * C + B + C := by omega
  have hvisible_core :
      2 * NB + 2 * NC =
        (n - 1) * (B + C + 1) + (NB + NC + B + C - n + 1) := by
    rw [hNB, hNC]
    have hpred : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hnpos
    have hmulB : (n - 1) * B + B = n * B := by
      nth_rewrite 2 [← hpred]
      rw [Nat.add_mul, one_mul]
    have hmulC : (n - 1) * C + C = n * C := by
      nth_rewrite 2 [← hpred]
      rw [Nat.add_mul, one_mul]
    symm
    calc
      (n - 1) * (B + C + 1) + (n * B + n * C + B + C - n + 1)
          = n * B + n * C + ((n - 1) * B + B) + ((n - 1) * C + C) := by
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
            omega
      _ = n * B + n * C + n * B + n * C := by
            rw [hmulB, hmulC]
      _ = 2 * (n * B) + 2 * (n * C) := by
            omega
  have htail_core :
      (2 * m) * NB + (2 * m) * NC =
        (2 * m) * (n * (n - 1)) + 2 * (NB + NC - n * (n - 1)) * m := by
    have hsplit : NB + NC = n * (n - 1) + (NB + NC - n * (n - 1)) := by
      omega
    calc
      (2 * m) * NB + (2 * m) * NC = (2 * m) * (NB + NC) := by
        rw [Nat.mul_add]
      _ = (2 * m) * (n * (n - 1) + (NB + NC - n * (n - 1))) := by
        exact congrArg (fun x => (2 * m) * x) hsplit
      _ = (2 * m) * (n * (n - 1)) + (2 * m) * (NB + NC - n * (n - 1)) := by
        rw [Nat.mul_add]
      _ = (2 * m) * (n * (n - 1)) + 2 * (NB + NC - n * (n - 1)) * m := by
        ac_rfl
  have hinside :
      (2 * m + 2) * n + B + C - 2 * n + 1 =
        2 * m * n + (B + C + 1) := by
    rw [Nat.add_mul]
    omega
  have hsub_add :
      (n - 1) * ((2 * m + 2) * n + B + C - 2 * n + 1) =
        (2 * m) * (n * (n - 1)) + (n - 1) * (B + C + 1) := by
    rw [hinside, Nat.mul_add]
    have hmul : (n - 1) * (2 * m * n) = (2 * m) * (n * (n - 1)) := by
      ac_rfl
    rw [hmul]
  have hfront_add :
      (2 * m + 2) * NB + (2 * m + 2) * NC + P =
        (P + NB + NC + B + C - n + 1 +
          2 * (NB + NC - n * (n - 1)) * m) +
          (n - 1) * ((2 * m + 2) * n + B + C - 2 * n + 1) := by
    calc
      (2 * m + 2) * NB + (2 * m + 2) * NC + P
          = ((2 * m) * NB + 2 * NB) + ((2 * m) * NC + 2 * NC) + P := by
            rw [Nat.add_mul, Nat.add_mul]
      _ = ((2 * m) * NB + (2 * m) * NC) + (2 * NB + 2 * NC) + P := by
            ac_rfl
      _ =
          ((2 * m) * (n * (n - 1)) + 2 * (NB + NC - n * (n - 1)) * m) +
            ((n - 1) * (B + C + 1) + (NB + NC + B + C - n + 1)) + P := by
            rw [htail_core, hvisible_core]
      _ =
          (P + NB + NC + B + C - n + 1 +
            2 * (NB + NC - n * (n - 1)) * m) +
            ((2 * m) * (n * (n - 1)) + (n - 1) * (B + C + 1)) := by
            omega
      _ =
          (P + NB + NC + B + C - n + 1 +
            2 * (NB + NC - n * (n - 1)) * m) +
            (n - 1) * ((2 * m + 2) * n + B + C - 2 * n + 1) := by
            rw [hsub_add]
  have hle :
      (n - 1) * ((2 * m + 2) * n + B + C - 2 * n + 1) ≤
        (2 * m + 2) * NB + (2 * m + 2) * NC + P := by
    rw [hfront_add]
    omega
  exact (Nat.sub_eq_iff_eq_add hle).2 hfront_add

end Core3loop
