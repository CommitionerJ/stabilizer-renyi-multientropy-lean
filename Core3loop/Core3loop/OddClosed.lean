import Core3loop.ProfileOddClosed
import Core3loop.Exponents

namespace Core3loop

lemma exists_profileCard_eq_two_mul_add_one_of_odd {a n : ℕ} [NeZero n]
    (hn : Odd n) :
    ∃ m, ProfileCard a n = 2 * m + 1 := by
  simpa [ProfileCard, card_XCoord] using (odd_card_XCoord_of_odd (a := a) (n := n) hn)

theorem DeltaABC_odd_closed_with_profileCard_witness_of_odd {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    ∃ m, ProfileCard a n = 2 * m + 1 ∧
      DeltaABC a b c n =
        (2 : ℤ) ^ (n ^ (b + c) + n ^ b + n ^ c + (n - 1) ^ 2 + ordinaryPairExponentABC b c n * m) := by
  rcases exists_profileCard_eq_two_mul_add_one_of_odd (a := a) (n := n) hn with ⟨m, hm⟩
  refine ⟨m, hm, ?_⟩
  rw [DeltaABC_after_A_eq_pow_mul_oddPureTailSignSumABC_of_odd
    (a := a) (b := b) (c := c) (n := n) ha hb hc hn]
  rw [oddPureTailSignSumABC_eq_closed_form
    (a := a) (b := b) (c := c) (n := n) (m := m) hm hb hc]
  rw [← pow_add]

lemma genericDeltaExponent_eq_profileCard_witness_exponent
    {a b c n m : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hm : ProfileCard a n = 2 * m + 1) :
    genericDeltaExponent a b c n =
      n ^ (b + c) + n ^ b + n ^ c + (n - 1) ^ 2 + ordinaryPairExponentABC b c n * m := by
  let A : ℕ := ProfileCard a n
  let B : ℕ := n ^ b
  let C : ℕ := n ^ c
  let NB : ℕ := n ^ (b + 1)
  let NC : ℕ := n ^ (c + 1)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt hb
  have hc1 : 1 ≤ c := Nat.succ_le_of_lt hc
  have hBn : n ≤ B := by
    dsimp [B]
    simpa [pow_one] using Nat.pow_le_pow_right hn1 hb1
  have hCn : n ≤ C := by
    dsimp [C]
    simpa [pow_one] using Nat.pow_le_pow_right hn1 hc1
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
  have hNB : NB = (n - 1) * B + B := by
    dsimp [NB, B]
    have hpred : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    calc
      n ^ (b + 1) = n ^ b * n := by rw [Nat.pow_add, pow_one]
      _ = n * n ^ b := by rw [Nat.mul_comm]
      _ = (n - 1 + 1) * n ^ b := by
            nth_rewrite 1 [← hpred]
            rfl
      _ = (n - 1) * n ^ b + n ^ b := by rw [Nat.add_mul, one_mul]
  have hNC : NC = (n - 1) * C + C := by
    dsimp [NC, C]
    have hpred : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    calc
      n ^ (c + 1) = n ^ c * n := by rw [Nat.pow_add, pow_one]
      _ = n * n ^ c := by rw [Nat.mul_comm]
      _ = (n - 1 + 1) * n ^ c := by
            nth_rewrite 1 [← hpred]
            rfl
      _ = (n - 1) * n ^ c + n ^ c := by rw [Nat.add_mul, one_mul]
  have hsplitBC :
      (n - 1) * B + (n - 1) * C =
        (n - 1) * (B + C - n + 1) + (n - 1) ^ 2 := by
    calc
      (n - 1) * B + (n - 1) * C = (n - 1) * (B + C) := by
        rw [Nat.mul_add]
      _ = (n - 1) * ((n - 1) + (B + C - n + 1)) := by
        have hsplit : B + C = (n - 1) + (B + C - n + 1) := by
          omega
        simpa using congrArg (fun t : ℕ => (n - 1) * t) hsplit
      _ = (n - 1) * (n - 1) + (n - 1) * (B + C - n + 1) := by
        rw [Nat.mul_add]
      _ = (n - 1) * (B + C - n + 1) + (n - 1) ^ 2 := by
        rw [pow_two]
        ac_rfl
  have hcore_add :
      NB + NC =
        (n - 1) * (B + C - n + 1) + (B + C + (n - 1) ^ 2) := by
    rw [hNB, hNC]
    calc
      (n - 1) * B + B + ((n - 1) * C + C)
          = ((n - 1) * B + (n - 1) * C) + (B + C) := by
              ac_rfl
      _ = ((n - 1) * (B + C - n + 1) + (n - 1) ^ 2) + (B + C) := by
            rw [hsplitBC]
      _ = (n - 1) * (B + C - n + 1) + (B + C + (n - 1) ^ 2) := by
            ac_rfl
  have hnm1_le_B : n - 1 ≤ B := le_trans (Nat.sub_le _ _) hBn
  have htail_le : n * (n - 1) ≤ NB + NC := by
    calc
      n * (n - 1) ≤ n * B := Nat.mul_le_mul_left _ hnm1_le_B
      _ = NB := by
            dsimp [NB, B]
            rw [Nat.pow_add, pow_one, Nat.mul_comm]
      _ ≤ NB + NC := Nat.le_add_right _ _
  have hpair_add :
      (2 * m) * NB + (2 * m) * NC =
        (2 * m) * (n * (n - 1)) + (2 * m) * (NB + NC - n * (n - 1)) := by
    have htail :
        NB + NC = (NB + NC - n * (n - 1)) + n * (n - 1) := by
      exact (Nat.sub_eq_iff_eq_add htail_le).1 rfl
    calc
      (2 * m) * NB + (2 * m) * NC = (2 * m) * (NB + NC) := by
        rw [Nat.mul_add]
      _ = (2 * m) * ((NB + NC - n * (n - 1)) + n * (n - 1)) := by
            exact congrArg (fun t : ℕ => (2 * m) * t) htail
      _ = (2 * m) * (NB + NC - n * (n - 1)) + (2 * m) * (n * (n - 1)) := by
            rw [Nat.mul_add]
      _ = (2 * m) * (n * (n - 1)) + (2 * m) * (NB + NC - n * (n - 1)) := by
            ac_rfl
  have hinside :
      (2 * m + 1) * n + B + C - 2 * n + 1 =
        2 * m * n + (B + C - n + 1) := by
    rw [Nat.add_mul, one_mul]
    omega
  have hsub_add :
      (n - 1) * ((2 * m + 1) * n + B + C - 2 * n + 1) =
        (2 * m) * (n * (n - 1)) + (n - 1) * (B + C - n + 1) := by
    rw [hinside, Nat.mul_add]
    ac_rfl
  have hfront_add :
      (2 * m + 1) * NB + (2 * m + 1) * NC + n ^ (b + c) =
        (n - 1) * ((2 * m + 1) * n + B + C - 2 * n + 1) +
          (n ^ (b + c) + B + C + (n - 1) ^ 2 +
            (2 * m) * (NB + NC - n * (n - 1))) := by
    calc
      (2 * m + 1) * NB + (2 * m + 1) * NC + n ^ (b + c)
          = ((2 * m) * NB + NB) + ((2 * m) * NC + NC) + n ^ (b + c) := by
              rw [Nat.add_mul, one_mul, Nat.add_mul, one_mul]
      _ = ((2 * m) * NB + (2 * m) * NC) + (NB + NC) + n ^ (b + c) := by
            ac_rfl
      _ = ((2 * m) * (n * (n - 1)) + (2 * m) * (NB + NC - n * (n - 1))) +
            ((n - 1) * (B + C - n + 1) + (B + C + (n - 1) ^ 2)) +
            n ^ (b + c) := by
              rw [hpair_add, hcore_add]
      _ = (n - 1) * ((2 * m + 1) * n + B + C - 2 * n + 1) +
            (n ^ (b + c) + B + C + (n - 1) ^ 2 +
              (2 * m) * (NB + NC - n * (n - 1))) := by
              rw [hsub_add]
              ac_rfl
  have hfront :
      (2 * m + 1) * NB + (2 * m + 1) * NC + n ^ (b + c) -
          (n - 1) * ((2 * m + 1) * n + B + C - 2 * n + 1) =
        n ^ (b + c) + B + C + (n - 1) ^ 2 +
          (2 * m) * (NB + NC - n * (n - 1)) := by
    have hle :
        (n - 1) * ((2 * m + 1) * n + B + C - 2 * n + 1) ≤
          (2 * m + 1) * NB + (2 * m + 1) * NC + n ^ (b + c) := by
      exact Nat.le.intro hfront_add.symm
    have hfront_add' :
        (2 * m + 1) * NB + (2 * m + 1) * NC + n ^ (b + c) =
          (n ^ (b + c) + B + C + (n - 1) ^ 2 +
            (2 * m) * (NB + NC - n * (n - 1))) +
          (n - 1) * ((2 * m + 1) * n + B + C - 2 * n + 1) := by
      rw [hfront_add]
      ac_rfl
    exact (Nat.sub_eq_iff_eq_add hle).2 hfront_add'
  unfold genericDeltaExponent ordinaryPairExponentABC
  have hA : A = 2 * m + 1 := by simpa [A] using hm
  rw [hpowab, hpowac, hpowa, hA]
  change (2 * m + 1) * NB + (2 * m + 1) * NC + n ^ (b + c) -
      (n - 1) * ((2 * m + 1) * n + n ^ b + n ^ c - 2 * n + 1) =
    n ^ (b + c) + B + C + (n - 1) ^ 2 + 2 * (NB + NC - n * (n - 1)) * m
  rw [hfront]
  ac_rfl

theorem DeltaABC_odd_closed_of_odd {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    DeltaABC a b c n = (2 : ℤ) ^ genericDeltaExponent a b c n := by
  rcases DeltaABC_odd_closed_with_profileCard_witness_of_odd
      (a := a) (b := b) (c := c) (n := n) ha hb hc hn with ⟨m, hm, hΔ⟩
  rw [hΔ]
  congr 1
  exact (genericDeltaExponent_eq_profileCard_witness_exponent
    (a := a) (b := b) (c := c) (n := n) (m := m) ha hb hc hm).symm

end Core3loop
