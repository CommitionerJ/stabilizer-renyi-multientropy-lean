import Core3loop.Basic

namespace Core3loop

def genericDeltaExponent (a b c n : ℕ) : ℕ :=
  n ^ (a + b) + n ^ (a + c) + n ^ (b + c)
    - (n - 1) * (n ^ a + n ^ b + n ^ c - 2 * n + 1)

def evenSpecialDeltaExponent (a b c n : ℕ) : ℕ :=
  n ^ (a + b) + n ^ (a + c) + n ^ (b + c)
    - (n - 1) * (n ^ a + n ^ b + n ^ c - 3 * n + 3)

lemma genericDeltaExponent_a_eq_one {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    genericDeltaExponent 1 b c n =
      n ^ (b + c) + n ^ b + n ^ c + (n - 1) ^ 2 := by
  let B := n ^ b
  let C := n ^ c
  let P := n ^ (b + c)
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
  have hpowb : n ^ (1 + b) = (n - 1) * B + B := by
    dsimp [B]
    have hpred : n - 1 + 1 = n := by omega
    calc
      n ^ (1 + b) = n * n ^ b := by rw [Nat.add_comm, Nat.pow_succ']
      _ = (n - 1 + 1) * n ^ b := by
        nth_rewrite 1 [← hpred]
        rfl
      _ = (n - 1) * n ^ b + n ^ b := by rw [Nat.add_mul, one_mul]
  have hpowc : n ^ (1 + c) = (n - 1) * C + C := by
    dsimp [C]
    have hpred : n - 1 + 1 = n := by omega
    calc
      n ^ (1 + c) = n * n ^ c := by rw [Nat.add_comm, Nat.pow_succ']
      _ = (n - 1 + 1) * n ^ c := by
        nth_rewrite 1 [← hpred]
        rfl
      _ = (n - 1) * n ^ c + n ^ c := by rw [Nat.add_mul, one_mul]
  have hinside : n + B + C - 2 * n + 1 = B + C - n + 1 := by
    omega
  have hsplitBC :
      (n - 1) * B + (n - 1) * C =
        (n - 1) ^ 2 + (n - 1) * (B + C - n + 1) := by
    calc
      (n - 1) * B + (n - 1) * C = (n - 1) * (B + C) := by
        rw [Nat.mul_add]
      _ = (n - 1) * ((n - 1) + (B + C - n + 1)) := by
        have hsplit : B + C = (n - 1) + (B + C - n + 1) := by
          omega
        simpa using congrArg (fun t : ℕ => (n - 1) * t) hsplit
      _ = (n - 1) * (n - 1) + (n - 1) * (B + C - n + 1) := by
        rw [Nat.mul_add]
      _ = (n - 1) ^ 2 + (n - 1) * (B + C - n + 1) := by
        rw [pow_two]
  unfold genericDeltaExponent
  rw [Nat.pow_one, hpowb, hpowc]
  rw [show n ^ (b + c) = P by rfl]
  rw [hinside]
  have hsum :
      (n - 1) * B + B + ((n - 1) * C + C) + P =
        P + B + C + ((n - 1) * B + (n - 1) * C) := by
    ac_rfl
  rw [show (n - 1) * B + B + ((n - 1) * C + C) + P =
      P + B + C + ((n - 1) * B + (n - 1) * C) by
      exact hsum]
  rw [hsplitBC]
  have hcancel :
      P + B + C + ((n - 1) ^ 2 + (n - 1) * (B + C - n + 1)) -
          (n - 1) * (B + C - n + 1) =
        P + B + C + (n - 1) ^ 2 := by
    omega
  simpa [B, C] using hcancel

lemma genericDeltaExponent_222 {n : ℕ} [NeZero n] :
    genericDeltaExponent 2 2 2 n =
      3 * n ^ 4 + 5 * n ^ 2 + 1 - (3 * n ^ 3 + 3 * n) := by
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
  unfold genericDeltaExponent
  simp
  ring_nf
  have hinner : 3 + k * 6 + k ^ 2 * 3 - (2 + k * 2) = 1 + 4 * k + 3 * k ^ 2 := by
    omega
  rw [hinner]
  ring_nf
  omega

lemma evenSpecialDeltaExponent_222 {n : ℕ} [NeZero n] :
    evenSpecialDeltaExponent 2 2 2 n =
      3 * n ^ 4 + 6 * n ^ 2 + 3 - (3 * n ^ 3 + 6 * n) := by
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
  unfold evenSpecialDeltaExponent
  simp
  ring_nf
  have hinner : 3 + k * 6 + k ^ 2 * 3 - (3 + k * 3) = 3 * k + 3 * k ^ 2 := by
    omega
  rw [hinner]
  ring_nf
  omega

end Core3loop
