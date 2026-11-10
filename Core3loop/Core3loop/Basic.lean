import Core3loop.Reference.No13_abc_general

open scoped BigOperators

namespace Core3loop

abbrev F := ZMod 2
abbrev I (n : ℕ) := ZMod n

abbrev Coord (m n : ℕ) := No13Migration.Coord m n
abbrev XCoord (a n : ℕ) := No13Migration.XCoord a n
abbrev YCoord (b n : ℕ) := No13Migration.YCoord b n
abbrev ZCoord (c n : ℕ) := No13Migration.ZCoord c n

abbrev Site (a b c n : ℕ) := XCoord a n × YCoord b n × ZCoord c n

abbrev AFieldABC (b c n : ℕ) := No13Migration.AFieldABC b c n
abbrev BFieldABC (a c n : ℕ) := No13Migration.BFieldABC a c n
abbrev CFieldABC (a b n : ℕ) := No13Migration.CFieldABC a b n

abbrev ProfileABC (a n : ℕ) := XCoord a n → F
abbrev BCoefABC (a c n : ℕ) := I n → ZCoord c n → ProfileABC a n
abbrev CCoefABC (a b n : ℕ) := YCoord b n → I n → ProfileABC a n

abbrev ScalarBCoef (c n : ℕ) := I n → ZCoord c n → F
abbrev ScalarCCoef (b n : ℕ) := YCoord b n → I n → F

abbrev bitSign := No13Migration.bitSign

lemma F_add_self (x : F) : x + x = 0 :=
  No13Migration.F2_add_self x

lemma zmod_step_const {n : ℕ} [NeZero n] {α : Type*} (g : I n → α)
    (h : ∀ s, g (s + 1) = g s) :
    ∀ s, g s = g 0 :=
  No13Migration.zmod_step_const g h

def shiftCoord {m n : ℕ} (u : Coord m n) (i : Fin m) : Coord m n :=
  u + Pi.single i 1

def decCoord {m n : ℕ} (u : Coord m n) (i : Fin m) : Coord m n :=
  u - Pi.single i 1

abbrev shiftX {a n : ℕ} := @shiftCoord (a - 1) n
abbrev shiftY {b n : ℕ} := @shiftCoord b n
abbrev shiftZ {c n : ℕ} := @shiftCoord c n

noncomputable abbrev sigmaCoord {m n : ℕ} [NeZero n] := @No13Migration.sumCoord m n
noncomputable abbrev sumY {b n : ℕ} [NeZero n] := @No13Migration.sumY b n
noncomputable abbrev sumZ {c n : ℕ} [NeZero n] := @No13Migration.sumZ c n

def tailCoord {m n : ℕ} (u : Coord (m + 1) n) : Coord m n :=
  fun i => u i.succ

def composeCoord {m n : ℕ} (head : I n) (tail : Coord m n) : Coord (m + 1) n
  | ⟨0, _h⟩ => head
  | ⟨k + 1, hk⟩ => tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩

@[simp] lemma tailCoord_composeCoord {m n : ℕ} (head : I n) (tail : Coord m n) :
    tailCoord (composeCoord head tail) = tail := by
  funext i
  cases i with
  | mk val isLt =>
      rfl

@[simp] lemma composeCoord_zero {m n : ℕ} (head : I n) (tail : Coord m n) :
    composeCoord head tail 0 = head := rfl

noncomputable abbrev coordSingle {m n : ℕ} [NeZero n] := @No13Migration.coordSingle m n
noncomputable abbrev yOfSum {b n : ℕ} [NeZero n] := @No13Migration.yOfSum b n
noncomputable abbrev zOfSum {c n : ℕ} [NeZero n] := @No13Migration.zOfSum c n

@[simp] lemma sumCoord_coordSingle {m n : ℕ} [NeZero n] (hm : 0 < m) (t : I n) :
    sigmaCoord (coordSingle (m := m) (n := n) hm t) = t := by
  simpa [sigmaCoord] using No13Migration.sumCoord_coordSingle (k := m) (n := n) hm t

@[simp] lemma sumY_yOfSum {b n : ℕ} [NeZero n] (hb : 0 < b) (s : I n) :
    sumY (yOfSum (n := n) hb s) = s :=
  No13Migration.sumY_yOfSum hb s

@[simp] lemma sumZ_zOfSum {c n : ℕ} [NeZero n] (hc : 0 < c) (r : I n) :
    sumZ (zOfSum (n := n) hc r) = r :=
  No13Migration.sumZ_zOfSum hc r

@[simp] lemma sumY_add_single {b n : ℕ} [NeZero n] (y : YCoord b n) (i : Fin b) :
    sumY (y + Pi.single i 1) = sumY y + 1 :=
  No13Migration.sumY_add_single y i

@[simp] lemma sumZ_add_single {c n : ℕ} [NeZero n] (z : ZCoord c n) (i : Fin c) :
    sumZ (z + Pi.single i 1) = sumZ z + 1 :=
  No13Migration.sumZ_add_single z i

lemma card_Coord (m n : ℕ) [NeZero n] :
    Fintype.card (Coord m n) = n ^ m := by
  simpa [Coord] using No13Migration.card_Coord (k := m) (n := n)

lemma card_XCoord (a n : ℕ) [NeZero n] :
    Fintype.card (XCoord a n) = n ^ (a - 1) := by
  simpa [XCoord] using No13Migration.card_XCoord (a := a) (n := n)

lemma card_YCoord (b n : ℕ) [NeZero n] :
    Fintype.card (YCoord b n) = n ^ b := by
  simpa [YCoord] using No13Migration.card_YCoord (b := b) (n := n)

lemma card_ZCoord (c n : ℕ) [NeZero n] :
    Fintype.card (ZCoord c n) = n ^ c := by
  simpa [ZCoord] using No13Migration.card_ZCoord (c := c) (n := n)

lemma card_Site {a b c n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (Site a b c n) = n ^ (a + b + c - 1) := by
  calc
    Fintype.card (Site a b c n)
        = Fintype.card (XCoord a n) * Fintype.card (YCoord b n) * Fintype.card (ZCoord c n) := by
            simp [Site, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = n ^ (a - 1) * n ^ b * n ^ c := by rw [card_XCoord, card_YCoord, card_ZCoord]
    _ = n ^ ((a - 1) + b + c) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
    _ = n ^ (a + b + c - 1) := by
          have : (a - 1) + b + c = a + b + c - 1 := by omega
          rw [this]

lemma card_AFieldABC (b c n : ℕ) [NeZero n] :
    Fintype.card (AFieldABC b c n) = 2 ^ (n ^ (b + c)) := by
  simpa [AFieldABC] using No13Migration.card_AFieldABC (b := b) (c := c) (n := n)

lemma card_BFieldABC {a c n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (BFieldABC a c n) = 2 ^ (n ^ (a + c)) := by
  simpa [BFieldABC] using No13Migration.card_BFieldABC (a := a) (c := c) (n := n) ha

lemma card_CFieldABC {a b n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (CFieldABC a b n) = 2 ^ (n ^ (a + b)) := by
  simpa [CFieldABC] using No13Migration.card_CFieldABC (a := a) (b := b) (n := n) ha

lemma card_ProfileABC (a n : ℕ) [NeZero n] :
    Fintype.card (ProfileABC a n) = 2 ^ (n ^ (a - 1)) := by
  rw [Fintype.card_fun, card_XCoord]
  simp [F, ZMod.card]

end Core3loop
