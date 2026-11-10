import Core3loop.Symplectic

namespace Core3loop

abbrev BUevenBCoefABC (a c n : ℕ) [NeZero n] :=
  { bcoef : BCoefABC a c n // ∀ t z, bcoef t z ∈ Ueven (a := a) (n := n) }

abbrev CUevenCCoefABC (a b n : ℕ) [NeZero n] :=
  { ccoef : CCoefABC a b n // ∀ y r, ccoef y r ∈ Ueven (a := a) (n := n) }

abbrev EvenTailBModelABC (a c n : ℕ) [NeZero n] :=
  I n → ZCoord c n → Ueven (a := a) (n := n)

abbrev EvenTailCModelABC (a b n : ℕ) [NeZero n] :=
  YCoord b n → I n → Ueven (a := a) (n := n)

noncomputable instance uevenFintype {a n : ℕ} [NeZero n] :
    Fintype (Ueven (a := a) (n := n)) := by
  classical
  infer_instance

noncomputable instance bUevenBCoefABCFintype {a c n : ℕ} [NeZero n] :
    Fintype (BUevenBCoefABC a c n) := by
  classical
  infer_instance

noncomputable instance cUevenCCoefABCFintype {a b n : ℕ} [NeZero n] :
    Fintype (CUevenCCoefABC a b n) := by
  classical
  infer_instance

noncomputable instance evenTailBModelABCFintype {a c n : ℕ} [NeZero n] :
    Fintype (EvenTailBModelABC a c n) := by
  classical
  infer_instance

noncomputable instance evenTailCModelABCFintype {a b n : ℕ} [NeZero n] :
    Fintype (EvenTailCModelABC a b n) := by
  classical
  infer_instance

noncomputable def bUevenBCoefEquivEvenTailBModelABC {a c n : ℕ} [NeZero n] :
    BUevenBCoefABC a c n ≃ EvenTailBModelABC a c n where
  toFun := fun bτ t z => ⟨bτ.1 t z, bτ.2 t z⟩
  invFun := fun X => ⟨fun t z => (X t z).1, fun t z => (X t z).2⟩
  left_inv := by
    intro bτ
    apply Subtype.ext
    funext t z
    rfl
  right_inv := by
    intro X
    funext t z
    apply Subtype.ext
    rfl

noncomputable def cUevenCCoefEquivEvenTailCModelABC {a b n : ℕ} [NeZero n] :
    CUevenCCoefABC a b n ≃ EvenTailCModelABC a b n where
  toFun := fun cτ y r => ⟨cτ.1 y r, cτ.2 y r⟩
  invFun := fun X => ⟨fun y r => (X y r).1, fun y r => (X y r).2⟩
  left_inv := by
    intro cτ
    apply Subtype.ext
    funext y r
    rfl
  right_inv := by
    intro X
    funext y r
    apply Subtype.ext
    rfl

noncomputable def evenTailBModelABCEquivPair {a c n : ℕ} [NeZero n] :
    EvenTailBModelABC a c n ≃ ((I n × ZCoord c n) → Ueven (a := a) (n := n)) where
  toFun := fun X tpz => X tpz.1 tpz.2
  invFun := fun X t z => X (t, z)
  left_inv := by
    intro X
    funext t z
    rfl
  right_inv := by
    intro X
    funext tpz
    rcases tpz with ⟨t, z⟩
    rfl

noncomputable def evenTailCModelABCEquivPair {a b n : ℕ} [NeZero n] :
    EvenTailCModelABC a b n ≃ ((YCoord b n × I n) → Ueven (a := a) (n := n)) where
  toFun := fun X yr => X yr.1 yr.2
  invFun := fun X y r => X (y, r)
  left_inv := by
    intro X
    funext y r
    rfl
  right_inv := by
    intro X
    funext yr
    rcases yr with ⟨y, r⟩
    rfl

lemma card_evenTailBIndexABC {c n : ℕ} [NeZero n] :
    Fintype.card (I n × ZCoord c n) = n ^ (c + 1) := by
  calc
    Fintype.card (I n × ZCoord c n) = n * n ^ c := by
      simp [I, ZMod.card]
    _ = n ^ (c + 1) := by
      rw [Nat.pow_succ']

lemma card_evenTailCIndexABC {b n : ℕ} [NeZero n] :
    Fintype.card (YCoord b n × I n) = n ^ (b + 1) := by
  calc
    Fintype.card (YCoord b n × I n) = n ^ b * n := by
      simp [I, ZMod.card]
    _ = n * n ^ b := by
      rw [Nat.mul_comm]
    _ = n ^ (b + 1) := by
      rw [Nat.pow_succ', Nat.mul_comm]

lemma natCard_UevenABC_of_even {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Nat.card (Ueven (a := a) (n := n)) = 2 ^ (n ^ (a - 1) - 2) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  rw [finrank_Ueven_of_even_n (a := a) (n := n) hn ha2]
  simp [F]

theorem card_UevenABC_of_even {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Fintype.card (Ueven (a := a) (n := n)) = 2 ^ (n ^ (a - 1) - 2) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_UevenABC_of_even (a := a) (n := n) hn ha2

lemma natCard_evenTailBModelABC_of_even {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Nat.card (EvenTailBModelABC a c n) = 2 ^ ((n ^ (a - 1) - 2) * n ^ (c + 1)) := by
  rw [Nat.card_congr (evenTailBModelABCEquivPair (a := a) (c := c) (n := n))]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, card_evenTailBIndexABC]
  rw [← Nat.card_eq_fintype_card (α := Ueven (a := a) (n := n))]
  rw [natCard_UevenABC_of_even (a := a) (n := n) hn ha2]
  rw [← pow_mul]

theorem card_evenTailBModelABC_of_even {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Fintype.card (EvenTailBModelABC a c n) = 2 ^ ((n ^ (a - 1) - 2) * n ^ (c + 1)) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_evenTailBModelABC_of_even (a := a) (c := c) (n := n) hn ha2

lemma natCard_evenTailCModelABC_of_even {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Nat.card (EvenTailCModelABC a b n) = 2 ^ ((n ^ (a - 1) - 2) * n ^ (b + 1)) := by
  rw [Nat.card_congr (evenTailCModelABCEquivPair (a := a) (b := b) (n := n))]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, card_evenTailCIndexABC]
  rw [← Nat.card_eq_fintype_card (α := Ueven (a := a) (n := n))]
  rw [natCard_UevenABC_of_even (a := a) (n := n) hn ha2]
  rw [← pow_mul]

theorem card_evenTailCModelABC_of_even {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Fintype.card (EvenTailCModelABC a b n) = 2 ^ ((n ^ (a - 1) - 2) * n ^ (b + 1)) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_evenTailCModelABC_of_even (a := a) (b := b) (n := n) hn ha2

theorem card_BUevenBCoefABC_of_even {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Fintype.card (BUevenBCoefABC a c n) = 2 ^ ((n ^ (a - 1) - 2) * n ^ (c + 1)) := by
  rw [Fintype.card_congr (bUevenBCoefEquivEvenTailBModelABC (a := a) (c := c) (n := n))]
  exact card_evenTailBModelABC_of_even (a := a) (c := c) (n := n) hn ha2

theorem card_CUevenCCoefABC_of_even {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Fintype.card (CUevenCCoefABC a b n) = 2 ^ ((n ^ (a - 1) - 2) * n ^ (b + 1)) := by
  rw [Fintype.card_congr (cUevenCCoefEquivEvenTailCModelABC (a := a) (b := b) (n := n))]
  exact card_evenTailCModelABC_of_even (a := a) (b := b) (n := n) hn ha2

end Core3loop
