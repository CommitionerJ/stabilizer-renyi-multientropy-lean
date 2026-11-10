import Core4loop.Graphs

namespace Core4loop

abbrev AFun4 (n b c d : ℕ) :=
  YVec n b → ZVec n c → WVec n d → F

abbrev BFun4 (n a c d : ℕ) :=
  PVec n a → I n → ZVec n c → WVec n d → F

abbrev CFun4 (n a b d : ℕ) :=
  PVec n a → YVec n b → I n → WVec n d → F

abbrev WFun4 (n a b c : ℕ) :=
  PVec n a → YVec n b → ZVec n c → I n → F

structure NF4 (n a b c d : ℕ) where
  A : AFun4 n b c d
  B : BFun4 n a c d
  C : CFun4 n a b d
  W : WFun4 n a b c

def P4 (a b c d n : ℕ) : ℕ :=
  n ^ (b + c + d) + n ^ (a + c + d) +
  n ^ (a + b + d) + n ^ (a + b + c)

noncomputable def aFun4Equiv (n b c d : ℕ) :
    AFun4 n b c d ≃ (YVec n b × ZVec n c × WVec n d → F) where
  toFun f := fun | ⟨y, z, w⟩ => f y z w
  invFun f := fun y z w => f (y, z, w)
  left_inv f := by
    funext y z w
    rfl
  right_inv f := by
    funext u
    rcases u with ⟨y, z, w⟩
    rfl

noncomputable def bFun4Equiv (n a c d : ℕ) :
    BFun4 n a c d ≃ (PVec n a × I n × ZVec n c × WVec n d → F) where
  toFun f := fun | ⟨p, sy, z, w⟩ => f p sy z w
  invFun f := fun p sy z w => f (p, sy, z, w)
  left_inv f := by
    funext p sy z w
    rfl
  right_inv f := by
    funext u
    rcases u with ⟨p, sy, z, w⟩
    rfl

noncomputable def cFun4Equiv (n a b d : ℕ) :
    CFun4 n a b d ≃ (PVec n a × YVec n b × I n × WVec n d → F) where
  toFun f := fun | ⟨p, y, sz, w⟩ => f p y sz w
  invFun f := fun p y sz w => f (p, y, sz, w)
  left_inv f := by
    funext p y sz w
    rfl
  right_inv f := by
    funext u
    rcases u with ⟨p, y, sz, w⟩
    rfl

noncomputable def wFun4Equiv (n a b c : ℕ) :
    WFun4 n a b c ≃ (PVec n a × YVec n b × ZVec n c × I n → F) where
  toFun f := fun | ⟨p, y, z, sw⟩ => f p y z sw
  invFun f := fun p y z sw => f (p, y, z, sw)
  left_inv f := by
    funext p y z sw
    rfl
  right_inv f := by
    funext u
    rcases u with ⟨p, y, z, sw⟩
    rfl

noncomputable def nf4EquivProd (n a b c d : ℕ) :
    NF4 n a b c d ≃
      AFun4 n b c d × BFun4 n a c d × CFun4 n a b d × WFun4 n a b c where
  toFun nf := (nf.A, nf.B, nf.C, nf.W)
  invFun x :=
    { A := x.1
      B := x.2.1
      C := x.2.2.1
      W := x.2.2.2 }
  left_inv nf := by
    cases nf
    rfl
  right_inv x := by
    rcases x with ⟨A, B, C, W⟩
    rfl

noncomputable instance aFun4Fintype (n b c d : ℕ) [NeZero n] :
    Fintype (AFun4 n b c d) :=
  Fintype.ofEquiv _ (aFun4Equiv n b c d).symm

noncomputable instance bFun4Fintype (n a c d : ℕ) [NeZero n] :
    Fintype (BFun4 n a c d) :=
  Fintype.ofEquiv _ (bFun4Equiv n a c d).symm

noncomputable instance cFun4Fintype (n a b d : ℕ) [NeZero n] :
    Fintype (CFun4 n a b d) :=
  Fintype.ofEquiv _ (cFun4Equiv n a b d).symm

noncomputable instance wFun4Fintype (n a b c : ℕ) [NeZero n] :
    Fintype (WFun4 n a b c) :=
  Fintype.ofEquiv _ (wFun4Equiv n a b c).symm

noncomputable instance nf4Fintype (n a b c d : ℕ) [NeZero n] :
    Fintype (NF4 n a b c d) :=
  Fintype.ofEquiv _ (nf4EquivProd n a b c d).symm

lemma card_BIndex4 {n a c d : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (PVec n a × I n × ZVec n c × WVec n d) =
      n ^ (a + c + d) := by
  simp only [PVec, ZVec, WVec, I]
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  rw [card_vec, ZMod.card, card_vec, card_vec]
  calc
    n ^ (a - 1) * (n * (n ^ c * n ^ d))
        = n ^ (a - 1) * (n * n ^ (c + d)) := by
            rw [pow_add]
    _ = n ^ (a - 1) * (n ^ 1 * n ^ (c + d)) := by
            simp
    _ = n ^ (a - 1) * n ^ (1 + (c + d)) := by
            rw [← pow_add]
    _ = n ^ ((a - 1) + (1 + (c + d))) := by
            rw [← pow_add]
    _ = n ^ (a + c + d) := by
            congr 1
            omega

lemma card_CIndex4 {n a b d : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (PVec n a × YVec n b × I n × WVec n d) =
      n ^ (a + b + d) := by
  simp only [PVec, YVec, WVec, I]
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  rw [card_vec, card_vec, ZMod.card, card_vec]
  calc
    n ^ (a - 1) * (n ^ b * (n * n ^ d))
        = n ^ (a - 1) * (n ^ b * (n ^ 1 * n ^ d)) := by
            simp
    _ = n ^ (a - 1) * (n ^ b * n ^ (1 + d)) := by
            rw [← pow_add]
    _ = n ^ (a - 1) * n ^ (b + (1 + d)) := by
            rw [← pow_add]
    _ = n ^ ((a - 1) + (b + (1 + d))) := by
            rw [← pow_add]
    _ = n ^ (a + b + d) := by
            congr 1
            omega

lemma card_WIndex4 {n a b c : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (PVec n a × YVec n b × ZVec n c × I n) =
      n ^ (a + b + c) := by
  simp only [PVec, YVec, ZVec, I]
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  rw [card_vec, card_vec, card_vec, ZMod.card]
  calc
    n ^ (a - 1) * (n ^ b * (n ^ c * n))
        = n ^ (a - 1) * (n ^ b * (n ^ c * n ^ 1)) := by
            simp
    _ = n ^ (a - 1) * (n ^ b * n ^ (c + 1)) := by
            rw [← pow_add]
    _ = n ^ (a - 1) * n ^ (b + (c + 1)) := by
            rw [← pow_add]
    _ = n ^ ((a - 1) + (b + (c + 1))) := by
            rw [← pow_add]
    _ = n ^ (a + b + c) := by
            congr 1
            omega

lemma card_AFun4 (n b c d : ℕ) [NeZero n] :
    Fintype.card (AFun4 n b c d) = 2 ^ (n ^ (b + c + d)) := by
  rw [Fintype.card_congr (aFun4Equiv n b c d), Fintype.card_fun, card_vec3]
  simp [F]

lemma card_BFun4 {n a c d : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (BFun4 n a c d) = 2 ^ (n ^ (a + c + d)) := by
  rw [Fintype.card_congr (bFun4Equiv n a c d), Fintype.card_fun, card_BIndex4 ha]
  simp [F]

lemma card_CFun4 {n a b d : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (CFun4 n a b d) = 2 ^ (n ^ (a + b + d)) := by
  rw [Fintype.card_congr (cFun4Equiv n a b d), Fintype.card_fun, card_CIndex4 ha]
  simp [F]

lemma card_WFun4 {n a b c : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (WFun4 n a b c) = 2 ^ (n ^ (a + b + c)) := by
  rw [Fintype.card_congr (wFun4Equiv n a b c), Fintype.card_fun, card_WIndex4 ha]
  simp [F]

theorem card_NF4
    {a b c d n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (NF4 n a b c d) = 2 ^ P4 a b c d n := by
  rw [Fintype.card_congr (nf4EquivProd n a b c d)]
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  rw [card_AFun4, card_BFun4 ha, card_CFun4 ha, card_WFun4 ha]
  unfold P4
  calc
    2 ^ n ^ (b + c + d) *
        (2 ^ n ^ (a + c + d) *
          (2 ^ n ^ (a + b + d) * 2 ^ n ^ (a + b + c)))
        = 2 ^ n ^ (b + c + d) *
            (2 ^ n ^ (a + c + d) *
              2 ^ (n ^ (a + b + d) + n ^ (a + b + c))) := by
              rw [← pow_add]
    _ = 2 ^ n ^ (b + c + d) *
          2 ^ (n ^ (a + c + d) +
            (n ^ (a + b + d) + n ^ (a + b + c))) := by
            rw [← pow_add]
    _ = 2 ^ (n ^ (b + c + d) +
          (n ^ (a + c + d) +
            (n ^ (a + b + d) + n ^ (a + b + c)))) := by
            rw [← pow_add]
    _ = 2 ^ (n ^ (b + c + d) + n ^ (a + c + d) +
          n ^ (a + b + d) + n ^ (a + b + c)) := by
            congr 1
            omega

theorem card_NF4_formula
    {a b c d n : ℕ} [NeZero n] (ha : 0 < a) :
    Fintype.card (NF4 n a b c d) = 2 ^ P4 a b c d n :=
  card_NF4 ha

end Core4loop
