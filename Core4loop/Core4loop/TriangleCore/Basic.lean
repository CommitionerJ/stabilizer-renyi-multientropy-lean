import Core4loop.NormalFormDims

namespace Core4loop
namespace TriangleCore

abbrev TriPVec (n r : ℕ) := Vec n (r - 1)
abbrev TriYVec (n s : ℕ) := Vec n s
abbrev TriZVec (n t : ℕ) := Vec n t

abbrev TriAFun (n s t : ℕ) := TriYVec n s → TriZVec n t → F
abbrev TriBFun (n r t : ℕ) := TriPVec n r → I n → TriZVec n t → F
abbrev TriCFun (n r s : ℕ) := TriPVec n r → TriYVec n s → I n → F

structure TriNF (n r s t : ℕ) where
  A : TriAFun n s t
  B : TriBFun n r t
  C : TriCFun n r s

noncomputable def triAFunEquiv (n s t : ℕ) :
    TriAFun n s t ≃ (TriYVec n s × TriZVec n t → F) where
  toFun f := fun u => f u.1 u.2
  invFun f := fun y z => f (y, z)
  left_inv f := by
    funext y z
    rfl
  right_inv f := by
    funext u
    rcases u with ⟨y, z⟩
    rfl

noncomputable def triBFunEquiv (n r t : ℕ) :
    TriBFun n r t ≃ (TriPVec n r × I n × TriZVec n t → F) where
  toFun f := fun u => f u.1 u.2.1 u.2.2
  invFun f := fun p sy z => f (p, sy, z)
  left_inv f := by
    funext p sy z
    rfl
  right_inv f := by
    funext u
    rcases u with ⟨p, sy, z⟩
    rfl

noncomputable def triCFunEquiv (n r s : ℕ) :
    TriCFun n r s ≃ (TriPVec n r × TriYVec n s × I n → F) where
  toFun f := fun u => f u.1 u.2.1 u.2.2
  invFun f := fun p y sz => f (p, y, sz)
  left_inv f := by
    funext p y sz
    rfl
  right_inv f := by
    funext u
    rcases u with ⟨p, y, sz⟩
    rfl

noncomputable def triNFEquivProd (n r s t : ℕ) :
    TriNF n r s t ≃ TriAFun n s t × TriBFun n r t × TriCFun n r s where
  toFun nf := (nf.A, nf.B, nf.C)
  invFun x := { A := x.1, B := x.2.1, C := x.2.2 }
  left_inv nf := by
    cases nf
    rfl
  right_inv x := by
    rcases x with ⟨A, B, C⟩
    rfl

noncomputable instance triAFunFintype (n s t : ℕ) [NeZero n] :
    Fintype (TriAFun n s t) :=
  Fintype.ofEquiv _ (triAFunEquiv n s t).symm

noncomputable instance triBFunFintype (n r t : ℕ) [NeZero n] :
    Fintype (TriBFun n r t) :=
  Fintype.ofEquiv _ (triBFunEquiv n r t).symm

noncomputable instance triCFunFintype (n r s : ℕ) [NeZero n] :
    Fintype (TriCFun n r s) :=
  Fintype.ofEquiv _ (triCFunEquiv n r s).symm

noncomputable instance triNFFintype (n r s t : ℕ) [NeZero n] :
    Fintype (TriNF n r s t) :=
  Fintype.ofEquiv _ (triNFEquivProd n r s t).symm

lemma card_triAIndex (n s t : ℕ) [NeZero n] :
    Fintype.card (TriYVec n s × TriZVec n t) = n ^ (s + t) := by
  simp only [TriYVec, TriZVec]
  rw [Fintype.card_prod, card_vec, card_vec, ← pow_add]

lemma card_triBIndex {n r t : ℕ} [NeZero n] (hr : 0 < r) :
    Fintype.card (TriPVec n r × I n × TriZVec n t) = n ^ (r + t) := by
  simp only [TriPVec, TriZVec, I]
  rw [Fintype.card_prod, Fintype.card_prod, card_vec, ZMod.card, card_vec]
  calc
    n ^ (r - 1) * (n * n ^ t)
        = n ^ (r - 1) * (n ^ 1 * n ^ t) := by simp
    _ = n ^ (r - 1) * n ^ (1 + t) := by rw [← pow_add]
    _ = n ^ ((r - 1) + (1 + t)) := by rw [← pow_add]
    _ = n ^ (r + t) := by
      congr 1
      omega

lemma card_triCIndex {n r s : ℕ} [NeZero n] (hr : 0 < r) :
    Fintype.card (TriPVec n r × TriYVec n s × I n) = n ^ (r + s) := by
  simp only [TriPVec, TriYVec, I]
  rw [Fintype.card_prod, Fintype.card_prod, card_vec, card_vec, ZMod.card]
  calc
    n ^ (r - 1) * (n ^ s * n)
        = n ^ (r - 1) * (n ^ s * n ^ 1) := by simp
    _ = n ^ (r - 1) * n ^ (s + 1) := by rw [← pow_add]
    _ = n ^ ((r - 1) + (s + 1)) := by rw [← pow_add]
    _ = n ^ (r + s) := by
      congr 1
      omega

lemma card_triAFun (n s t : ℕ) [NeZero n] :
    Fintype.card (TriAFun n s t) = 2 ^ (n ^ (s + t)) := by
  rw [Fintype.card_congr (triAFunEquiv n s t), Fintype.card_fun, card_triAIndex]
  simp [F]

lemma card_triBFun {n r t : ℕ} [NeZero n] (hr : 0 < r) :
    Fintype.card (TriBFun n r t) = 2 ^ (n ^ (r + t)) := by
  rw [Fintype.card_congr (triBFunEquiv n r t), Fintype.card_fun, card_triBIndex hr]
  simp [F]

lemma card_triCFun {n r s : ℕ} [NeZero n] (hr : 0 < r) :
    Fintype.card (TriCFun n r s) = 2 ^ (n ^ (r + s)) := by
  rw [Fintype.card_congr (triCFunEquiv n r s), Fintype.card_fun, card_triCIndex hr]
  simp [F]

def PTriangle (r s t n : ℕ) : ℕ :=
  n ^ (s + t) + n ^ (r + t) + n ^ (r + s)

theorem card_TriNF {r s t n : ℕ} [NeZero n] (hr : 0 < r) :
    Fintype.card (TriNF n r s t) = 2 ^ PTriangle r s t n := by
  rw [Fintype.card_congr (triNFEquivProd n r s t)]
  rw [Fintype.card_prod, Fintype.card_prod]
  rw [card_triAFun, card_triBFun hr, card_triCFun hr]
  unfold PTriangle
  rw [← pow_add, ← pow_add]
  congr 1
  omega

end TriangleCore
end Core4loop
