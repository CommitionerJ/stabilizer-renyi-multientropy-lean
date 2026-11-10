import Core3loop.PhaseReduction
import Core3loop.VisibleSpace

open scoped BigOperators

namespace Core3loop

noncomputable def xCoordZero {n : ℕ} : XCoord 1 n := default

lemma eq_xCoordZero {n : ℕ} (x : XCoord 1 n) : x = xCoordZero (n := n) := by
  ext i
  have hi : i.1 < 0 := by simpa using i.2
  exact False.elim (Nat.not_lt_zero _ hi)

instance subsingleton_XCoord_one {n : ℕ} : Subsingleton (XCoord 1 n) where
  allEq := by
    intro x y
    trans xCoordZero (n := n)
    · exact eq_xCoordZero (n := n) x
    · exact (eq_xCoordZero (n := n) y).symm

lemma sum_XCoord_one {n : ℕ} [NeZero n] (f : XCoord 1 n → F) :
    ∑ x : XCoord 1 n, f x = f (xCoordZero (n := n)) := by
  exact Fintype.sum_subsingleton (f := f) (a := xCoordZero (n := n))

noncomputable def bFieldEquivScalarBCoef {c n : ℕ} [NeZero n] :
    BFieldABC 1 c n ≃ ScalarBCoef c n where
  toFun := fun B t z => B (xCoordZero (n := n), t, z)
  invFun := fun bcoef x => bcoef x.2.1 x.2.2
  left_inv := by
    intro B
    funext x
    rcases x with ⟨p, t, z⟩
    have hp : p = xCoordZero (n := n) := eq_xCoordZero (n := n) p
    subst hp
    rfl
  right_inv := by
    intro bcoef
    rfl

noncomputable def cFieldEquivScalarCCoef {b n : ℕ} [NeZero n] :
    CFieldABC 1 b n ≃ ScalarCCoef b n where
  toFun := fun C y r => C (xCoordZero (n := n), y, r)
  invFun := fun ccoef x => ccoef x.2.1 x.2.2
  left_inv := by
    intro C
    funext x
    rcases x with ⟨p, y, r⟩
    have hp : p = xCoordZero (n := n) := eq_xCoordZero (n := n) p
    subst hp
    rfl
  right_inv := by
    intro ccoef
    rfl

lemma coeffFromBC_abc_apply_of_a_eq_one {b c n : ℕ} [NeZero n]
    (B : BFieldABC 1 c n) (C : CFieldABC 1 b n) (y : YCoord b n) (z : ZCoord c n) :
    coeffFromBC_abc (a := 1) (b := b) (c := c) (n := n) B C (y, z) =
      (bFieldEquivScalarBCoef (c := c) (n := n) B) (sumY y) z +
        (bFieldEquivScalarBCoef (c := c) (n := n) B) (sumY y + 1) z +
        (cFieldEquivScalarCCoef (b := b) (n := n) C) y (sumZ z) +
        (cFieldEquivScalarCCoef (b := b) (n := n) C) y (sumZ z + 1) := by
  unfold coeffFromBC_abc No13Migration.coeffFromBC_abc_real
  rw [sum_XCoord_one (n := n) (f := fun p : XCoord 1 n =>
    B (p, sumY y, z) +
      B (p, sumY y + 1, z) +
      C (p, y, sumZ z) +
      C (p, y, sumZ z + 1))]
  rfl

noncomputable def survivingBCEquivScalarVisible {b c n : ℕ} [NeZero n] :
    SurvivingBC 1 b c n ≃ ScalarVisibleCompat b c n where
  toFun := fun bc =>
    { bcoef := bFieldEquivScalarBCoef (c := c) (n := n) bc.1.1
      ccoef := cFieldEquivScalarCCoef (b := b) (n := n) bc.1.2
      compat := by
        intro y z
        have h := congrFun bc.2 (y, z)
        rw [coeffFromBC_abc_apply_of_a_eq_one (b := b) (c := c) (n := n) bc.1.1 bc.1.2 y z] at h
        exact h }
  invFun := fun bc =>
    ⟨((bFieldEquivScalarBCoef (c := c) (n := n)).symm bc.bcoef,
      (cFieldEquivScalarCCoef (b := b) (n := n)).symm bc.ccoef),
      by
        funext yz
        rcases yz with ⟨y, z⟩
        rw [coeffFromBC_abc_apply_of_a_eq_one (b := b) (c := c) (n := n)
          ((bFieldEquivScalarBCoef (c := c) (n := n)).symm bc.bcoef)
          ((cFieldEquivScalarCCoef (b := b) (n := n)).symm bc.ccoef) y z]
        simpa using bc.compat y z⟩
  left_inv := by
    intro bc
    rcases bc with ⟨⟨B, C⟩, hBC⟩
    apply Subtype.ext
    apply Prod.ext
    · exact (bFieldEquivScalarBCoef (c := c) (n := n)).left_inv B
    · exact (cFieldEquivScalarCCoef (b := b) (n := n)).left_inv C
  right_inv := by
    intro bc
    cases bc
    simp [bFieldEquivScalarBCoef, cFieldEquivScalarCCoef]

end Core3loop
