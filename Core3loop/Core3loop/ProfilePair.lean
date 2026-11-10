import Core3loop.PhaseReduction
import Core3loop.Symplectic

open scoped BigOperators

namespace Core3loop

noncomputable def bFieldEquivBCoefABC {a c n : ℕ} [NeZero n] :
    BFieldABC a c n ≃ BCoefABC a c n where
  toFun := fun B t z x => B (x, t, z)
  invFun := fun bcoef u => bcoef u.2.1 u.2.2 u.1
  left_inv := by
    intro B
    funext u
    rcases u with ⟨x, t, z⟩
    rfl
  right_inv := by
    intro bcoef
    rfl

noncomputable def cFieldEquivCCoefABC {a b n : ℕ} [NeZero n] :
    CFieldABC a b n ≃ CCoefABC a b n where
  toFun := fun C y r x => C (x, y, r)
  invFun := fun ccoef u => ccoef u.2.1 u.2.2 u.1
  left_inv := by
    intro C
    funext u
    rcases u with ⟨x, y, r⟩
    rfl
  right_inv := by
    intro ccoef
    rfl

noncomputable def qLeftProfileABC {a b c n : ℕ} [NeZero n]
    (bcoef : BCoefABC a c n) (ccoef : CCoefABC a b n) : F :=
  ∑ y : YCoord b n, ∑ z : ZCoord c n,
    dotProfile (a := a) (n := n) (bcoef (sumY y) z) (ccoef y (sumZ z))

noncomputable def qRightProfileABC {a b c n : ℕ} [NeZero n]
    (bcoef : BCoefABC a c n) (ccoef : CCoefABC a b n) : F :=
  ∑ y : YCoord b n, ∑ z : ZCoord c n,
    dotProfile (a := a) (n := n) (bcoef (sumY y + 1) z) (ccoef y (sumZ z + 1))

noncomputable def qProfileABC {a b c n : ℕ} [NeZero n]
    (bcoef : BCoefABC a c n) (ccoef : CCoefABC a b n) : F :=
  qLeftProfileABC (a := a) (b := b) (c := c) (n := n) bcoef ccoef +
    qRightProfileABC (a := a) (b := b) (c := c) (n := n) bcoef ccoef

lemma QpairABC_eq_qProfileABC {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) :
    QpairABC (a := a) (b := b) (c := c) (n := n) B C =
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        (bFieldEquivBCoefABC (a := a) (c := c) (n := n) B)
        (cFieldEquivCCoefABC (a := a) (b := b) (n := n) C) := by
  let bcoef := bFieldEquivBCoefABC (a := a) (c := c) (n := n) B
  let ccoef := cFieldEquivCCoefABC (a := a) (b := b) (n := n) C
  unfold QpairABC qProfileABC qLeftProfileABC qRightProfileABC
  calc
    ∑ u : Site a b c n, pairBC_abc (a := a) (b := b) (c := c) (n := n) B C u
      =
        ∑ yz : YCoord b n × ZCoord c n,
          ∑ x : XCoord a n,
            pairBC_abc (a := a) (b := b) (c := c) (n := n) B C (x, yz.1, yz.2) := by
              simpa [Site] using
                (Fintype.sum_prod_type_right
                  (f := fun u : XCoord a n × (YCoord b n × ZCoord c n) =>
                    pairBC_abc (a := a) (b := b) (c := c) (n := n) B C
                      (u.1, u.2.1, u.2.2)))
    _ =
      ∑ y : YCoord b n, ∑ z : ZCoord c n,
        ∑ x : XCoord a n,
          pairBC_abc (a := a) (b := b) (c := c) (n := n) B C (x, y, z) := by
            rw [Fintype.sum_prod_type]
    _ =
      ∑ y : YCoord b n, ∑ z : ZCoord c n,
        ((∑ x : XCoord a n, B (x, sumY y, z) * C (x, y, sumZ z)) +
          ∑ x : XCoord a n, B (x, sumY y + 1, z) * C (x, y, sumZ z + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            refine Finset.sum_congr rfl ?_
            intro z hz
            simp [pairBC_abc, Finset.sum_add_distrib]
    _ =
      ∑ y : YCoord b n, ∑ z : ZCoord c n,
        (dotProfile (a := a) (n := n) (bcoef (sumY y) z) (ccoef y (sumZ z)) +
          dotProfile (a := a) (n := n) (bcoef (sumY y + 1) z) (ccoef y (sumZ z + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            refine Finset.sum_congr rfl ?_
            intro z hz
            change
              (∑ x : XCoord a n, B (x, sumY y, z) * C (x, y, sumZ z)) +
                ∑ x : XCoord a n, B (x, sumY y + 1, z) * C (x, y, sumZ z + 1) =
              (∑ x : XCoord a n, B (x, sumY y, z) * C (x, y, sumZ z)) +
                ∑ x : XCoord a n, B (x, sumY y + 1, z) * C (x, y, sumZ z + 1)
            rfl
    _ =
      (∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n) (bcoef (sumY y) z) (ccoef y (sumZ z))) +
        ∑ y : YCoord b n, ∑ z : ZCoord c n,
          dotProfile (a := a) (n := n) (bcoef (sumY y + 1) z) (ccoef y (sumZ z + 1)) := by
            simp_rw [Finset.sum_add_distrib]
    _ = qProfileABC (a := a) (b := b) (c := c) (n := n) bcoef ccoef := by
          rfl

end Core3loop
