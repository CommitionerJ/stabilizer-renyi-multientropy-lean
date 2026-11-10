import Core4loop.PhaseAfterA

open scoped BigOperators

namespace Core4loop

noncomputable def squareCompatFun {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (p : PVec n a) (y : YVec n b) (sz : I n) (w : WVec n d) : F :=
  (∑ z : ZVec n c,
    if vecSum z = sz then betaB B p y z w + xiW W p y z w else 0)
  + ∑ z : ZVec n c,
    if vecSum z + 1 = sz then gammaB B p y z w + zetaW W p y z w else 0

noncomputable def squareCompat {n a b c d : ℕ} [NeZero n] :
    (BFun4 n a c d × WFun4 n a b c) →ₗ[F] CFun4 n a b d where
  toFun x := fun p y sz w => squareCompatFun x.1 x.2 p y sz w
  map_add' x x' := by
    funext p y sz w
    unfold squareCompatFun betaB gammaB xiW zetaW
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    calc
      ((∑ z : ZVec n c,
          if vecSum z = sz then
            x.1 p (vecSum y) z w + x'.1 p (vecSum y) z w
              + (x.2 p y z (vecSum w) + x'.2 p y z (vecSum w))
          else 0)
        + ∑ z : ZVec n c,
          if vecSum z + 1 = sz then
            x.1 p (vecSum y + 1) z w + x'.1 p (vecSum y + 1) z w
              + (x.2 p y z (vecSum w + 1) + x'.2 p y z (vecSum w + 1))
          else 0)
          =
          ((∑ z : ZVec n c,
              if vecSum z = sz then
                x.1 p (vecSum y) z w + x.2 p y z (vecSum w)
              else 0)
            + ∑ z : ZVec n c,
              if vecSum z = sz then
                x'.1 p (vecSum y) z w + x'.2 p y z (vecSum w)
              else 0)
          + ((∑ z : ZVec n c,
              if vecSum z + 1 = sz then
                x.1 p (vecSum y + 1) z w + x.2 p y z (vecSum w + 1)
              else 0)
            + ∑ z : ZVec n c,
              if vecSum z + 1 = sz then
                x'.1 p (vecSum y + 1) z w + x'.2 p y z (vecSum w + 1)
              else 0) := by
            congr 1
            · rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro z _
              by_cases h : vecSum z = sz
              · simp [h]
                ring
              · simp [h]
            · rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro z _
              by_cases h : vecSum z + 1 = sz
              · simp [h]
                ring
              · simp [h]
      _ =
          ((∑ z : ZVec n c,
              if vecSum z = sz then
                x.1 p (vecSum y) z w + x.2 p y z (vecSum w)
              else 0) +
            ∑ z : ZVec n c,
              if vecSum z + 1 = sz then
                x.1 p (vecSum y + 1) z w + x.2 p y z (vecSum w + 1)
              else 0) +
          ((∑ z : ZVec n c,
              if vecSum z = sz then
                x'.1 p (vecSum y) z w + x'.2 p y z (vecSum w)
              else 0) +
            ∑ z : ZVec n c,
              if vecSum z + 1 = sz then
                x'.1 p (vecSum y + 1) z w + x'.2 p y z (vecSum w + 1)
              else 0) := by
            ring
  map_smul' r x := by
    funext p y sz w
    unfold squareCompatFun betaB gammaB xiW zetaW
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    calc
      ((∑ z : ZVec n c,
          if vecSum z = sz then
            r * x.1 p (vecSum y) z w + r * x.2 p y z (vecSum w)
          else 0)
        + ∑ z : ZVec n c,
          if vecSum z + 1 = sz then
            r * x.1 p (vecSum y + 1) z w + r * x.2 p y z (vecSum w + 1)
          else 0)
          =
          r * (∑ z : ZVec n c,
            if vecSum z = sz then
              x.1 p (vecSum y) z w + x.2 p y z (vecSum w)
            else 0)
        + r * ∑ z : ZVec n c,
            if vecSum z + 1 = sz then
              x.1 p (vecSum y + 1) z w + x.2 p y z (vecSum w + 1)
            else 0 := by
            congr 1
            · rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro z _
              by_cases h : vecSum z = sz
              · simp [h]
                ring
              · simp [h]
            · rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro z _
              by_cases h : vecSum z + 1 = sz
              · simp [h]
                ring
              · simp [h]
      _ =
          r *
            ((∑ z : ZVec n c,
                if vecSum z = sz then
                  x.1 p (vecSum y) z w + x.2 p y z (vecSum w)
                else 0)
              + ∑ z : ZVec n c,
                if vecSum z + 1 = sz then
                  x.1 p (vecSum y + 1) z w + x.2 p y z (vecSum w + 1)
                else 0) := by
            ring

end Core4loop
