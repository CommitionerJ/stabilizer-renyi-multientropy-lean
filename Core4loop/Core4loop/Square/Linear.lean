import Core4loop.Gauss.SurvivorSum
import Core4loop.Square.CompatCore

open scoped BigOperators

namespace Core4loop

lemma coeffApply_squareCompat_eq_Q2 {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    coeffApply
        (cFun4Equiv n a b d (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
        (cFun4Equiv n a b d C)
      = Q2 B C W := by
  classical
  unfold coeffApply Q2 squareCompat squareCompatFun betaB gammaB deltaC etaC xiW zetaW cFun4Equiv
  simp only
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : I n, ∑ w : WVec n d,
        C p y x w *
          ((∑ z : ZVec n c,
              if vecSum z = x then B p (vecSum y) z w + W p y z (vecSum w) else 0) +
            ∑ z : ZVec n c,
              if vecSum z + 1 = x then
                B p (vecSum y + 1) z w + W p y z (vecSum w + 1)
              else 0))
        =
        ∑ w : WVec n d, ∑ x : I n,
          C p y x w *
            ((∑ z : ZVec n c,
                if vecSum z = x then B p (vecSum y) z w + W p y z (vecSum w) else 0) +
              ∑ z : ZVec n c,
                if vecSum z + 1 = x then
                  B p (vecSum y + 1) z w + W p y z (vecSum w + 1)
                else 0) := by
          exact Finset.sum_comm
    _ = ∑ w : WVec n d, ∑ z : ZVec n c,
        (B p (vecSum y) z w * C p y (vecSum z) w
        + B p (vecSum y + 1) z w * C p y (vecSum z + 1) w
        + C p y (vecSum z) w * W p y z (vecSum w)
        + C p y (vecSum z + 1) w * W p y z (vecSum w + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro w _
          calc
            (∑ x : I n,
              C p y x w *
                ((∑ z : ZVec n c,
                    if vecSum z = x then
                      B p (vecSum y) z w + W p y z (vecSum w)
                    else 0) +
                  ∑ z : ZVec n c,
                    if vecSum z + 1 = x then
                      B p (vecSum y + 1) z w + W p y z (vecSum w + 1)
                    else 0))
              =
              (∑ x : I n,
                C p y x w *
                  ∑ z : ZVec n c,
                    if vecSum z = x then
                      B p (vecSum y) z w + W p y z (vecSum w)
                    else 0)
              + ∑ x : I n,
                C p y x w *
                  ∑ z : ZVec n c,
                    if vecSum z + 1 = x then
                      B p (vecSum y + 1) z w + W p y z (vecSum w + 1)
                    else 0 := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl ?_
                intro x _
                ring
            _ =
              (∑ z : ZVec n c,
                C p y (vecSum z) w * (B p (vecSum y) z w + W p y z (vecSum w)))
              + ∑ z : ZVec n c,
                C p y (vecSum z + 1) w *
                  (B p (vecSum y + 1) z w + W p y z (vecSum w + 1)) := by
                congr 1
                · calc
                    (∑ x : I n,
                        C p y x w *
                          ∑ z : ZVec n c,
                            if vecSum z = x then
                              B p (vecSum y) z w + W p y z (vecSum w)
                            else 0)
                        =
                        ∑ x : I n, ∑ z : ZVec n c,
                          C p y x w *
                            (if vecSum z = x then
                              B p (vecSum y) z w + W p y z (vecSum w)
                            else 0) := by
                          refine Finset.sum_congr rfl ?_
                          intro x _
                          rw [Finset.mul_sum]
                    _ = ∑ z : ZVec n c, ∑ x : I n,
                          C p y x w *
                            (if vecSum z = x then
                              B p (vecSum y) z w + W p y z (vecSum w)
                            else 0) := by
                          exact Finset.sum_comm
                    _ = ∑ z : ZVec n c,
                        C p y (vecSum z) w *
                          (B p (vecSum y) z w + W p y z (vecSum w)) := by
                          refine Finset.sum_congr rfl ?_
                          intro z _
                          rw [Finset.sum_eq_single (vecSum z)]
                          · simp
                          · intro x _ hx
                            simp [hx.symm]
                          · simp
                · calc
                    (∑ x : I n,
                        C p y x w *
                          ∑ z : ZVec n c,
                            if vecSum z + 1 = x then
                              B p (vecSum y + 1) z w + W p y z (vecSum w + 1)
                            else 0)
                        =
                        ∑ x : I n, ∑ z : ZVec n c,
                          C p y x w *
                            (if vecSum z + 1 = x then
                              B p (vecSum y + 1) z w + W p y z (vecSum w + 1)
                            else 0) := by
                          refine Finset.sum_congr rfl ?_
                          intro x _
                          rw [Finset.mul_sum]
                    _ = ∑ z : ZVec n c, ∑ x : I n,
                          C p y x w *
                            (if vecSum z + 1 = x then
                              B p (vecSum y + 1) z w + W p y z (vecSum w + 1)
                            else 0) := by
                          exact Finset.sum_comm
                    _ = ∑ z : ZVec n c,
                        C p y (vecSum z + 1) w *
                          (B p (vecSum y + 1) z w + W p y z (vecSum w + 1)) := by
                          refine Finset.sum_congr rfl ?_
                          intro z _
                          rw [Finset.sum_eq_single (vecSum z + 1)]
                          · simp
                          · intro x _ hx
                            simp [hx.symm]
                          · simp
            _ = ∑ z : ZVec n c,
              (B p (vecSum y) z w * C p y (vecSum z) w
              + B p (vecSum y + 1) z w * C p y (vecSum z + 1) w
              + C p y (vecSum z) w * W p y z (vecSum w)
              + C p y (vecSum z + 1) w * W p y z (vecSum w + 1)) := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl ?_
                intro z _
                ring
    _ = ∑ z : ZVec n c, ∑ w : WVec n d,
        (B p (vecSum y) z w * C p y (vecSum z) w
        + B p (vecSum y + 1) z w * C p y (vecSum z + 1) w
        + C p y (vecSum z) w * W p y z (vecSum w)
        + C p y (vecSum z + 1) w * W p y z (vecSum w + 1)) := by
          exact Finset.sum_comm

lemma square_sum_over_C {n a b c d : ℕ} [NeZero n] [DecidableEq (CFun4 n a b d)]
    (ha : 0 < a) (B : BFun4 n a c d) (W : WFun4 n a b c) :
    (∑ C : CFun4 n a b d, bitSign (Q2 B C W)) =
      if squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0 then
        (2 : ℤ) ^ (n ^ (a + b + d))
      else 0 := by
  classical
  let e := cFun4Equiv n a b d
  let coeff :=
    e (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W))
  have hsum :
      (∑ C : CFun4 n a b d, bitSign (Q2 B C W)) =
        signedCoeffSum coeff := by
    unfold signedCoeffSum coeffApply
    calc
      (∑ C : CFun4 n a b d, bitSign (Q2 B C W))
          = ∑ C : CFun4 n a b d, bitSign (coeffApply coeff (e C)) := by
              refine Finset.sum_congr rfl ?_
              intro C _
              rw [coeffApply_squareCompat_eq_Q2]
      _ = ∑ f : PVec n a × YVec n b × I n × WVec n d → F,
            bitSign (∑ i : PVec n a × YVec n b × I n × WVec n d, f i * coeff i) := by
              exact Fintype.sum_equiv e
                (fun C : CFun4 n a b d => bitSign (coeffApply coeff (e C)))
                (fun f : PVec n a × YVec n b × I n × WVec n d → F =>
                  bitSign (∑ i : PVec n a × YVec n b × I n × WVec n d, f i * coeff i))
                (fun C => by rfl)
  rw [hsum, signedCoeffSum_formula]
  by_cases h : squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0
  · have hcoeff : coeff = 0 := by
      funext i
      rcases i with ⟨p, y, sz, w⟩
      simp [coeff, e, h, cFun4Equiv]
    rw [if_pos hcoeff, if_pos h]
    rw [card_CIndex4 ha]
  · have hcoeff : coeff ≠ 0 := by
      intro hcoeff
      apply h
      apply (cFun4Equiv n a b d).injective
      funext i
      rcases i with ⟨p, y, sz, w⟩
      simpa [coeff, e, cFun4Equiv] using congrFun hcoeff (p, y, sz, w)
    rw [if_neg hcoeff, if_neg h]

end Core4loop
