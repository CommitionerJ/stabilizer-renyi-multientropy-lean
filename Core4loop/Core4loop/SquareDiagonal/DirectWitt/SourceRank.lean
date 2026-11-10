import Core4loop.RootSpaces.KRange
import Core4loop.SquareDiagonal.PreC.Reduction
import Core4loop.NormalFormDims
import Core4loop.SquareDiagonal.EvenP.SourceSplit

open scoped BigOperators

namespace Core4loop

attribute [local instance] Fintype.ofFinite

namespace DiamondSourceRank

noncomputable section

open SquareDiagonal.EvenP

/-- A positive block is coordinatized by its tail and its total sum. -/
private def vecTailSumEquiv
    (n k : ℕ) [NeZero n] (hk : 0 < k) :
    Vec n k ≃ PVec n k × I n := by
  cases k with
  | zero => omega
  | succ k =>
      exact
        { toFun := fun v => (vecTail v, vecSum v)
          invFun := fun q => vecCons (q.2 - vecSum q.1) q.1
          left_inv := by
            intro v
            have hsum := vecSum_vecCons (v 0) (vecTail v)
            rw [vecCons_head_tail v] at hsum
            have hhead : vecSum v - vecSum (vecTail v) = v 0 := by
              rw [hsum]
              exact add_sub_cancel_right _ _
            change
              vecCons (vecSum v - vecSum (vecTail v)) (vecTail v) = v
            rw [hhead]
            exact vecCons_head_tail v
          right_inv := by
            intro q
            rcases q with ⟨p, s⟩
            apply Prod.ext
            · change vecTail (vecCons (s - vecSum p) p) = p
              exact vecTail_vecCons _ _
            · change
                vecSum (vecCons (s - vecSum p) p) = s
              rw [vecSum_vecCons]
              exact sub_add_cancel _ _ }

@[simp]
private theorem vecTailSumEquiv_apply_snd
    {n k : ℕ} [NeZero n] (hk : 0 < k) (v : Vec n k) :
    (vecTailSumEquiv n k hk v).2 = vecSum v := by
  cases k with
  | zero => omega
  | succ k => rfl

@[simp]
private theorem vecTailSumEquiv_symm_sum
    {n k : ℕ} [NeZero n] (hk : 0 < k) (p : PVec n k) (s : I n) :
    vecSum ((vecTailSumEquiv n k hk).symm (p, s)) = s := by
  cases k with
  | zero => omega
  | succ k =>
      change vecSum (vecCons (s - vecSum p) p) = s
      rw [vecSum_vecCons]
      exact sub_add_cancel _ _

private theorem sum_vec_fiber_eq_sum_tail
    {n k : ℕ} [NeZero n] (hk : 0 < k)
    (s : I n) (f : Vec n k → F) :
    (∑ v : Vec n k, if vecSum v = s then f v else 0) =
      ∑ p : PVec n k, f ((vecTailSumEquiv n k hk).symm (p, s)) := by
  classical
  let e := vecTailSumEquiv n k hk
  calc
    (∑ v : Vec n k, if vecSum v = s then f v else 0) =
        ∑ q : PVec n k × I n,
          if q.2 = s then f (e.symm q) else 0 := by
            exact Fintype.sum_equiv e
              (fun v : Vec n k => if vecSum v = s then f v else 0)
              (fun q : PVec n k × I n =>
                if q.2 = s then f (e.symm q) else 0)
              (fun v => by
                change
                  (if vecSum v = s then f v else 0) =
                    if (e v).2 = s then f (e.symm (e v)) else 0
                rw [show (e v).2 = vecSum v by
                  exact vecTailSumEquiv_apply_snd hk v]
                rw [e.symm_apply_apply])
    _ = ∑ p : PVec n k, ∑ t : I n,
          if t = s then f (e.symm (p, t)) else 0 := by
            rw [Fintype.sum_prod_type]
    _ = ∑ p : PVec n k, f (e.symm (p, s)) := by
            refine Finset.sum_congr rfl ?_
            intro p _
            simp

private theorem sum_vec_add_one_fiber_eq_sum_tail
    {n k : ℕ} [NeZero n] (hk : 0 < k)
    (s : I n) (f : Vec n k → F) :
    (∑ v : Vec n k, if vecSum v + 1 = s then f v else 0) =
      ∑ p : PVec n k,
        f ((vecTailSumEquiv n k hk).symm (p, s - 1)) := by
  have h := sum_vec_fiber_eq_sum_tail hk (s - 1) f
  calc
    (∑ v : Vec n k, if vecSum v + 1 = s then f v else 0) =
        ∑ v : Vec n k, if vecSum v = s - 1 then f v else 0 := by
          refine Finset.sum_congr rfl ?_
          intro v _
          congr 1
          exact propext
            (@eq_sub_iff_add_eq (I n) _ (vecSum v) s (1 : I n)).symm
    _ = _ := h

/-- Coefficient coordinates for `C` as the rotated root coordinates.

The shear records the original `C` scalar as
`s = -sum(yA) - sum(zB) - sum(w)`.  This is the convention for which all
three cyclic directions of the rotated `K_yzw` move the source fibre in the
same direction. -/
private noncomputable def coeffRootEquiv
    {n a b d : ℕ} [NeZero n] (ha : 0 < a) :
    CFun4 n a b d ≃ₗ[F] RootTarget n a b d := by
  let eA := vecTailSumEquiv n a ha
  exact
    { toFun := fun C yA zB w =>
        C (eA yA).1 zB (-((eA yA).2 + vecSum zB + vecSum w)) w
      invFun := fun R p y s w =>
        R (eA.symm (p, -(s + vecSum y + vecSum w))) y w
      left_inv := by
        intro C
        funext p y s w
        have he :
            eA (eA.symm (p, -(s + vecSum y + vecSum w))) =
              (p, -(s + vecSum y + vecSum w)) :=
          eA.apply_symm_apply _
        change
          C
              (eA (eA.symm (p, -(s + vecSum y + vecSum w)))).1 y
              (-((eA (eA.symm (p, -(s + vecSum y + vecSum w)))).2
                + vecSum y + vecSum w)) w =
            C p y s w
        rw [he]
        congr 1
        ring
      right_inv := by
        intro R
        funext yA zB w
        have he : eA.symm (eA yA) = yA := eA.symm_apply_apply yA
        change
          R
              (eA.symm
                ((eA yA).1,
                  -(-((eA yA).2 + vecSum zB + vecSum w)
                    + vecSum zB + vecSum w))) zB w =
            R yA zB w
        have hs :
            -(-((eA yA).2 + vecSum zB + vecSum w)
                + vecSum zB + vecSum w) =
              (eA yA).2 := by ring
        rw [hs]
        exact congrArg (fun y => R y zB w) he
      map_add' := by
        intro C C'
        funext yA zB w
        rfl
      map_smul' := by
        intro r C
        funext yA zB w
        rfl }

private noncomputable def sourceAReindexEquiv
    {n b c d : ℕ} [NeZero n] (hc : 0 < c) :
    AFun4 n b c d ≃ₗ[F] BFun4 n c b d := by
  let eC := vecTailSumEquiv n c hc
  exact
    { toFun := fun A pC i zB w =>
        A zB (eC.symm (pC, -(i + vecSum zB + vecSum w))) w
      invFun := fun B y z w =>
        B (eC z).1 (-((eC z).2 + vecSum y + vecSum w)) y w
      left_inv := by
        intro A
        funext y z w
        have he : eC.symm (eC z) = z := eC.symm_apply_apply z
        change
          A y
              (eC.symm
                ((eC z).1,
                  -(-((eC z).2 + vecSum y + vecSum w)
                    + vecSum y + vecSum w))) w =
            A y z w
        have hs :
            -(-((eC z).2 + vecSum y + vecSum w)
                + vecSum y + vecSum w) =
              (eC z).2 := by ring
        rw [hs]
        exact congrArg (fun z => A y z w) he
      right_inv := by
        intro B
        funext pC i zB w
        have he :
            eC (eC.symm (pC, -(i + vecSum zB + vecSum w))) =
              (pC, -(i + vecSum zB + vecSum w)) :=
          eC.apply_symm_apply _
        change
          B
              (eC (eC.symm (pC, -(i + vecSum zB + vecSum w)))).1
              (-((eC (eC.symm (pC, -(i + vecSum zB + vecSum w)))).2
                + vecSum zB + vecSum w)) zB w =
            B pC i zB w
        rw [he]
        congr 1
        ring
      map_add' := by
        intro A A'
        funext pC i zB w
        rfl
      map_smul' := by
        intro r A
        funext pC i zB w
        rfl }

private noncomputable def sourceBReindexEquiv
    {n a c d : ℕ} [NeZero n] (ha : 0 < a) (hc : 0 < c) :
    BFun4 n a c d ≃ₗ[F] CFun4 n c a d := by
  let eA := vecTailSumEquiv n a ha
  let eC := vecTailSumEquiv n c hc
  exact
    { toFun := fun B pC yA j w =>
        B (eA yA).1 j
          (eC.symm (pC, -((eA yA).2 + j + vecSum w))) w
      invFun := fun C p j z w =>
        C (eC z).1
          (eA.symm (p, -((eC z).2 + j + vecSum w))) j w
      left_inv := by
        intro B
        funext p j z w
        have heC : eC.symm (eC z) = z := eC.symm_apply_apply z
        have heA :
            eA
                (eA.symm (p, -((eC z).2 + j + vecSum w))) =
              (p, -((eC z).2 + j + vecSum w)) :=
          eA.apply_symm_apply _
        change
          B
              (eA (eA.symm (p, -((eC z).2 + j + vecSum w)))).1 j
              (eC.symm
                ((eC z).1,
                  -((eA (eA.symm
                    (p, -((eC z).2 + j + vecSum w)))).2
                    + j + vecSum w))) w =
            B p j z w
        rw [heA]
        have hs :
            -(-((eC z).2 + j + vecSum w) + j + vecSum w) =
              (eC z).2 := by ring
        rw [hs]
        exact congrArg (fun z => B p j z w) heC
      right_inv := by
        intro C
        funext pC yA j w
        have heA : eA.symm (eA yA) = yA := eA.symm_apply_apply yA
        have heC :
            eC
                (eC.symm (pC, -((eA yA).2 + j + vecSum w))) =
              (pC, -((eA yA).2 + j + vecSum w)) :=
          eC.apply_symm_apply _
        change
          C
              (eC
                (eC.symm (pC, -((eA yA).2 + j + vecSum w)))).1
              (eA.symm
                ((eA yA).1,
                  -((eC
                    (eC.symm
                      (pC, -((eA yA).2 + j + vecSum w)))).2
                    + j + vecSum w))) j w =
            C pC yA j w
        rw [heC]
        have hs :
            -(-((eA yA).2 + j + vecSum w) + j + vecSum w) =
              (eA yA).2 := by ring
        rw [hs]
        exact congrArg (fun y => C pC y j w) heA
      map_add' := by
        intro B B'
        funext pC yA j w
        rfl
      map_smul' := by
        intro r B
        funext pC yA j w
        rfl }

private noncomputable def sourceWReindexEquiv
    {n a b c : ℕ} [NeZero n] (ha : 0 < a) (hc : 0 < c) :
    WFun4 n a b c ≃ₗ[F] WFun4 n c a b := by
  let eA := vecTailSumEquiv n a ha
  let eC := vecTailSumEquiv n c hc
  exact
    { toFun := fun W pC yA zB k =>
        W (eA yA).1 zB
          (eC.symm (pC, -((eA yA).2 + vecSum zB + k))) k
      invFun := fun X p y z k =>
        X (eC z).1
          (eA.symm (p, -((eC z).2 + vecSum y + k))) y k
      left_inv := by
        intro W
        funext p y z k
        have heC : eC.symm (eC z) = z := eC.symm_apply_apply z
        have heA :
            eA
                (eA.symm (p, -((eC z).2 + vecSum y + k))) =
              (p, -((eC z).2 + vecSum y + k)) :=
          eA.apply_symm_apply _
        change
          W
              (eA (eA.symm (p, -((eC z).2 + vecSum y + k)))).1 y
              (eC.symm
                ((eC z).1,
                  -((eA
                    (eA.symm (p, -((eC z).2 + vecSum y + k)))).2
                    + vecSum y + k))) k =
            W p y z k
        rw [heA]
        have hs :
            -(-((eC z).2 + vecSum y + k) + vecSum y + k) =
              (eC z).2 := by ring
        rw [hs]
        exact congrArg (fun z => W p y z k) heC
      right_inv := by
        intro X
        funext pC yA zB k
        have heA : eA.symm (eA yA) = yA := eA.symm_apply_apply yA
        have heC :
            eC
                (eC.symm
                  (pC, -((eA yA).2 + vecSum zB + k))) =
              (pC, -((eA yA).2 + vecSum zB + k)) :=
          eC.apply_symm_apply _
        change
          X
              (eC
                (eC.symm
                  (pC, -((eA yA).2 + vecSum zB + k)))).1
              (eA.symm
                ((eA yA).1,
                  -((eC
                    (eC.symm
                      (pC, -((eA yA).2 + vecSum zB + k)))).2
                    + vecSum zB + k))) zB k =
            X pC yA zB k
        rw [heC]
        have hs :
            -(-((eA yA).2 + vecSum zB + k) + vecSum zB + k) =
              (eA yA).2 := by ring
        rw [hs]
        exact congrArg (fun y => X pC y zB k) heA
      map_add' := by
        intro W W'
        funext pC yA zB k
        rfl
      map_smul' := by
        intro r W
        funext pC yA zB k
        rfl }

private noncomputable def sourceReindexEquiv
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hc : 0 < c) :
    (AFun4 n b c d × BFun4 n a c d × WFun4 n a b c) ≃ₗ[F]
      (BFun4 n c b d × CFun4 n c a d × WFun4 n c a b) where
  toFun x :=
    (sourceAReindexEquiv (n := n) (b := b) (c := c) (d := d) hc x.1,
      sourceBReindexEquiv
        (n := n) (a := a) (c := c) (d := d) ha hc x.2.1,
      sourceWReindexEquiv
        (n := n) (a := a) (b := b) (c := c) ha hc x.2.2)
  invFun x :=
    ((sourceAReindexEquiv
        (n := n) (b := b) (c := c) (d := d) hc).symm x.1,
      (sourceBReindexEquiv
        (n := n) (a := a) (c := c) (d := d) ha hc).symm x.2.1,
      (sourceWReindexEquiv
        (n := n) (a := a) (b := b) (c := c) ha hc).symm x.2.2)
  left_inv := by
    intro x
    apply Prod.ext
    · exact
        (sourceAReindexEquiv
          (n := n) (b := b) (c := c) (d := d) hc).symm_apply_apply x.1
    · apply Prod.ext
      · exact
          (sourceBReindexEquiv
            (n := n) (a := a) (c := c) (d := d)
            ha hc).symm_apply_apply x.2.1
      · exact
          (sourceWReindexEquiv
            (n := n) (a := a) (b := b) (c := c)
            ha hc).symm_apply_apply x.2.2
  right_inv := by
    intro x
    apply Prod.ext
    · exact
        (sourceAReindexEquiv
          (n := n) (b := b) (c := c) (d := d) hc).apply_symm_apply x.1
    · apply Prod.ext
      · exact
          (sourceBReindexEquiv
            (n := n) (a := a) (c := c) (d := d)
            ha hc).apply_symm_apply x.2.1
      · exact
          (sourceWReindexEquiv
            (n := n) (a := a) (b := b) (c := c)
            ha hc).apply_symm_apply x.2.2
  map_add' := by
    intro x x'
    apply Prod.ext
    · exact
        (sourceAReindexEquiv
          (n := n) (b := b) (c := c) (d := d) hc).map_add _ _
    · apply Prod.ext
      · exact
          (sourceBReindexEquiv
            (n := n) (a := a) (c := c) (d := d) ha hc).map_add _ _
      · exact
          (sourceWReindexEquiv
            (n := n) (a := a) (b := b) (c := c) ha hc).map_add _ _
  map_smul' := by
    intro r x
    apply Prod.ext
    · exact
        (sourceAReindexEquiv
          (n := n) (b := b) (c := c) (d := d) hc).map_smul _ _
    · apply Prod.ext
      · exact
          (sourceBReindexEquiv
            (n := n) (a := a) (c := c) (d := d) ha hc).map_smul _ _
      · exact
          (sourceWReindexEquiv
            (n := n) (a := a) (b := b) (c := c) ha hc).map_smul _ _

@[simp]
private theorem sourceAReindexEquiv_apply
    {n b c d : ℕ} [NeZero n] (hc : 0 < c)
    (A : AFun4 n b c d) (p : PVec n c) (i : I n)
    (z : ZVec n b) (w : WVec n d) :
    sourceAReindexEquiv (n := n) (b := b) (c := c) (d := d) hc A p i z w =
      A z
        ((vecTailSumEquiv n c hc).symm
          (p, -(i + vecSum z + vecSum w))) w := rfl

@[simp]
private theorem sourceBReindexEquiv_apply
    {n a c d : ℕ} [NeZero n] (ha : 0 < a) (hc : 0 < c)
    (B : BFun4 n a c d) (p : PVec n c) (y : YVec n a)
    (j : I n) (w : WVec n d) :
    sourceBReindexEquiv (n := n) (a := a) (c := c) (d := d)
        ha hc B p y j w =
      B (vecTailSumEquiv n a ha y).1 j
        ((vecTailSumEquiv n c hc).symm
          (p, -((vecTailSumEquiv n a ha y).2 + j + vecSum w))) w := rfl

@[simp]
private theorem sourceWReindexEquiv_apply
    {n a b c : ℕ} [NeZero n] (ha : 0 < a) (hc : 0 < c)
    (W : WFun4 n a b c) (p : PVec n c) (y : YVec n a)
    (z : ZVec n b) (k : I n) :
    sourceWReindexEquiv (n := n) (a := a) (b := b) (c := c)
        ha hc W p y z k =
      W (vecTailSumEquiv n a ha y).1 z
        ((vecTailSumEquiv n c hc).symm
          (p, -((vecTailSumEquiv n a ha y).2 + vecSum z + k))) k := rfl

/-
/-- The literal coefficient of a `C` coordinate contributed by the `A`
part of the pre-`C` source. -/
private noncomputable def diamondAConstraint
    {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) : CFun4 n a b d :=
  fun _p y s w =>
    (∑ z : ZVec n c, if vecSum z = s then A y z w else 0) +
      ∑ z : ZVec n c, if vecSum z + 1 = s then A y z w else 0

set_option maxHeartbeats 2000000 in
private theorem diamondAConstraint_pairing_eq
    {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (C : CFun4 n a b d) :
    coeffApply
        (cFun4Equiv n a b d
          (diamondAConstraint
            (n := n) (a := a) (b := b) (c := c) (d := d) A))
        (cFun4Equiv n a b d C) =
      coeffApplyA
        (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) A := by
  classical
  unfold coeffApply coeffApplyA diamondAConstraint KCMap dzC deltaC etaC
    cFun4Equiv aFun4Equiv
  simp_rw [Fintype.sum_prod_type]
  calc
    (∑ p : PVec n a, ∑ y : YVec n b, ∑ x : I n, ∑ w : WVec n d,
        ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0) +
          ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0) *
            C p y x w) =
      ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro y _
          calc
            (∑ x : I n, ∑ w : WVec n d,
                ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0) +
                  ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0) *
                    C p y x w) =
              ∑ w : WVec n d, ∑ x : I n,
                C p y x w *
                  ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0) +
                    ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0) := by
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl ?_
                      intro w _
                      refine Finset.sum_congr rfl ?_
                      intro x _
                      ring
            _ = ∑ w : WVec n d, ∑ z : ZVec n c,
                (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
                  refine Finset.sum_congr rfl ?_
                  intro w _
                  calc
                    (∑ x : I n,
                        C p y x w *
                          ((∑ z : ZVec n c,
                              if vecSum z = x then A y z w else 0) +
                            ∑ z : ZVec n c,
                              if vecSum z + 1 = x then A y z w else 0)) =
                      (∑ x : I n,
                        C p y x w *
                          ∑ z : ZVec n c,
                            if vecSum z = x then A y z w else 0) +
                      ∑ x : I n,
                        C p y x w *
                          ∑ z : ZVec n c,
                            if vecSum z + 1 = x then A y z w else 0 := by
                              rw [← Finset.sum_add_distrib]
                              refine Finset.sum_congr rfl ?_
                              intro x _
                              ring
                    _ =
                      (∑ z : ZVec n c, C p y (vecSum z) w * A y z w) +
                      ∑ z : ZVec n c,
                        C p y (vecSum z + 1) w * A y z w := by
                          congr 1
                          · calc
                              (∑ x : I n,
                                  C p y x w *
                                    ∑ z : ZVec n c,
                                      if vecSum z = x then A y z w else 0) =
                                ∑ z : ZVec n c, ∑ x : I n,
                                  C p y x w *
                                    (if vecSum z = x then A y z w else 0) := by
                                      rw [Finset.sum_comm]
                                      refine Finset.sum_congr rfl ?_
                                      intro z _
                                      rw [Finset.mul_sum]
                              _ = _ := by
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
                                      if vecSum z + 1 = x then A y z w else 0) =
                                ∑ z : ZVec n c, ∑ x : I n,
                                  C p y x w *
                                    (if vecSum z + 1 = x then A y z w else 0) := by
                                      rw [Finset.sum_comm]
                                      refine Finset.sum_congr rfl ?_
                                      intro z _
                                      rw [Finset.mul_sum]
                              _ = _ := by
                                refine Finset.sum_congr rfl ?_
                                intro z _
                                rw [Finset.sum_eq_single (vecSum z + 1)]
                                · simp
                                · intro x _ hx
                                  simp [hx.symm]
                                · simp
                    _ = _ := by
                      rw [← Finset.sum_add_distrib]
                      refine Finset.sum_congr rfl ?_
                      intro z _
                      ring
            _ = _ := Finset.sum_comm
    _ = ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        (∑ p : PVec n a,
          (C p y (vecSum z) w + C p y (vecSum z + 1) w)) * A y z w := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro w _
          rw [← Finset.sum_mul]
-/

set_option maxHeartbeats 2000000 in
-- Normalizing the six finite fibre sums requires a larger bounded tactic
-- budget than the repository default.
private theorem rotated_K_yzw_apply_eq_constraint
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c)
    (yA : YVec n a) (zB : ZVec n b) (w : WVec n d) :
    K_yzw
        (n := n) (a := c) (b := a) (c := b) (d := d)
        (sourceReindexEquiv ha hc (A, B, W)) yA zB w =
      diamondEvenPAConstraint
          (n := n) (a := a) (b := b) (c := c) (d := d) A
          (vecTailSumEquiv n a ha yA).1 zB
          (-((vecTailSumEquiv n a ha yA).2 + vecSum zB + vecSum w)) w +
        squareCompat
          (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)
          (vecTailSumEquiv n a ha yA).1 zB
          (-((vecTailSumEquiv n a ha yA).2 + vecSum zB + vecSum w)) w := by
  let s : I n :=
    -((vecTailSumEquiv n a ha yA).2 + vecSum zB + vecSum w)
  rw [show
    diamondEvenPAConstraint
          (n := n) (a := a) (b := b) (c := c) (d := d) A
          (vecTailSumEquiv n a ha yA).1 zB s w =
      (∑ v : ZVec n c, if vecSum v = s then A zB v w else 0) +
        ∑ v : ZVec n c, if vecSum v + 1 = s then A zB v w else 0 by
          rfl]
  rw [show
    squareCompat
          (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)
          (vecTailSumEquiv n a ha yA).1 zB s w =
      (∑ v : ZVec n c,
        if vecSum v = s then
          B (vecTailSumEquiv n a ha yA).1 (vecSum zB) v w +
            W (vecTailSumEquiv n a ha yA).1 zB v (vecSum w)
        else 0) +
      ∑ v : ZVec n c,
        if vecSum v + 1 = s then
          B (vecTailSumEquiv n a ha yA).1 (vecSum zB + 1) v w +
            W (vecTailSumEquiv n a ha yA).1 zB v (vecSum w + 1)
        else 0 by
          rfl]
  rw [sum_vec_fiber_eq_sum_tail hc s (fun v => A zB v w)]
  rw [sum_vec_add_one_fiber_eq_sum_tail hc s (fun v => A zB v w)]
  rw [sum_vec_fiber_eq_sum_tail hc s
    (fun v =>
      B (vecTailSumEquiv n a ha yA).1 (vecSum zB) v w +
        W (vecTailSumEquiv n a ha yA).1 zB v (vecSum w))]
  rw [sum_vec_add_one_fiber_eq_sum_tail hc s
    (fun v =>
      B (vecTailSumEquiv n a ha yA).1 (vecSum zB + 1) v w +
        W (vecTailSumEquiv n a ha yA).1 zB v (vecSum w + 1))]
  change
    (∑ p : PVec n c,
      (dyB
          (sourceAReindexEquiv
            (n := n) (b := b) (c := c) (d := d) hc A)
          p yA zB w +
        dzC
          (sourceBReindexEquiv
            (n := n) (a := a) (c := c) (d := d) ha hc B)
          p yA zB w +
        dwW
          (sourceWReindexEquiv
            (n := n) (a := a) (b := b) (c := c) ha hc W)
          p yA zB w)) = _
  unfold dyB dzC dwW betaB gammaB deltaC etaC xiW zetaW
  simp only [sourceAReindexEquiv_apply, sourceBReindexEquiv_apply,
    sourceWReindexEquiv_apply]
  repeat' rw [Finset.sum_add_distrib]
  dsimp [s]
  simp only [vecTailSumEquiv_apply_snd]
  apply Eq.symm
  ring_nf

/-
set_option maxHeartbeats 2000000 in
private theorem diamondCPhaseCoeffClean_eq_constraint_pairing
    {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) (C : CFun4 n a b d) :
    diamondCPhaseCoeffClean A B W C =
      coeffApply
        (cFun4Equiv n a b d
          (diamondAConstraint
              (n := n) (a := a) (b := b) (c := c) (d := d) A +
            squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
        (cFun4Equiv n a b d C) := by
  rw [show
    diamondCPhaseCoeffClean A B W C =
      coeffApplyA
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) A +
        coeffApply
          (cFun4Equiv n a b d
            (squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
          (cFun4Equiv n a b d C) by
            rfl]
  rw [← diamondAConstraint_pairing_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) A C]
  unfold coeffApply cFun4Equiv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rcases i with ⟨p, y, s, w⟩
  simp only [Pi.add_apply]
  ring

private theorem diamondPreCMap_eq_zero_iff_constraint
    {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) :
    diamondPreCMap
        (n := n) (a := a) (b := b) (c := c) (d := d) (A, B, W) = 0 ↔
      diamondAConstraint
          (n := n) (a := a) (b := b) (c := c) (d := d) A +
        squareCompat
          (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0 := by
  classical
  constructor
  · intro h
    funext p y s w
    let i0 : PVec n a × YVec n b × I n × WVec n d := (p, y, s, w)
    let C0 : CFun4 n a b d :=
      fun p' y' s' w' => if (p', y', s', w') = i0 then 1 else 0
    have happ :=
      congrArg (fun L : CFun4 n a b d →ₗ[F] F => L C0) h
    change diamondCPhaseCoeffClean A B W C0 = 0 at happ
    rw [diamondCPhaseCoeffClean_eq_constraint_pairing A B W C0] at happ
    change
      (∑ i : PVec n a × YVec n b × I n × WVec n d,
        (diamondAConstraint
              (n := n) (a := a) (b := b) (c := c) (d := d) A +
            squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d) (B, W))
            i.1 i.2.1 i.2.2.1 i.2.2.2 *
          (if i = i0 then 1 else 0)) = 0 at happ
    simpa [i0] using happ
  · intro h
    apply LinearMap.ext
    intro C
    change diamondCPhaseCoeffClean A B W C = 0
    rw [diamondCPhaseCoeffClean_eq_constraint_pairing A B W C]
    simp [h, coeffApply, cFun4Equiv]
-/

private theorem diamondPreCMap_eq_zero_iff_rotated_K_yzw_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) :
    diamondPreCMap
        (n := n) (a := a) (b := b) (c := c) (d := d) (A, B, W) = 0 ↔
    K_yzw
        (n := n) (a := c) (b := a) (c := b) (d := d)
        (sourceReindexEquiv ha hc (A, B, W)) = 0 := by
  rw [SquareDiagonal.EvenP.diamondPreCMap_eq_zero_iff_constraint]
  constructor
  · intro h
    funext yA zB w
    rw [rotated_K_yzw_apply_eq_constraint ha hc A B W yA zB w]
    rw [h]
    exact F_add_self _
  · intro h
    funext p y s w
    let yA : YVec n a :=
      (vecTailSumEquiv n a ha).symm
        (p, -(s + vecSum y + vecSum w))
    have he :
        vecTailSumEquiv n a ha yA =
          (p, -(s + vecSum y + vecSum w)) := by
      exact (vecTailSumEquiv n a ha).apply_symm_apply _
    have hs :
        -((vecTailSumEquiv n a ha yA).2 + vecSum y + vecSum w) = s := by
      rw [he]
      ring
    have happ := congrFun (congrFun (congrFun h yA) y) w
    simp only [Pi.zero_apply] at happ
    rw [rotated_K_yzw_apply_eq_constraint ha hc A B W yA y w] at happ
    rw [he] at happ
    change
      diamondEvenPAConstraint
          (n := n) (a := a) (b := b) (c := c) (d := d) A p y
            (-(-(s + vecSum y + vecSum w) + vecSum y + vecSum w)) w +
        squareCompat
          (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) p y
            (-(-(s + vecSum y + vecSum w) + vecSum y + vecSum w)) w = 0 at happ
    have hs' :
        -(-(s + vecSum y + vecSum w) + vecSum y + vecSum w) = s := by
      ring
    rw [hs'] at happ
    exact (add_eq_zero_iff_eq_of_F_module _ _).mp happ

private noncomputable def diamondPreCKernelEquivKYZW
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) :
    LinearMap.ker
        (diamondPreCMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≃ₗ[F]
      LinearMap.ker
        (K_yzw
          (n := n) (a := c) (b := a) (c := b) (d := d)) where
  toFun x :=
    ⟨sourceReindexEquiv ha hc x.1, by
      apply LinearMap.mem_ker.mpr
      apply
        (diamondPreCMap_eq_zero_iff_rotated_K_yzw_eq_zero
          ha hc x.1.1 x.1.2.1 x.1.2.2).mp
      exact LinearMap.mem_ker.mp x.2⟩
  invFun y :=
    ⟨(sourceReindexEquiv ha hc).symm y.1, by
      apply LinearMap.mem_ker.mpr
      apply
        (diamondPreCMap_eq_zero_iff_rotated_K_yzw_eq_zero
          ha hc
          ((sourceReindexEquiv ha hc).symm y.1).1
          ((sourceReindexEquiv ha hc).symm y.1).2.1
          ((sourceReindexEquiv ha hc).symm y.1).2.2).mpr
      change
        K_yzw
          (n := n) (a := c) (b := a) (c := b) (d := d)
          (sourceReindexEquiv ha hc
            ((sourceReindexEquiv ha hc).symm y.1)) = 0
      rw [(sourceReindexEquiv ha hc).apply_symm_apply]
      exact LinearMap.mem_ker.mp y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact (sourceReindexEquiv ha hc).symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact (sourceReindexEquiv ha hc).apply_symm_apply y.1
  map_add' x y := by
    apply Subtype.ext
    exact (sourceReindexEquiv ha hc).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (sourceReindexEquiv ha hc).map_smul r x.1

set_option maxHeartbeats 2000000 in
-- The two finite rank-nullity identities require a bounded increase in
-- instance-search and tactic budgets.
set_option synthInstance.maxHeartbeats 200000 in
private theorem finrank_range_diamondPreCMap_eq_rotated_K_yzw
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) :
    Module.finrank F
        (LinearMap.range
          (diamondPreCMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.range
          (K_yzw
            (n := n) (a := c) (b := a) (c := b) (d := d))) := by
  have hPre :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondPreCMap
        (n := n) (a := a) (b := b) (c := c) (d := d))
  have hK :=
    LinearMap.finrank_range_add_finrank_ker
      (K_yzw
        (n := n) (a := c) (b := a) (c := b) (d := d))
  have hDomain :=
    LinearEquiv.finrank_eq
      (sourceReindexEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc)
  have hKernel :=
    LinearEquiv.finrank_eq
      (diamondPreCKernelEquivKYZW
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc)
  omega

end

end DiamondSourceRank

namespace SquareDiagonal.DirectWitt

set_option maxHeartbeats 2000000 in
-- The finite function-space products require a larger elaboration budget than
-- the repository default.
set_option synthInstance.maxHeartbeats 1000000 in
/--
The literal pre-`C` source map has the three-coordinate root rank predicted
by the rotated `K_yzw` certificate.  The formula is kept subtraction-free.
-/
theorem finrank_range_diamondPreCMap_add_vertex_terms
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (diamondPreCMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1)^2 * (n^a + n^b + n^d)
    =
    (n - 1) * (n^(a+b) + n^(a+d) + n^(b+d))
      + (n - 1)^3 := by
  rw [DiamondSourceRank.finrank_range_diamondPreCMap_eq_rotated_K_yzw
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hc]
  simpa [mul_add, add_assoc, add_left_comm, add_comm] using
    (finrank_range_K_yzw_add_pair_infs
      (n := n) (a := c) (b := a) (c := b) (d := d) ha hb hd)

set_option maxHeartbeats 2000000 in
-- Rank-nullity on the literal finite function-space product needs the same
-- bounded instance-search budget.
set_option synthInstance.maxHeartbeats 1000000 in
/--
Rank-nullity for the literal pre-`C` source, with the three normal-form
source fields expanded to their exact dimensions.
-/
theorem finrank_diamondPreCSource_add_range
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) :
    Module.finrank F (DiamondPreCSource n a b c d)
      + Module.finrank F
          (LinearMap.range
            (diamondPreCMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    =
    n^(b+c+d) + n^(a+c+d) + n^(a+b+c) := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondPreCMap
        (n := n) (a := a) (b := b) (c := c) (d := d))
  rw [Module.finrank_prod, Module.finrank_prod,
    finrank_AFun4 (n := n) (b := b) (c := c) (d := d),
    finrank_BFun4 (n := n) (a := a) (c := c) (d := d) ha,
    finrank_WFun4 (n := n) (a := a) (b := b) (c := c) ha] at h
  change
    Module.finrank F
          (LinearMap.ker
            (diamondPreCMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
        + Module.finrank F
          (LinearMap.range
            (diamondPreCMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
      =
      n^(b+c+d) + n^(a+c+d) + n^(a+b+c)
  omega

end SquareDiagonal.DirectWitt

end Core4loop
