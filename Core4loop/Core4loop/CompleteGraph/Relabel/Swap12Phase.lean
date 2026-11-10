import Core4loop.Phase

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop

noncomputable section

/-- Split a positive vector into its tail and total cyclic sum. -/
private def k4VecTailSumEquiv
    (n k : Nat) [NeZero n] (hk : 0 < k) :
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
            change vecCons (vecSum v - vecSum (vecTail v)) (vecTail v) = v
            rw [hhead]
            exact vecCons_head_tail v
          right_inv := by
            intro q
            rcases q with ⟨p, s⟩
            apply Prod.ext
            · exact vecTail_vecCons (s - vecSum p) p
            · change vecSum (vecCons (s - vecSum p) p) = s
              rw [vecSum_vecCons]
              exact sub_add_cancel _ _ }

@[simp]
private theorem k4VecTailSumEquiv_snd
    {n k : Nat} [NeZero n] (hk : 0 < k) (v : Vec n k) :
    (k4VecTailSumEquiv n k hk v).2 = vecSum v := by
  cases k with
  | zero => omega
  | succ k => rfl

@[simp]
private theorem k4VecTailSumEquiv_symm_sum
    {n k : Nat} [NeZero n] (hk : 0 < k)
    (p : PVec n k) (s : I n) :
    vecSum ((k4VecTailSumEquiv n k hk).symm (p, s)) = s := by
  cases k with
  | zero => omega
  | succ k =>
      change vecSum (vecCons (s - vecSum p) p) = s
      rw [vecSum_vecCons]
      exact sub_add_cancel _ _

@[simp]
private theorem k4VecTailSumEquiv_eta
    {n k : Nat} [NeZero n] (hk : 0 < k) (v : Vec n k) :
    (k4VecTailSumEquiv n k hk).symm
        ((k4VecTailSumEquiv n k hk v).1, vecSum v) = v := by
  rw [← k4VecTailSumEquiv_snd hk v]
  exact (k4VecTailSumEquiv n k hk).symm_apply_apply v

/--
Change the reference vertex from block A to block B. The shears in the C and
W fields are forced by the shared cyclic bra shift.
-/
def k4Swap12NF
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b)
    (nf : NF4 n a b c d) :
    NF4 n b a c d :=
  let ea := k4VecTailSumEquiv n a ha
  let eb := k4VecTailSumEquiv n b hb
  { A := fun y z w =>
      nf.B (ea y).1 (-(ea y).2 - vecSum z - vecSum w) z w
    B := fun p s z w =>
      nf.A (eb.symm (p, -s - vecSum z - vecSum w)) z w
    C := fun p y s w =>
      nf.C (ea y).1
        (eb.symm (p, -(ea y).2 - s - vecSum w)) s w
    W := fun p y z s =>
      nf.W (ea y).1
        (eb.symm (p, -(ea y).2 - vecSum z - s)) z s }

-- Dependent function fields simplify most robustly after exposing the goal.
set_option linter.flexible false in
private theorem k4Swap12NF_involutive
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b)
    (nf : NF4 n a b c d) :
    k4Swap12NF hb ha (k4Swap12NF ha hb nf) = nf := by
  rcases nf with ⟨A, B, C, W⟩
  simp only [k4Swap12NF]
  rw [NF4.mk.injEq]
  constructor
  · funext y z w
    simp
    have hscalar :
        vecSum w - (-vecSum y - vecSum z) - vecSum z - vecSum w =
          vecSum y := by
      ring
    rw [hscalar, k4VecTailSumEquiv_eta hb y]
  · constructor
    · funext p s z w
      simp
      have hscalar :
          vecSum w - (-s - vecSum z) - vecSum z - vecSum w = s := by
        ring
      rw [hscalar]
    · constructor
      · funext p y s w
        simp
        have hscalar :
            vecSum w - (-vecSum y - s) - s - vecSum w = vecSum y := by
          ring
        rw [hscalar, k4VecTailSumEquiv_eta hb y]
      · funext p y z s
        simp
        have hscalar :
            s - (-vecSum y - vecSum z) - vecSum z - s = vecSum y := by
          ring
        rw [hscalar, k4VecTailSumEquiv_eta hb y]

/-- The root-reference change as an equivalence of full normal-form fields. -/
noncomputable def k4Swap12NFEquiv
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) :
    NF4 n a b c d ≃ NF4 n b a c d where
  toFun := k4Swap12NF ha hb
  invFun := k4Swap12NF hb ha
  left_inv := k4Swap12NF_involutive ha hb
  right_inv := k4Swap12NF_involutive hb ha

private abbrev K4RootCell (n a b c d : Nat) :=
  PVec n a × YVec n b × ZVec n c × WVec n d

/--
Cell reindex with scalar offset `t`. The ket map is `t = 0`; the distinct
bra map is `t = -1`.
-/
private def k4Swap12CellForward
    {n a b c d : Nat} [NeZero n]
    (t : I n) (ha : 0 < a) (hb : 0 < b)
    (x : K4RootCell n b a c d) :
    K4RootCell n a b c d :=
  let ea := k4VecTailSumEquiv n a ha
  let eb := k4VecTailSumEquiv n b hb
  ( (ea x.2.1).1,
    eb.symm
      (x.1, -(ea x.2.1).2 - vecSum x.2.2.1 - vecSum x.2.2.2 + t),
    x.2.2.1,
    x.2.2.2 )

-- The inverse proof normalizes the dependent product coordinates together.
set_option linter.flexible false in
private def k4Swap12CellEquiv
    {n a b c d : Nat} [NeZero n]
    (t : I n) (ha : 0 < a) (hb : 0 < b) :
    K4RootCell n b a c d ≃ K4RootCell n a b c d where
  toFun := k4Swap12CellForward t ha hb
  invFun := k4Swap12CellForward t hb ha
  left_inv := by
    rintro ⟨p, y, z, w⟩
    simp [k4Swap12CellForward]
    have hscalar :
        -t + (vecSum w - (-vecSum y - vecSum z)) -
              vecSum z - vecSum w + t =
          vecSum y := by
      ring
    rw [hscalar, k4VecTailSumEquiv_eta ha y]
  right_inv := by
    rintro ⟨p, y, z, w⟩
    simp [k4Swap12CellForward]
    have hscalar :
        -t + (vecSum w - (-vecSum y - vecSum z)) -
              vecSum z - vecSum w + t =
          vecSum y := by
      ring
    rw [hscalar, k4VecTailSumEquiv_eta hb y]

private def k4KetPhase
    {n a b c d : Nat} [NeZero n]
    (nf : NF4 n a b c d) (x : K4RootCell n a b c d) : F :=
  disc .complete
    (alphaOf nf x.1 x.2.1 x.2.2.1 x.2.2.2)
    (betaOf nf x.1 x.2.1 x.2.2.1 x.2.2.2)
    (deltaOf nf x.1 x.2.1 x.2.2.1 x.2.2.2)
    (xiOf nf x.1 x.2.1 x.2.2.1 x.2.2.2)

private def k4BraPhase
    {n a b c d : Nat} [NeZero n]
    (nf : NF4 n a b c d) (x : K4RootCell n a b c d) : F :=
  disc .complete
    (alphaOf nf x.1 x.2.1 x.2.2.1 x.2.2.2)
    (gammaOf nf x.1 x.2.1 x.2.2.1 x.2.2.2)
    (etaOf nf x.1 x.2.1 x.2.2.1 x.2.2.2)
    (zetaOf nf x.1 x.2.1 x.2.2.1 x.2.2.2)

private noncomputable def k4CellSum
    {n a b c d : Nat} [NeZero n]
    (f : K4RootCell n a b c d → F) : F :=
  ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
    f (p, y, z, w)

private theorem k4CellSum_eq_sum
    {n a b c d : Nat} [NeZero n]
    (f : K4RootCell n a b c d → F) :
    k4CellSum f = ∑ x, f x := by
  simp only [k4CellSum, Fintype.sum_prod_type]

private theorem k4CellSum_equiv
    {n a b c d a' b' c' d' : Nat} [NeZero n]
    (e : K4RootCell n a b c d ≃ K4RootCell n a' b' c' d')
    (f : K4RootCell n a b c d → F)
    (g : K4RootCell n a' b' c' d' → F)
    (h : ∀ x, f x = g (e x)) :
    k4CellSum f = k4CellSum g := by
  rw [k4CellSum_eq_sum, k4CellSum_eq_sum]
  exact Fintype.sum_equiv e f g h

set_option maxHeartbeats 1000000 in
-- Expanding four dependent reads requires a larger deterministic budget.
set_option linter.flexible false in
private theorem k4KetPhase_swap12
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b)
    (nf : NF4 n a b c d)
    (x : K4RootCell n b a c d) :
    k4KetPhase (k4Swap12NF ha hb nf) x =
      k4KetPhase nf (k4Swap12CellEquiv 0 ha hb x) := by
  rcases x with ⟨p, y, z, w⟩
  simp [k4KetPhase, k4Swap12NF, k4Swap12CellEquiv,
    k4Swap12CellForward, alphaOf, betaOf, deltaOf, xiOf, disc]
  ring_nf

set_option maxHeartbeats 1000000 in
-- Expanding four shifted dependent reads requires the same bounded budget.
set_option linter.flexible false in
private theorem k4BraPhase_swap12
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b)
    (nf : NF4 n a b c d)
    (x : K4RootCell n b a c d) :
    k4BraPhase (k4Swap12NF ha hb nf) x =
      k4BraPhase nf (k4Swap12CellEquiv (-1) ha hb x) := by
  rcases x with ⟨p, y, z, w⟩
  simp [k4BraPhase, k4Swap12NF, k4Swap12CellEquiv,
    k4Swap12CellForward, alphaOf, gammaOf, etaOf, zetaOf, disc]
  ring_nf

private theorem phaseExponentNF_complete_eq_cellSums
    {n a b c d : Nat} [NeZero n]
    (nf : NF4 n a b c d) :
    phaseExponentNF .complete nf =
      k4CellSum (k4KetPhase nf) + k4CellSum (k4BraPhase nf) := by
  simp only [phaseExponentNF, localPhase, k4CellSum, k4KetPhase, k4BraPhase,
    Finset.sum_add_distrib]

/--
Changing the chosen reference from block A to block B preserves the complete
graph phase. The ket and bra sums are reindexed separately by `T0` and `T1`.
-/
theorem phaseExponentNF_complete_swap12
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b)
    (nf : NF4 n a b c d) :
    phaseExponentNF .complete (k4Swap12NF ha hb nf) =
      phaseExponentNF .complete nf := by
  rw [phaseExponentNF_complete_eq_cellSums,
    phaseExponentNF_complete_eq_cellSums]
  congr 1
  · exact k4CellSum_equiv (k4Swap12CellEquiv 0 ha hb)
      (k4KetPhase (k4Swap12NF ha hb nf)) (k4KetPhase nf)
      (k4KetPhase_swap12 ha hb nf)
  · exact k4CellSum_equiv (k4Swap12CellEquiv (-1) ha hb)
      (k4BraPhase (k4Swap12NF ha hb nf)) (k4BraPhase nf)
      (k4BraPhase_swap12 ha hb nf)

end

end Core4loop
