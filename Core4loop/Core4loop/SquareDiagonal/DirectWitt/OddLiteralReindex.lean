import Core4loop.SquareDiagonal.DirectWitt.OddLiteralCoordinates
import Core4loop.SquareDiagonal.EvenP.CubeReindex

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

open Core4loop.SquareDiagonal.EvenP

noncomputable section

/-- Literal `C` reindexed as passive `P/Y/W` tails and one cyclic cube. -/
noncomputable def diamondOddCPassiveCubeEquiv
    {n a b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    CFun4 n a b d ≃ₗ[F]
      (PVec n a → PVec n b → PVec n d → CyclicCube n) where
  toFun C p yt wt i j k :=
    C p
      ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
      j
      ((diamondOddVecHeadTailEquiv hd).symm (k, wt))
  invFun G p y j w :=
    G p
      (diamondOddVecHeadTailEquiv hb y).2
      (diamondOddVecHeadTailEquiv hd w).2
      (diamondOddVecHeadTailEquiv hb y).1
      j
      (diamondOddVecHeadTailEquiv hd w).1
  left_inv C := by
    funext p y j w
    change
      C p
          ((diamondOddVecHeadTailEquiv hb).symm
            (diamondOddVecHeadTailEquiv hb y))
          j
          ((diamondOddVecHeadTailEquiv hd).symm
            (diamondOddVecHeadTailEquiv hd w)) =
        C p y j w
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv G := by
    funext p yt wt i j k
    simp
  map_add' C C' := rfl
  map_smul' r C := rfl

@[simp] theorem diamondOddCPassiveCubeEquiv_apply
    {n a b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (C : CFun4 n a b d)
    (p : PVec n a) (yt : PVec n b) (wt : PVec n d)
    (i j k : I n) :
    diamondOddCPassiveCubeEquiv hb hd C p yt wt i j k =
      C p
        ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
        j
        ((diamondOddVecHeadTailEquiv hd).symm (k, wt)) := rfl

@[simp] theorem diamondOddCPassiveCubeEquiv_symm_apply
    {n a b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (G : PVec n a → PVec n b → PVec n d → CyclicCube n)
    (p : PVec n a) (y : YVec n b) (j : I n) (w : WVec n d) :
    (diamondOddCPassiveCubeEquiv hb hd).symm G p y j w =
      G p
        (diamondOddVecHeadTailEquiv hb y).2
        (diamondOddVecHeadTailEquiv hd w).2
        (diamondOddVecHeadTailEquiv hb y).1
        j
        (diamondOddVecHeadTailEquiv hd w).1 := rfl

private theorem odd_vecSum_headTail_symm
    {n k : Nat} [NeZero n] (hk : 0 < k)
    (head : I n) (tail : PVec n k) :
    vecSum ((diamondOddVecHeadTailEquiv hk).symm (head, tail)) =
      head + vecSum tail := by
  cases k with
  | zero => omega
  | succ k =>
      exact vecSum_vecCons head tail

private theorem odd_sum_vec_headTail
    {n k : Nat} [NeZero n] (hk : 0 < k)
    (f : Vec n k → F) :
    (∑ v : Vec n k, f v) =
      ∑ head : I n, ∑ tail : PVec n k,
        f ((diamondOddVecHeadTailEquiv hk).symm (head, tail)) := by
  calc
    (∑ v : Vec n k, f v) =
        ∑ x : I n × PVec n k,
          f ((diamondOddVecHeadTailEquiv hk).symm x) := by
      refine Fintype.sum_equiv (diamondOddVecHeadTailEquiv hk)
        f
        (fun x => f ((diamondOddVecHeadTailEquiv hk).symm x)) ?_
      intro v
      exact congrArg f
        ((diamondOddVecHeadTailEquiv hk).symm_apply_apply v).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]

private theorem odd_sum_if_add_eq
    {n : Nat} [NeZero n] (tailSum target : I n) (f : I n → F) :
    (∑ head : I n,
        if head + tailSum = target then f head else 0) =
      f (target - tailSum) := by
  rw [Finset.sum_eq_single (target - tailSum)]
  · have htarget : target - tailSum + tailSum = target := by abel
    rw [if_pos htarget]
  · intro head _ hhead
    by_cases hsum : head + tailSum = target
    · exact (hhead (calc
        head = (head + tailSum) - tailSum := by simp
        _ = target - tailSum := by rw [hsum])).elim
    · simp [hsum]
  · simp

private theorem odd_sum_if_add_add_one_eq
    {n : Nat} [NeZero n] (tailSum target : I n) (f : I n → F) :
    (∑ head : I n,
        if head + tailSum + 1 = target then f head else 0) =
      f (target - tailSum - 1) := by
  rw [Finset.sum_eq_single (target - tailSum - 1)]
  · have htarget :
        target - tailSum - 1 + tailSum + 1 = target := by abel
    rw [if_pos htarget]
  · intro head _ hhead
    by_cases hsum : head + tailSum + 1 = target
    · exact (hhead (calc
        head = (head + tailSum + 1) - tailSum - 1 := by abel
        _ = target - tailSum - 1 := by rw [hsum])).elim
    · simp [hsum]
  · simp

@[simp] private theorem odd_cubeDiffI_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffI f i j k = f i j k + f (i + 1) j k := by
  rfl

@[simp] private theorem odd_cubeDiffK_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffK f i j k = f i j k + f i j (k + 1) := by
  simp

@[simp] private theorem odd_cubeDiffJInv_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffJInv f i j k = f i j k + f i (j - 1) k := by
  let q0 : I n × I n × I n := (i, j, k)
  let q1 : I n × I n × I n := (i, j - 1, k)
  let e : CyclicCube n := fun i' j' k' =>
    if (i', j', k') = q0 then 1 else 0
  have h := cubeDiffJ_pairing_adjoint e f
  classical
  have hr : cubeDot e (cubeDiffJInv f) = cubeDiffJInv f i j k := by
    rw [cubeDot, Finset.sum_eq_single q0]
    · simp [e, q0]
    · intro q _ hq
      simp [e, hq]
    · simp
  have hfirst :
      (∑ q : I n × I n × I n,
          e q.1 q.2.1 q.2.2 * f q.1 q.2.1 q.2.2) =
        f i j k := by
    rw [Finset.sum_eq_single q0]
    · simp [e, q0]
    · intro q _ hq
      simp [e, hq]
    · simp
  have hsecond :
      (∑ q : I n × I n × I n,
          e q.1 (q.2.1 + 1) q.2.2 * f q.1 q.2.1 q.2.2) =
        f i (j - 1) k := by
    rw [Finset.sum_eq_single q1]
    · have hshift :
        ((q1.1, q1.2.1 + 1, q1.2.2) :
          I n × I n × I n) = q0 := by
        simp [q0, q1]
      have heq :
          e q1.1 (q1.2.1 + 1) q1.2.2 = 1 := by
        simp only [e]
        rw [if_pos hshift]
      rw [heq]
      simp [q1]
    · intro q _ hq
      by_cases hshift :
          ((q.1, q.2.1 + 1, q.2.2) :
            I n × I n × I n) = q0
      · have hqi : q.1 = i := by
          simpa [q0] using congrArg Prod.fst hshift
        have hqj : q.2.1 + 1 = j := by
          simpa [q0] using congrArg (fun x => x.2.1) hshift
        have hqk : q.2.2 = k := by
          simpa [q0] using congrArg (fun x => x.2.2) hshift
        have hqq1 : q = q1 := by
          apply Prod.ext
          · simpa [q1] using hqi
          · apply Prod.ext
            · simp only [q1]
              calc
                q.2.1 = (q.2.1 + 1) - 1 := by simp
                _ = j - 1 := by rw [hqj]
            · simpa [q1] using hqk
        exact (hq hqq1).elim
      · simp [e, hshift]
    · simp
  rw [hr] at h
  have hstar (i' j' k' : I n) :
      cubeDiffJStar e i' j' k' =
        e i' j' k' + e i' (j' + 1) k' := by
    simp
  rw [cubeDot] at h
  simp_rw [hstar] at h
  simp only [add_mul, Finset.sum_add_distrib] at h
  rw [hfirst, hsecond] at h
  exact h.symm

@[simp] private theorem odd_cubeDiffP_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffP f i j k = f i j k + f (i + 1) (j - 1) k := by
  simp

@[simp] private theorem odd_cubeDiffR_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffR f i j k = f i j k + f i (j - 1) (k + 1) := by
  simp

private theorem diamondOddLiteral_AConstraint_reindexed
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d)
    (p : PVec n a) (yt : PVec n b) (wt : PVec n d)
    (i sz k : I n) :
    diamondEvenPAConstraint
        (n := n) (a := a) (b := b) (c := c) (d := d) A
        p
        ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
        sz
        ((diamondOddVecHeadTailEquiv hd).symm (k, wt))
      =
    ∑ zt : PVec n c,
      cubeDiffJInv
        (diamondOddAPassiveCubeEquiv hb hc hd A yt zt wt)
        i (sz - vecSum zt) k := by
  unfold diamondEvenPAConstraint
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [odd_sum_vec_headTail hc, odd_sum_vec_headTail hc]
  simp_rw [odd_vecSum_headTail_symm]
  conv_lhs =>
    congr
    · rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
  simp_rw [odd_sum_if_add_eq, odd_sum_if_add_add_one_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro zt _
  simp only [odd_cubeDiffJInv_apply,
    diamondOddAPassiveCubeEquiv_apply]

private theorem diamondOddLiteral_squareCompat_reindexed
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (p : PVec n a) (yt : PVec n b) (wt : PVec n d)
    (i sz k : I n) :
    squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)
        p
        ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
        sz
        ((diamondOddVecHeadTailEquiv hd).symm (k, wt))
      =
    ∑ zt : PVec n c,
      (cubeDiffP (diamondOddBPassiveCubeEquiv hc hd B p zt wt)
          (i + vecSum yt) (sz - vecSum zt) k
       +
       cubeDiffR (diamondOddWPassiveCubeEquiv hb hc W p yt zt)
          i (sz - vecSum zt) (k + vecSum wt)) := by
  unfold squareCompat squareCompatFun betaB gammaB xiW zetaW
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [odd_sum_vec_headTail hc, odd_sum_vec_headTail hc]
  simp_rw [odd_vecSum_headTail_symm]
  conv_lhs =>
    congr
    · rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
  simp_rw [odd_sum_if_add_eq, odd_sum_if_add_add_one_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro zt _
  simp only [odd_cubeDiffP_apply, odd_cubeDiffR_apply,
    diamondOddBPassiveCubeEquiv_apply,
    diamondOddWPassiveCubeEquiv_apply]
  abel

/-- Literal arbitrary-`a` source equation, with no parity assumption. -/
theorem diamondOddLiteral_source_iff_reindexed
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) :
    diamondPreCMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (A, B, W) = 0 ↔
      ∀ (p : PVec n a) (yt : PVec n b) (wt : PVec n d)
        (i sz k : I n),
        (∑ zt : PVec n c,
          cubeDiffJInv
            (diamondOddAPassiveCubeEquiv hb hc hd A yt zt wt)
            i (sz - vecSum zt) k) =
        ∑ zt : PVec n c,
          (cubeDiffP (diamondOddBPassiveCubeEquiv hc hd B p zt wt)
              (i + vecSum yt) (sz - vecSum zt) k
            +
           cubeDiffR (diamondOddWPassiveCubeEquiv hb hc W p yt zt)
              i (sz - vecSum zt) (k + vecSum wt)) := by
  rw [diamondPreCMap_eq_zero_iff_constraint]
  constructor
  · intro h p yt wt i sz k
    have hpoint :
        diamondEvenPAConstraint
            (n := n) (a := a) (b := b) (c := c) (d := d) A
            p
            ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
            sz
            ((diamondOddVecHeadTailEquiv hd).symm (k, wt)) =
          squareCompat
            (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)
            p
            ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
            sz
            ((diamondOddVecHeadTailEquiv hd).symm (k, wt)) := by
      rw [h]
    rw [diamondOddLiteral_AConstraint_reindexed hb hc hd] at hpoint
    rw [diamondOddLiteral_squareCompat_reindexed hb hc hd] at hpoint
    exact hpoint
  · intro h
    funext p y sz w
    let ey := diamondOddVecHeadTailEquiv hb y
    let ew := diamondOddVecHeadTailEquiv hd w
    have hp := h p ey.2 ew.2 ey.1 sz ew.1
    rw [← diamondOddLiteral_AConstraint_reindexed
      (p := p) hb hc hd] at hp
    rw [← diamondOddLiteral_squareCompat_reindexed
      (p := p) hb hc hd] at hp
    have hy :
        (diamondOddVecHeadTailEquiv hb).symm (ey.1, ey.2) = y := by
      change
        (diamondOddVecHeadTailEquiv hb).symm
            (diamondOddVecHeadTailEquiv hb y) = y
      exact Equiv.symm_apply_apply _ _
    have hw :
        (diamondOddVecHeadTailEquiv hd).symm (ew.1, ew.2) = w := by
      change
        (diamondOddVecHeadTailEquiv hd).symm
            (diamondOddVecHeadTailEquiv hd w) = w
      exact Equiv.symm_apply_apply _ _
    simpa only [hy, hw] using hp

private theorem odd_sum_six_reorder
    {α β γ δ ε ζ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [Fintype ζ]
    (f : α → β → γ → δ → ε → ζ → F) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, ∑ e : ε, ∑ z : ζ,
        f a b c d e z) =
      ∑ b : β, ∑ d : δ, ∑ z : ζ, ∑ a : α, ∑ c : γ, ∑ e : ε,
        f a b c d e z := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro b _
  calc
    (∑ a : α, ∑ c : γ, ∑ d : δ, ∑ e : ε, ∑ z : ζ,
        f a b c d e z) =
        ∑ a : α, ∑ d : δ, ∑ c : γ, ∑ e : ε, ∑ z : ζ,
          f a b c d e z := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ d : δ, ∑ a : α, ∑ c : γ, ∑ e : ε, ∑ z : ζ,
          f a b c d e z := by
      rw [Finset.sum_comm]
    _ = ∑ d : δ, ∑ z : ζ, ∑ a : α, ∑ c : γ, ∑ e : ε,
          f a b c d e z := by
      refine Finset.sum_congr rfl ?_
      intro d _
      calc
        (∑ a : α, ∑ c : γ, ∑ e : ε, ∑ z : ζ,
            f a b c d e z) =
            ∑ a : α, ∑ c : γ, ∑ z : ζ, ∑ e : ε,
              f a b c d e z := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.sum_comm]
        _ = ∑ a : α, ∑ z : ζ, ∑ c : γ, ∑ e : ε,
              f a b c d e z := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.sum_comm]
        _ = ∑ z : ζ, ∑ a : α, ∑ c : γ, ∑ e : ε,
              f a b c d e z := by
          rw [Finset.sum_comm]

private theorem diamondOddLiteral_root_reindexed
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B +
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W)
        ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
        ((diamondOddVecHeadTailEquiv hc).symm (j, zt))
        ((diamondOddVecHeadTailEquiv hd).symm (k, wt))
      =
    ∑ p : PVec n a,
      (cubeDiffI (diamondOddBPassiveCubeEquiv hc hd B p zt wt)
            (i + vecSum yt) j k
        +
       cubeDiffK (diamondOddWPassiveCubeEquiv hb hc W p yt zt)
            i j (k + vecSum wt)) := by
  unfold KBMap KWMap dyB dwW betaB gammaB xiW zetaW
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
    odd_cubeDiffI_apply, odd_cubeDiffK_apply,
    diamondOddBPassiveCubeEquiv_apply,
    diamondOddWPassiveCubeEquiv_apply]
  rw [odd_vecSum_headTail_symm hb, odd_vecSum_headTail_symm hd]
  rw [← Finset.sum_add_distrib]

/-- Literal raw phase, including the outer arbitrary-`p` sum. -/
theorem diamondOddLiteral_q_eq_reindexed
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : DiamondPreCSource n a b c d) :
    diamondPreCQ x =
      ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        cubeDot
          (diamondOddAPassiveCubeEquiv hb hc hd x.1.1 yt zt wt)
          (fun i j k =>
            ∑ p : PVec n a,
              (cubeDiffI
                    (diamondOddBPassiveCubeEquiv hc hd
                      x.1.2.1 p zt wt)
                    (i + vecSum yt) j k
                +
               cubeDiffK
                    (diamondOddWPassiveCubeEquiv hb hc
                      x.1.2.2 p yt zt)
                    i j (k + vecSum wt))) := by
  unfold diamondPreCQ
  rw [coeffApplyA_eq_sum]
  rw [odd_sum_vec_headTail hb]
  simp_rw [odd_sum_vec_headTail hc, odd_sum_vec_headTail hd]
  rw [odd_sum_six_reorder]
  refine Finset.sum_congr rfl ?_
  intro yt _
  refine Finset.sum_congr rfl ?_
  intro zt _
  refine Finset.sum_congr rfl ?_
  intro wt _
  simp_rw [cubeDot, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro k _
  simp only [diamondOddAPassiveCubeEquiv_apply]
  rw [diamondOddLiteral_root_reindexed hb hc hd]

/-- Translate all three active heads of `A` by their passive tail sums. -/
noncomputable def diamondOddAGaugeEquiv
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    AFun4 n b c d ≃ₗ[F]
      (PVec n b → PVec n c → PVec n d → CyclicCube n) where
  toFun A yt zt wt i j k :=
    diamondOddAPassiveCubeEquiv hb hc hd A yt zt wt
      (i - vecSum yt) (j - vecSum zt) (k - vecSum wt)
  invFun G y z w :=
    G
      (diamondOddVecHeadTailEquiv hb y).2
      (diamondOddVecHeadTailEquiv hc z).2
      (diamondOddVecHeadTailEquiv hd w).2
      ((diamondOddVecHeadTailEquiv hb y).1 +
        vecSum (diamondOddVecHeadTailEquiv hb y).2)
      ((diamondOddVecHeadTailEquiv hc z).1 +
        vecSum (diamondOddVecHeadTailEquiv hc z).2)
      ((diamondOddVecHeadTailEquiv hd w).1 +
        vecSum (diamondOddVecHeadTailEquiv hd w).2)
  left_inv A := by
    funext y z w
    simp only [diamondOddAPassiveCubeEquiv_apply, add_sub_cancel_right]
    rw [Prod.eta, Prod.eta, Prod.eta,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
  right_inv G := by
    funext yt zt wt i j k
    simp
  map_add' A A' := rfl
  map_smul' r A := rfl

@[simp] theorem diamondOddAGaugeEquiv_apply
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    diamondOddAGaugeEquiv hb hc hd A yt zt wt i j k =
      diamondOddAPassiveCubeEquiv hb hc hd A yt zt wt
        (i - vecSum yt) (j - vecSum zt) (k - vecSum wt) := rfl

@[simp] theorem diamondOddAGaugeEquiv_symm_apply
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (G : PVec n b → PVec n c → PVec n d → CyclicCube n)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    (diamondOddAGaugeEquiv hb hc hd).symm G y z w =
      G
        (diamondOddVecHeadTailEquiv hb y).2
        (diamondOddVecHeadTailEquiv hc z).2
        (diamondOddVecHeadTailEquiv hd w).2
        ((diamondOddVecHeadTailEquiv hb y).1 +
          vecSum (diamondOddVecHeadTailEquiv hb y).2)
        ((diamondOddVecHeadTailEquiv hc z).1 +
          vecSum (diamondOddVecHeadTailEquiv hc z).2)
        ((diamondOddVecHeadTailEquiv hd w).1 +
          vecSum (diamondOddVecHeadTailEquiv hd w).2) := rfl

/-- Translate the `Z/W` heads of `B` by their passive tail sums. -/
noncomputable def diamondOddBGaugeEquiv
    {n a c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    BFun4 n a c d ≃ₗ[F]
      (PVec n a → PVec n c → PVec n d → CyclicCube n) where
  toFun B p zt wt i j k :=
    diamondOddBPassiveCubeEquiv hc hd B p zt wt
      i (j - vecSum zt) (k - vecSum wt)
  invFun G p i z w :=
    G p
      (diamondOddVecHeadTailEquiv hc z).2
      (diamondOddVecHeadTailEquiv hd w).2
      i
      ((diamondOddVecHeadTailEquiv hc z).1 +
        vecSum (diamondOddVecHeadTailEquiv hc z).2)
      ((diamondOddVecHeadTailEquiv hd w).1 +
        vecSum (diamondOddVecHeadTailEquiv hd w).2)
  left_inv B := by
    funext p i z w
    simp only [diamondOddBPassiveCubeEquiv_apply, add_sub_cancel_right]
    rw [Prod.eta, Prod.eta,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv G := by
    funext p zt wt i j k
    simp
  map_add' B B' := rfl
  map_smul' r B := rfl

@[simp] theorem diamondOddBGaugeEquiv_apply
    {n a c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n a c d)
    (p : PVec n a) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    diamondOddBGaugeEquiv hc hd B p zt wt i j k =
      diamondOddBPassiveCubeEquiv hc hd B p zt wt
        i (j - vecSum zt) (k - vecSum wt) := rfl

@[simp] theorem diamondOddBGaugeEquiv_symm_apply
    {n a c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (G : PVec n a → PVec n c → PVec n d → CyclicCube n)
    (p : PVec n a) (i : I n) (z : ZVec n c) (w : WVec n d) :
    (diamondOddBGaugeEquiv hc hd).symm G p i z w =
      G p
        (diamondOddVecHeadTailEquiv hc z).2
        (diamondOddVecHeadTailEquiv hd w).2
        i
        ((diamondOddVecHeadTailEquiv hc z).1 +
          vecSum (diamondOddVecHeadTailEquiv hc z).2)
        ((diamondOddVecHeadTailEquiv hd w).1 +
          vecSum (diamondOddVecHeadTailEquiv hd w).2) := rfl

/-- Translate the `Y/W` heads of `C` by their passive tail sums. -/
noncomputable def diamondOddCGaugeEquiv
    {n a b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    CFun4 n a b d ≃ₗ[F]
      (PVec n a → PVec n b → PVec n d → CyclicCube n) where
  toFun C p yt wt i j k :=
    diamondOddCPassiveCubeEquiv hb hd C p yt wt
      (i - vecSum yt) j (k - vecSum wt)
  invFun G p y j w :=
    G p
      (diamondOddVecHeadTailEquiv hb y).2
      (diamondOddVecHeadTailEquiv hd w).2
      ((diamondOddVecHeadTailEquiv hb y).1 +
        vecSum (diamondOddVecHeadTailEquiv hb y).2)
      j
      ((diamondOddVecHeadTailEquiv hd w).1 +
        vecSum (diamondOddVecHeadTailEquiv hd w).2)
  left_inv C := by
    funext p y j w
    simp only [diamondOddCPassiveCubeEquiv_apply, add_sub_cancel_right]
    rw [Prod.eta, Prod.eta,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv G := by
    funext p yt wt i j k
    simp
  map_add' C C' := rfl
  map_smul' r C := rfl

@[simp] theorem diamondOddCGaugeEquiv_apply
    {n a b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (C : CFun4 n a b d)
    (p : PVec n a) (yt : PVec n b) (wt : PVec n d)
    (i j k : I n) :
    diamondOddCGaugeEquiv hb hd C p yt wt i j k =
      diamondOddCPassiveCubeEquiv hb hd C p yt wt
        (i - vecSum yt) j (k - vecSum wt) := rfl

@[simp] theorem diamondOddCGaugeEquiv_symm_apply
    {n a b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (G : PVec n a → PVec n b → PVec n d → CyclicCube n)
    (p : PVec n a) (y : YVec n b) (j : I n) (w : WVec n d) :
    (diamondOddCGaugeEquiv hb hd).symm G p y j w =
      G p
        (diamondOddVecHeadTailEquiv hb y).2
        (diamondOddVecHeadTailEquiv hd w).2
        ((diamondOddVecHeadTailEquiv hb y).1 +
          vecSum (diamondOddVecHeadTailEquiv hb y).2)
        j
        ((diamondOddVecHeadTailEquiv hd w).1 +
          vecSum (diamondOddVecHeadTailEquiv hd w).2) := rfl

/-- Translate the `Y/Z` heads of `W` by their passive tail sums. -/
noncomputable def diamondOddWGaugeEquiv
    {n a b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    WFun4 n a b c ≃ₗ[F]
      (PVec n a → PVec n b → PVec n c → CyclicCube n) where
  toFun W p yt zt i j k :=
    diamondOddWPassiveCubeEquiv hb hc W p yt zt
      (i - vecSum yt) (j - vecSum zt) k
  invFun G p y z k :=
    G p
      (diamondOddVecHeadTailEquiv hb y).2
      (diamondOddVecHeadTailEquiv hc z).2
      ((diamondOddVecHeadTailEquiv hb y).1 +
        vecSum (diamondOddVecHeadTailEquiv hb y).2)
      ((diamondOddVecHeadTailEquiv hc z).1 +
        vecSum (diamondOddVecHeadTailEquiv hc z).2)
      k
  left_inv W := by
    funext p y z k
    simp only [diamondOddWPassiveCubeEquiv_apply, add_sub_cancel_right]
    rw [Prod.eta, Prod.eta,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv G := by
    funext p yt zt i j k
    simp
  map_add' W W' := rfl
  map_smul' r W := rfl

@[simp] theorem diamondOddWGaugeEquiv_apply
    {n a b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (W : WFun4 n a b c)
    (p : PVec n a) (yt : PVec n b) (zt : PVec n c)
    (i j k : I n) :
    diamondOddWGaugeEquiv hb hc W p yt zt i j k =
      diamondOddWPassiveCubeEquiv hb hc W p yt zt
        (i - vecSum yt) (j - vecSum zt) k := rfl

@[simp] theorem diamondOddWGaugeEquiv_symm_apply
    {n a b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (G : PVec n a → PVec n b → PVec n c → CyclicCube n)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (k : I n) :
    (diamondOddWGaugeEquiv hb hc).symm G p y z k =
      G p
        (diamondOddVecHeadTailEquiv hb y).2
        (diamondOddVecHeadTailEquiv hc z).2
        ((diamondOddVecHeadTailEquiv hb y).1 +
          vecSum (diamondOddVecHeadTailEquiv hb y).2)
        ((diamondOddVecHeadTailEquiv hc z).1 +
          vecSum (diamondOddVecHeadTailEquiv hc z).2)
        k := rfl

/-- Gauged literal `A × (B × W)` ambient coordinates. -/
abbrev DiamondOddLiteralAmbient
    (n a b c d : Nat) [NeZero n] :=
  (PVec n b → PVec n c → PVec n d → CyclicCube n) ×
  (PVec n a → PVec n c → PVec n d → CyclicCube n) ×
  (PVec n a → PVec n b → PVec n c → CyclicCube n)

/-- Target of the single gauged strict-source map. -/
abbrev DiamondOddLiteralTarget
    (n a b d : Nat) [NeZero n] :=
  PVec n a → PVec n b → PVec n d → CyclicCube n

/-- Product of the three explicit `A/B/W` gauges, in production order. -/
noncomputable def diamondOddABWGaugeEquiv
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (AFun4 n b c d × BFun4 n a c d × WFun4 n a b c) ≃ₗ[F]
      DiamondOddLiteralAmbient n a b c d where
  toFun x :=
    (diamondOddAGaugeEquiv hb hc hd x.1,
      diamondOddBGaugeEquiv hc hd x.2.1,
      diamondOddWGaugeEquiv hb hc x.2.2)
  invFun u :=
    ((diamondOddAGaugeEquiv hb hc hd).symm u.1,
      (diamondOddBGaugeEquiv hc hd).symm u.2.1,
      (diamondOddWGaugeEquiv hb hc).symm u.2.2)
  left_inv x := by
    rcases x with ⟨A, B, W⟩
    simp
  right_inv u := by
    rcases u with ⟨A, B, W⟩
    simp
  map_add' x y := by
    ext <;> rfl
  map_smul' r x := by
    ext <;> rfl

@[simp] theorem diamondOddABWGaugeEquiv_apply
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) :
    diamondOddABWGaugeEquiv hb hc hd (A, B, W) =
      (diamondOddAGaugeEquiv hb hc hd A,
        diamondOddBGaugeEquiv hc hd B,
        diamondOddWGaugeEquiv hb hc W) := rfl

@[simp] theorem diamondOddABWGaugeEquiv_symm_apply
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (u : DiamondOddLiteralAmbient n a b c d) :
    (diamondOddABWGaugeEquiv hb hc hd).symm u =
      ((diamondOddAGaugeEquiv hb hc hd).symm u.1,
        (diamondOddBGaugeEquiv hc hd).symm u.2.1,
        (diamondOddWGaugeEquiv hb hc).symm u.2.2) := rfl

/-- The single strict-source map after all literal head/tail gauges. -/
noncomputable def diamondOddLiteralSourceMap
    {n a b c d : Nat} [NeZero n] :
    DiamondOddLiteralAmbient n a b c d →ₗ[F]
      DiamondOddLiteralTarget n a b d where
  toFun u p yt wt :=
    cubeDiffJInv (∑ zt : PVec n c, u.1 yt zt wt) +
      cubeDiffP (∑ zt : PVec n c, u.2.1 p zt wt) +
      cubeDiffR (∑ zt : PVec n c, u.2.2 p yt zt)
  map_add' u v := by
    funext p yt wt
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply,
      Finset.sum_add_distrib, LinearMap.map_add]
    abel
  map_smul' r u := by
    funext p yt wt
    change
      cubeDiffJInv (∑ zt : PVec n c, r • u.1 yt zt wt) +
          cubeDiffP (∑ zt : PVec n c, r • u.2.1 p zt wt) +
          cubeDiffR (∑ zt : PVec n c, r • u.2.2 p yt zt) =
        r •
          (cubeDiffJInv (∑ zt : PVec n c, u.1 yt zt wt) +
            cubeDiffP (∑ zt : PVec n c, u.2.1 p zt wt) +
            cubeDiffR (∑ zt : PVec n c, u.2.2 p yt zt))
    simp only [← Finset.smul_sum, map_smul, smul_add]

@[simp] theorem diamondOddLiteralSourceMap_apply
    {n a b c d : Nat} [NeZero n]
    (u : DiamondOddLiteralAmbient n a b c d)
    (p : PVec n a) (yt : PVec n b) (wt : PVec n d) :
    diamondOddLiteralSourceMap u p yt wt =
      cubeDiffJInv (∑ zt : PVec n c, u.1 yt zt wt) +
      cubeDiffP (∑ zt : PVec n c, u.2.1 p zt wt) +
      cubeDiffR (∑ zt : PVec n c, u.2.2 p yt zt) := rfl

theorem diamondOddLiteralSourceMap_apply_pointwise
    {n a b c d : Nat} [NeZero n]
    (u : DiamondOddLiteralAmbient n a b c d)
    (p : PVec n a) (yt : PVec n b) (wt : PVec n d)
    (i j k : I n) :
    diamondOddLiteralSourceMap u p yt wt i j k =
      ∑ zt : PVec n c,
        (u.1 yt zt wt i j k +
         u.1 yt zt wt i (j - 1) k +
         u.2.1 p zt wt i j k +
         u.2.1 p zt wt (i + 1) (j - 1) k +
         u.2.2 p yt zt i j k +
         u.2.2 p yt zt i (j - 1) (k + 1)) := by
  rw [diamondOddLiteralSourceMap_apply]
  simp only [Pi.add_apply, odd_cubeDiffJInv_apply,
    odd_cubeDiffP_apply, odd_cubeDiffR_apply, Finset.sum_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  abel

private theorem diamondOddLiteralSourceMap_abwGauge_pointwise
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c)
    (p : PVec n a) (yt : PVec n b) (wt : PVec n d)
    (i j k : I n) :
    diamondOddLiteralSourceMap
        (diamondOddABWGaugeEquiv hb hc hd (A, B, W))
        p yt wt i j k =
      (∑ zt : PVec n c,
        cubeDiffJInv
          (diamondOddAPassiveCubeEquiv hb hc hd A yt zt wt)
          (i - vecSum yt) (j - vecSum zt) (k - vecSum wt))
      +
      ∑ zt : PVec n c,
        (cubeDiffP
            (diamondOddBPassiveCubeEquiv hc hd B p zt wt)
            i (j - vecSum zt) (k - vecSum wt)
          +
         cubeDiffR
            (diamondOddWPassiveCubeEquiv hb hc W p yt zt)
            (i - vecSum yt) (j - vecSum zt) k) := by
  rw [diamondOddLiteralSourceMap_apply_pointwise]
  simp only [diamondOddABWGaugeEquiv_apply,
    diamondOddAGaugeEquiv_apply, diamondOddBGaugeEquiv_apply,
    diamondOddWGaugeEquiv_apply, odd_cubeDiffJInv_apply,
    odd_cubeDiffP_apply, odd_cubeDiffR_apply,
    Finset.sum_add_distrib]
  have hj (zt : PVec n c) :
      j - 1 - vecSum zt = j - vecSum zt - 1 := by
    abel
  simp_rw [hj]
  abel

/-- The production pre-C source vanishes exactly on the gauged source map. -/
theorem diamondPreCMap_eq_zero_iff_oddLiteralSourceMap
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : AFun4 n b c d × BFun4 n a c d × WFun4 n a b c) :
    diamondPreCMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 ↔
      diamondOddLiteralSourceMap
        (diamondOddABWGaugeEquiv hb hc hd x) = 0 := by
  rcases x with ⟨A, B, W⟩
  rw [diamondOddLiteral_source_iff_reindexed hb hc hd A B W]
  constructor
  · intro h
    funext p yt wt i j k
    change
      diamondOddLiteralSourceMap
          (diamondOddABWGaugeEquiv hb hc hd (A, B, W))
          p yt wt i j k =
        (0 : F)
    rw [diamondOddLiteralSourceMap_abwGauge_pointwise
      hb hc hd A B W]
    rw [h p yt wt (i - vecSum yt) j (k - vecSum wt)]
    simp only [sub_add_cancel, F_add_self]
  · intro h p yt wt i j k
    have hp := congrFun
      (congrFun (congrFun (congrFun (congrFun (congrFun h p) yt) wt)
        (i + vecSum yt)) j) (k + vecSum wt)
    rw [diamondOddLiteralSourceMap_abwGauge_pointwise
      hb hc hd A B W] at hp
    simp only [Pi.zero_apply] at hp
    have hi : i + vecSum yt - vecSum yt = i := by abel
    have hk : k + vecSum wt - vecSum wt = k := by abel
    rw [hi, hk] at hp
    let rhs :=
      ∑ zt : PVec n c,
        (cubeDiffP
            (diamondOddBPassiveCubeEquiv hc hd B p zt wt)
            (i + vecSum yt) (j - vecSum zt) k
          +
         cubeDiffR
            (diamondOddWPassiveCubeEquiv hb hc W p yt zt)
            i (j - vecSum zt) (k + vecSum wt))
    have hplus := congrArg (fun t : F => t + rhs) hp
    calc
      (∑ zt : PVec n c,
          cubeDiffJInv
            (diamondOddAPassiveCubeEquiv hb hc hd A yt zt wt)
            i (j - vecSum zt) k) =
          ((∑ zt : PVec n c,
              cubeDiffJInv
                (diamondOddAPassiveCubeEquiv hb hc hd A yt zt wt)
                i (j - vecSum zt) k) + rhs) + rhs := by
            simp only [add_assoc, F_add_self, add_zero]
      _ = 0 + rhs := hplus
      _ = rhs := zero_add rhs

/-- The kernel of the single gauged literal source map. -/
noncomputable abbrev DiamondOddLiteralSource
    (n a b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (diamondOddLiteralSourceMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

/-- Restriction of the ambient gauge to the actual strict pre-C kernel. -/
noncomputable def diamondOddLiteralSourceEquiv
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DiamondPreCSource n a b c d ≃ₗ[F]
      DiamondOddLiteralSource n a b c d where
  toFun x :=
    ⟨diamondOddABWGaugeEquiv hb hc hd x.1,
      LinearMap.mem_ker.mpr
        ((diamondPreCMap_eq_zero_iff_oddLiteralSourceMap
          hb hc hd x.1).mp (LinearMap.mem_ker.mp x.2))⟩
  invFun u :=
    ⟨(diamondOddABWGaugeEquiv hb hc hd).symm u.1,
      LinearMap.mem_ker.mpr
        ((diamondPreCMap_eq_zero_iff_oddLiteralSourceMap hb hc hd
          ((diamondOddABWGaugeEquiv hb hc hd).symm u.1)).mpr (by
            rw [(diamondOddABWGaugeEquiv hb hc hd).apply_symm_apply u.1]
            exact LinearMap.mem_ker.mp u.2))⟩
  left_inv x := by
    apply Subtype.ext
    exact (diamondOddABWGaugeEquiv hb hc hd).symm_apply_apply x.1
  right_inv u := by
    apply Subtype.ext
    exact (diamondOddABWGaugeEquiv hb hc hd).apply_symm_apply u.1
  map_add' x y := by
    apply Subtype.ext
    exact (diamondOddABWGaugeEquiv hb hc hd).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (diamondOddABWGaugeEquiv hb hc hd).map_smul r x.1

@[simp] theorem diamondOddLiteralSourceEquiv_apply
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : DiamondPreCSource n a b c d) :
    (diamondOddLiteralSourceEquiv hb hc hd x).1 =
      diamondOddABWGaugeEquiv hb hc hd x.1 := rfl

@[simp] theorem diamondOddLiteralSourceEquiv_symm_apply
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (u : DiamondOddLiteralSource n a b c d) :
    ((diamondOddLiteralSourceEquiv hb hc hd).symm u).1 =
      (diamondOddABWGaugeEquiv hb hc hd).symm u.1 := rfl

private theorem diamondPreCMap_apply_eq_constraint_pairing
    {n a b c d : Nat} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) (C : CFun4 n a b d) :
    diamondPreCMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (A, B, W) C =
      coeffApply
        (cFun4Equiv n a b d
          (diamondEvenPAConstraint
              (n := n) (a := a) (b := b) (c := c) (d := d) A +
            squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
        (cFun4Equiv n a b d C) := by
  change
    coeffApplyA
        (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) A +
      coeffApply
        (cFun4Equiv n a b d
          (squareCompat
            (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
        (cFun4Equiv n a b d C) = _
  rw [← coeffApply_diamondEvenPAConstraint_eq_coeffApplyA_KCMap]
  unfold coeffApply
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro q _
  have hadd :
      cFun4Equiv n a b d
          (diamondEvenPAConstraint
              (n := n) (a := a) (b := b) (c := c) (d := d) A +
            squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)) q =
        cFun4Equiv n a b d
            (diamondEvenPAConstraint
              (n := n) (a := a) (b := b) (c := c) (d := d) A) q +
          cFun4Equiv n a b d
            (squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)) q := by
    rcases q with ⟨p, y, sz, w⟩
    rfl
  rw [hadd]
  ring_nf

private theorem diamondOddLiteral_constraint_apply_eq_sourceMap
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c)
    (p : PVec n a) (y : YVec n b) (sz : I n) (w : WVec n d) :
    (diamondEvenPAConstraint
          (n := n) (a := a) (b := b) (c := c) (d := d) A +
        squareCompat
          (n := n) (a := a) (b := b) (c := c) (d := d) (B, W))
        p y sz w =
      diamondOddLiteralSourceMap
        (diamondOddABWGaugeEquiv hb hc hd (A, B, W))
        p
        (diamondOddVecHeadTailEquiv hb y).2
        (diamondOddVecHeadTailEquiv hd w).2
        ((diamondOddVecHeadTailEquiv hb y).1 +
          vecSum (diamondOddVecHeadTailEquiv hb y).2)
        sz
        ((diamondOddVecHeadTailEquiv hd w).1 +
          vecSum (diamondOddVecHeadTailEquiv hd w).2) := by
  let ey := diamondOddVecHeadTailEquiv hb y
  let ew := diamondOddVecHeadTailEquiv hd w
  have hy :
      (diamondOddVecHeadTailEquiv hb).symm (ey.1, ey.2) = y := by
    change
      (diamondOddVecHeadTailEquiv hb).symm
          (diamondOddVecHeadTailEquiv hb y) = y
    exact Equiv.symm_apply_apply _ _
  have hw :
      (diamondOddVecHeadTailEquiv hd).symm (ew.1, ew.2) = w := by
    change
      (diamondOddVecHeadTailEquiv hd).symm
          (diamondOddVecHeadTailEquiv hd w) = w
    exact Equiv.symm_apply_apply _ _
  change
    diamondEvenPAConstraint
        (n := n) (a := a) (b := b) (c := c) (d := d) A
        p y sz w +
      squareCompat
        (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)
        p y sz w = _
  rw [← hy, ← hw]
  rw [diamondOddLiteral_AConstraint_reindexed hb hc hd]
  rw [diamondOddLiteral_squareCompat_reindexed hb hc hd]
  rw [diamondOddLiteralSourceMap_abwGauge_pointwise hb hc hd A B W]
  simp only [Equiv.apply_symm_apply, add_sub_cancel_right]

private theorem odd_sum_gauged_vec_headTail
    {n k : Nat} [NeZero n] (hk : 0 < k)
    (f : Vec n k → F) :
    (∑ v : Vec n k, f v) =
      ∑ tail : PVec n k, ∑ head : I n,
        f ((diamondOddVecHeadTailEquiv hk).symm
          (head - vecSum tail, tail)) := by
  rw [odd_sum_vec_headTail hk, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tail _
  let e : I n ≃ I n := Equiv.addRight (vecSum tail)
  apply Fintype.sum_equiv e
  intro head
  simp [e]

private theorem diamondOddLiteralSourceMap_eq_preC_coefficient
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c)
    (p : PVec n a) (yt : PVec n b) (wt : PVec n d)
    (i j k : I n) :
    diamondOddLiteralSourceMap
        (diamondOddABWGaugeEquiv hb hc hd (A, B, W))
        p yt wt i j k =
      diamondEvenPAConstraint
          (n := n) (a := a) (b := b) (c := c) (d := d) A
          p
          ((diamondOddVecHeadTailEquiv hb).symm
            (i - vecSum yt, yt))
          j
          ((diamondOddVecHeadTailEquiv hd).symm
            (k - vecSum wt, wt))
        +
      squareCompat
          (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)
          p
          ((diamondOddVecHeadTailEquiv hb).symm
            (i - vecSum yt, yt))
          j
          ((diamondOddVecHeadTailEquiv hd).symm
            (k - vecSum wt, wt)) := by
  rw [diamondOddLiteralSourceMap_abwGauge_pointwise hb hc hd A B W]
  rw [← diamondOddLiteral_AConstraint_reindexed
    (p := p) hb hc hd A yt wt (i - vecSum yt) j (k - vecSum wt)]
  congr 1
  have hs := diamondOddLiteral_squareCompat_reindexed
    (p := p) hb hc hd B W yt wt (i - vecSum yt) j (k - vecSum wt)
  simp only [sub_add_cancel] at hs
  exact hs.symm

private theorem diamondOdd_coeffApply_reindexed
    {n a b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (R C : CFun4 n a b d) :
    coeffApply (cFun4Equiv n a b d R) (cFun4Equiv n a b d C) =
      ∑ p : PVec n a, ∑ yt : PVec n b, ∑ wt : PVec n d,
        cubeDot
          (fun i j k =>
            R p
              ((diamondOddVecHeadTailEquiv hb).symm
                (i - vecSum yt, yt))
              j
              ((diamondOddVecHeadTailEquiv hd).symm
                (k - vecSum wt, wt)))
          (diamondOddCGaugeEquiv hb hd C p yt wt) := by
  unfold coeffApply cFun4Equiv
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  rw [odd_sum_gauged_vec_headTail hb]
  apply Finset.sum_congr rfl
  intro yt _
  simp_rw [odd_sum_gauged_vec_headTail hd]
  calc
    (∑ i : I n, ∑ j : I n, ∑ wt : PVec n d, ∑ k : I n,
        C p
            ((diamondOddVecHeadTailEquiv hb).symm
              (i - vecSum yt, yt))
            j
            ((diamondOddVecHeadTailEquiv hd).symm
              (k - vecSum wt, wt))
          *
        R p
            ((diamondOddVecHeadTailEquiv hb).symm
              (i - vecSum yt, yt))
            j
            ((diamondOddVecHeadTailEquiv hd).symm
              (k - vecSum wt, wt))) =
      ∑ i : I n, ∑ wt : PVec n d, ∑ j : I n, ∑ k : I n,
        C p
            ((diamondOddVecHeadTailEquiv hb).symm
              (i - vecSum yt, yt))
            j
            ((diamondOddVecHeadTailEquiv hd).symm
              (k - vecSum wt, wt))
          *
        R p
            ((diamondOddVecHeadTailEquiv hb).symm
              (i - vecSum yt, yt))
            j
            ((diamondOddVecHeadTailEquiv hd).symm
              (k - vecSum wt, wt)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ =
      ∑ wt : PVec n d, ∑ i : I n, ∑ j : I n, ∑ k : I n,
        C p
            ((diamondOddVecHeadTailEquiv hb).symm
              (i - vecSum yt, yt))
            j
            ((diamondOddVecHeadTailEquiv hd).symm
              (k - vecSum wt, wt))
          *
        R p
            ((diamondOddVecHeadTailEquiv hb).symm
              (i - vecSum yt, yt))
            j
            ((diamondOddVecHeadTailEquiv hd).symm
              (k - vecSum wt, wt)) := by
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro wt _
      simp_rw [cubeDot, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      simp only [diamondOddCGaugeEquiv_apply,
        diamondOddCPassiveCubeEquiv_apply]
      ring

private theorem diamondCPhaseCoeffClean_eq_preC_coeffApply
    {n a b c d : Nat} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) (C : CFun4 n a b d) :
    diamondCPhaseCoeffClean A B W C =
      coeffApply
        (cFun4Equiv n a b d
          (diamondEvenPAConstraint
              (n := n) (a := a) (b := b) (c := c) (d := d) A
            +
           squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
        (cFun4Equiv n a b d C) := by
  change
    coeffApplyA
        (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) A
      +
      coeffApply
        (cFun4Equiv n a b d
          (squareCompat
            (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
        (cFun4Equiv n a b d C) = _
  rw [← coeffApply_diamondEvenPAConstraint_eq_coeffApplyA_KCMap]
  unfold coeffApply
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rcases q with ⟨p, y, j, w⟩
  change
    C p y j w *
          diamondEvenPAConstraint
            (n := n) (a := a) (b := b) (c := c) (d := d) A p y j w
        +
        C p y j w *
          squareCompat
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (B, W) p y j w =
      C p y j w *
        (diamondEvenPAConstraint
            (n := n) (a := a) (b := b) (c := c) (d := d) A p y j w
          +
         squareCompat
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (B, W) p y j w)
  ring

private theorem diamondOddLiteral_pairing_core
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) (C : CFun4 n a b d) :
    diamondCPhaseCoeffClean A B W C =
      ∑ p : PVec n a, ∑ yt : PVec n b, ∑ wt : PVec n d,
        cubeDot
          (diamondOddLiteralSourceMap
            (diamondOddABWGaugeEquiv hb hc hd (A, B, W)) p yt wt)
          (diamondOddCGaugeEquiv hb hd C p yt wt) := by
  rw [diamondCPhaseCoeffClean_eq_preC_coeffApply]
  rw [diamondOdd_coeffApply_reindexed hb hd]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro yt _
  apply Finset.sum_congr rfl
  intro wt _
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  simp only [Pi.add_apply]
  rw [diamondOddLiteralSourceMap_eq_preC_coefficient
    hb hc hd A B W]

/-- The production C coefficient is the gauged source/C pairing. -/
theorem diamondPreCMap_apply_eq_oddLiteral_pairing
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) (C : CFun4 n a b d) :
    diamondPreCMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (A, B, W) C =
      ∑ p : PVec n a, ∑ yt : PVec n b, ∑ wt : PVec n d,
        cubeDot
          (diamondOddLiteralSourceMap
            (diamondOddABWGaugeEquiv hb hc hd (A, B, W)) p yt wt)
          (diamondOddCGaugeEquiv hb hd C p yt wt) := by
  exact diamondOddLiteral_pairing_core hb hc hd A B W C

/-- The cleaned eliminated-C coefficient has the same gauged pairing. -/
theorem diamondCPhaseCoeffClean_eq_oddLiteral_pairing
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) (C : CFun4 n a b d) :
    diamondCPhaseCoeffClean A B W C =
      ∑ p : PVec n a, ∑ yt : PVec n b, ∑ wt : PVec n d,
        cubeDot
          (diamondOddLiteralSourceMap
            (diamondOddABWGaugeEquiv hb hc hd (A, B, W)) p yt wt)
          (diamondOddCGaugeEquiv hb hd C p yt wt) := by
  exact diamondOddLiteral_pairing_core hb hc hd A B W C

/-- Vanishing of every eliminated-C coefficient is exactly the gauged source. -/
theorem diamondCPhaseCoeffClean_forall_zero_iff_oddLiteralSourceMap
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) :
    (∀ C : CFun4 n a b d, diamondCPhaseCoeffClean A B W C = 0) ↔
      diamondOddLiteralSourceMap
        (diamondOddABWGaugeEquiv hb hc hd (A, B, W)) = 0 := by
  rw [← diamondPreCMap_eq_zero_iff_oddLiteralSourceMap
    hb hc hd (A, B, W)]
  constructor
  · intro h
    apply LinearMap.ext
    intro C
    exact h C
  · intro h C
    have hC := congrArg
      (fun L : CFun4 n a b d →ₗ[F] F => L C) h
    exact hC

private def diamondOddCubeShift
    {n : Nat} [NeZero n] (ui uj uk : I n)
    (X : CyclicCube n) : CyclicCube n :=
  fun i j k => X (i - ui) (j - uj) (k - uk)

private theorem diamondOddCubeShift_pairing_same
    {n : Nat} [NeZero n] (ui uj uk : I n)
    (X Y : CyclicCube n) :
    cubeDot
        (diamondOddCubeShift ui uj uk X)
        (diamondOddCubeShift ui uj uk Y) =
      cubeDot X Y := by
  classical
  unfold cubeDot
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.addRight (-ui))
      (Equiv.prodCongr (Equiv.addRight (-uj))
        (Equiv.addRight (-uk)))
  apply Fintype.sum_equiv e
  intro q
  simp [e, diamondOddCubeShift, sub_eq_add_neg]

private theorem diamondOddLiteral_gauged_phase_cube
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d) :
    cubeDot
        (diamondOddAPassiveCubeEquiv hb hc hd A yt zt wt)
        (fun i j k =>
          ∑ p : PVec n a,
            (cubeDiffI
                  (diamondOddBPassiveCubeEquiv hc hd B p zt wt)
                  (i + vecSum yt) j k
              +
             cubeDiffK
                  (diamondOddWPassiveCubeEquiv hb hc W p yt zt)
                  i j (k + vecSum wt))) =
      cubeDot
        (diamondOddAGaugeEquiv hb hc hd A yt zt wt)
        (∑ p : PVec n a,
          (cubeDiffI (diamondOddBGaugeEquiv hc hd B p zt wt) +
           cubeDiffK (diamondOddWGaugeEquiv hb hc W p yt zt))) := by
  let X : CyclicCube n :=
    diamondOddAPassiveCubeEquiv hb hc hd A yt zt wt
  let Y : CyclicCube n :=
    fun i j k =>
      ∑ p : PVec n a,
        (cubeDiffI
              (diamondOddBPassiveCubeEquiv hc hd B p zt wt)
              (i + vecSum yt) j k
          +
         cubeDiffK
              (diamondOddWPassiveCubeEquiv hb hc W p yt zt)
              i j (k + vecSum wt))
  have hA :
      diamondOddAGaugeEquiv hb hc hd A yt zt wt =
        diamondOddCubeShift
          (vecSum yt) (vecSum zt) (vecSum wt) X := by
    funext i j k
    rfl
  have hBW :
      (∑ p : PVec n a,
          (cubeDiffI (diamondOddBGaugeEquiv hc hd B p zt wt) +
           cubeDiffK (diamondOddWGaugeEquiv hb hc W p yt zt))) =
        diamondOddCubeShift
          (vecSum yt) (vecSum zt) (vecSum wt) Y := by
    funext i j k
    simp only [Finset.sum_apply, Pi.add_apply,
      odd_cubeDiffI_apply, odd_cubeDiffK_apply,
      diamondOddBGaugeEquiv_apply, diamondOddWGaugeEquiv_apply]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    · congr 1 <;> abel
    · congr 1 <;> abel
  rw [hA, hBW, diamondOddCubeShift_pairing_same]

/-- The literal phase on the gauged ambient coordinates. -/
noncomputable def diamondOddLiteralAmbientQ
    {n a b c d : Nat} [NeZero n]
    (u : DiamondOddLiteralAmbient n a b c d) : F :=
  ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
    cubeDot
      (u.1 yt zt wt)
      (∑ p : PVec n a,
        (cubeDiffI (u.2.1 p zt wt) +
         cubeDiffK (u.2.2 p yt zt)))

@[simp] theorem diamondOddLiteralAmbientQ_apply
    {n a b c d : Nat} [NeZero n]
    (u : DiamondOddLiteralAmbient n a b c d) :
    diamondOddLiteralAmbientQ u =
      ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        cubeDot
          (u.1 yt zt wt)
          (∑ p : PVec n a,
            (cubeDiffI (u.2.1 p zt wt) +
             cubeDiffK (u.2.2 p yt zt))) := rfl

/-- The production residual phase transported to the gauged ambient data. -/
theorem diamondPreCQ_eq_oddLiteralAmbientQ
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : DiamondPreCSource n a b c d) :
    diamondPreCQ x =
      diamondOddLiteralAmbientQ
        (diamondOddABWGaugeEquiv hb hc hd x.1) := by
  rw [diamondOddLiteral_q_eq_reindexed hb hc hd]
  unfold diamondOddLiteralAmbientQ
  apply Finset.sum_congr rfl
  intro yt _
  apply Finset.sum_congr rfl
  intro zt _
  apply Finset.sum_congr rfl
  intro wt _
  exact diamondOddLiteral_gauged_phase_cube
    hb hc hd x.1.1 x.1.2.1 x.1.2.2 yt zt wt

/-- Restriction of the same ambient phase to the gauged source kernel. -/
noncomputable def diamondOddLiteralQ
    {n a b c d : Nat} [NeZero n]
    (u : DiamondOddLiteralSource n a b c d) : F :=
  diamondOddLiteralAmbientQ u.1

@[simp] theorem diamondOddLiteralQ_apply
    {n a b c d : Nat} [NeZero n]
    (u : DiamondOddLiteralSource n a b c d) :
    diamondOddLiteralQ u =
      ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        cubeDot
          (u.1.1 yt zt wt)
          (∑ p : PVec n a,
            (cubeDiffI (u.1.2.1 p zt wt) +
             cubeDiffK (u.1.2.2 p yt zt))) := rfl

/-- The production phase transported all the way to the gauged kernel. -/
theorem diamondPreCQ_eq_oddLiteralQ
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : DiamondPreCSource n a b c d) :
    diamondPreCQ x =
      diamondOddLiteralQ
        (diamondOddLiteralSourceEquiv hb hc hd x) := by
  rw [diamondPreCQ_eq_oddLiteralAmbientQ hb hc hd x]
  rfl

end

end Core4loop.SquareDiagonal.DirectWitt
