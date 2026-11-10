import Core4loop.SquareDiagonal.EvenP.CrossProjection
import Core4loop.SquareDiagonal.EvenP.PointedValueNormalForm
import Core4loop.SquareDiagonal.EvenP.CubeOrbit

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

noncomputable def diamondVecHeadTailEquiv
    {n k : Nat} [NeZero n] (hk : 0 < k) :
    Vec n k ≃ I n × PVec n k := by
  simpa [PVec, Nat.sub_add_cancel hk] using vecSuccEquiv n (k - 1)

noncomputable def diamondBRootCubeEquiv
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    BFun4 n 1 c d ≃ₗ[F]
      (PVec n c → PVec n d → CyclicCube n) where
  toFun B zt wt i j k :=
    B zeroVec i
      ((diamondVecHeadTailEquiv hc).symm (j, zt))
      ((diamondVecHeadTailEquiv hd).symm (k, wt))
  invFun G _p i z w :=
    G (diamondVecHeadTailEquiv hc z).2
      (diamondVecHeadTailEquiv hd w).2
      i
      (diamondVecHeadTailEquiv hc z).1
      (diamondVecHeadTailEquiv hd w).1
  left_inv B := by
    funext p i z w
    have hp : p = (zeroVec : PVec n 1) := by
      funext q
      exact Fin.elim0 q
    subst p
    simp
  right_inv G := by
    funext zt wt i j k
    simp
  map_add' B B' := by
    rfl
  map_smul' r B := by
    rfl

noncomputable def diamondWRootCubeEquiv
    {n b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    WFun4 n 1 b c ≃ₗ[F]
      (PVec n b → PVec n c → CyclicCube n) where
  toFun W yt zt i j k :=
    W zeroVec
      ((diamondVecHeadTailEquiv hb).symm (i, yt))
      ((diamondVecHeadTailEquiv hc).symm (j, zt))
      k
  invFun G _p y z k :=
    G (diamondVecHeadTailEquiv hb y).2
      (diamondVecHeadTailEquiv hc z).2
      (diamondVecHeadTailEquiv hb y).1
      (diamondVecHeadTailEquiv hc z).1
      k
  left_inv W := by
    funext p y z k
    have hp : p = (zeroVec : PVec n 1) := by
      funext q
      exact Fin.elim0 q
    subst p
    simp
  right_inv G := by
    funext yt zt i j k
    simp
  map_add' W W' := by
    rfl
  map_smul' r W := by
    rfl

noncomputable def diamondARootCubeEquiv
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    AFun4 n b c d ≃ₗ[F]
      (PVec n b → PVec n c → PVec n d → CyclicCube n) where
  toFun A yt zt wt i j k :=
    A
      ((diamondVecHeadTailEquiv hb).symm (i, yt))
      ((diamondVecHeadTailEquiv hc).symm (j, zt))
      ((diamondVecHeadTailEquiv hd).symm (k, wt))
  invFun G y z w :=
    G (diamondVecHeadTailEquiv hb y).2
      (diamondVecHeadTailEquiv hc z).2
      (diamondVecHeadTailEquiv hd w).2
      (diamondVecHeadTailEquiv hb y).1
      (diamondVecHeadTailEquiv hc z).1
      (diamondVecHeadTailEquiv hd w).1
  left_inv A := by
    funext y z w
    simp
  right_inv G := by
    funext yt zt wt i j k
    simp
  map_add' A A' := by
    rfl
  map_smul' r A := by
    rfl

@[simp] theorem diamondVecHeadTailEquiv_apply
    {n k : Nat} [NeZero n] (hk : 0 < k) (v : Vec n k) :
    diamondVecHeadTailEquiv hk v =
      (v ⟨0, hk⟩, fun q : Fin (k - 1) =>
        v ⟨q.1 + 1, by omega⟩) := by
  cases k with
  | zero => omega
  | succ k => rfl

@[simp] theorem diamondBRootCubeEquiv_apply
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    diamondBRootCubeEquiv hc hd B zt wt i j k =
      B zeroVec i
        ((diamondVecHeadTailEquiv hc).symm (j, zt))
        ((diamondVecHeadTailEquiv hd).symm (k, wt)) := by
  rfl

@[simp] theorem diamondWRootCubeEquiv_apply
    {n b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (W : WFun4 n 1 b c) (yt : PVec n b) (zt : PVec n c)
    (i j k : I n) :
    diamondWRootCubeEquiv hb hc W yt zt i j k =
      W zeroVec
        ((diamondVecHeadTailEquiv hb).symm (i, yt))
        ((diamondVecHeadTailEquiv hc).symm (j, zt))
        k := by
  rfl

@[simp] theorem diamondARootCubeEquiv_apply
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    diamondARootCubeEquiv hb hc hd A yt zt wt i j k =
      A
        ((diamondVecHeadTailEquiv hb).symm (i, yt))
        ((diamondVecHeadTailEquiv hc).symm (j, zt))
        ((diamondVecHeadTailEquiv hd).symm (k, wt)) := by
  rfl

private theorem vecSum_headTail_symm
    {n k : Nat} [NeZero n] (hk : 0 < k)
    (head : I n) (tail : PVec n k) :
    vecSum ((diamondVecHeadTailEquiv hk).symm (head, tail)) =
      head + vecSum tail := by
  cases k with
  | zero => omega
  | succ k =>
      exact vecSum_vecCons head tail

private theorem sum_vec_headTail
    {n k : Nat} [NeZero n] (hk : 0 < k)
    (f : Vec n k → F) :
    (∑ v : Vec n k, f v) =
      ∑ head : I n, ∑ tail : PVec n k,
        f ((diamondVecHeadTailEquiv hk).symm (head, tail)) := by
  calc
    (∑ v : Vec n k, f v) =
        ∑ x : I n × PVec n k,
          f ((diamondVecHeadTailEquiv hk).symm x) := by
      refine Fintype.sum_equiv (diamondVecHeadTailEquiv hk)
        f
        (fun x => f ((diamondVecHeadTailEquiv hk).symm x)) ?_
      intro v
      exact congrArg f ((diamondVecHeadTailEquiv hk).symm_apply_apply v).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]

private theorem sum_if_add_eq
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

private theorem sum_if_add_add_one_eq
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

@[simp] private theorem cubeDiffI_apply_local
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffI f i j k = f i j k + f (i + 1) j k := by
  rfl

@[simp] private theorem cubeDiffK_apply_local
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffK f i j k = f i j k + f i j (k + 1) := by
  simp

@[simp] private theorem cubeDiffJInv_apply_local
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

@[simp] private theorem cubeDiffP_apply_local
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffP f i j k = f i j k + f (i + 1) (j - 1) k := by
  simp

@[simp] private theorem cubeDiffR_apply_local
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffR f i j k = f i j k + f i (j - 1) (k + 1) := by
  simp

theorem diamondCubeReindex_squareCompat
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (W : WFun4 n 1 b c)
    (yt : PVec n b) (wt : PVec n d) (i sz k : I n) :
    squareCompat (n := n) (a := 1) (b := b) (c := c) (d := d) (B, W)
        zeroVec
        ((diamondVecHeadTailEquiv hb).symm (i, yt))
        sz
        ((diamondVecHeadTailEquiv hd).symm (k, wt))
      =
    ∑ zt : PVec n c,
      (cubeDiffP (diamondBRootCubeEquiv hc hd B zt wt)
          (i + vecSum yt) (sz - vecSum zt) k
       +
       cubeDiffR (diamondWRootCubeEquiv hb hc W yt zt)
          i (sz - vecSum zt) (k + vecSum wt)) := by
  unfold squareCompat squareCompatFun betaB gammaB xiW zetaW
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_vec_headTail hc, sum_vec_headTail hc]
  simp_rw [vecSum_headTail_symm]
  conv_lhs =>
    congr
    · rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
  simp_rw [sum_if_add_eq, sum_if_add_add_one_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro zt _
  simp only [cubeDiffP_apply_local, cubeDiffR_apply_local,
    diamondBRootCubeEquiv_apply, diamondWRootCubeEquiv_apply]
  abel

theorem diamondCubeReindex_AConstraint
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d)
    (yt : PVec n b) (wt : PVec n d) (i sz k : I n) :
    diamondEvenPAConstraint
        (n := n) (a := 1) (b := b) (c := c) (d := d) A
        zeroVec
        ((diamondVecHeadTailEquiv hb).symm (i, yt))
        sz
        ((diamondVecHeadTailEquiv hd).symm (k, wt))
      =
    ∑ zt : PVec n c,
      cubeDiffJInv (diamondARootCubeEquiv hb hc hd A yt zt wt)
        i (sz - vecSum zt) k := by
  unfold diamondEvenPAConstraint
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_vec_headTail hc, sum_vec_headTail hc]
  simp_rw [vecSum_headTail_symm]
  conv_lhs =>
    congr
    · rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
  simp_rw [sum_if_add_eq, sum_if_add_add_one_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro zt _
  simp only [cubeDiffJInv_apply_local, diamondARootCubeEquiv_apply]

theorem diamondCubeReindex_leftRoot
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (l : DiamondEvenPLeft n b c d)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    diamondEvenPLeftRoot l
        ((diamondVecHeadTailEquiv hb).symm (i, yt))
        ((diamondVecHeadTailEquiv hc).symm (j, zt))
        ((diamondVecHeadTailEquiv hd).symm (k, wt))
      =
    cubeDiffI (diamondBRootCubeEquiv hc hd l.1.1 zt wt)
        (i + vecSum yt) j k
      +
    cubeDiffK (diamondWRootCubeEquiv hb hc l.1.2 yt zt)
        i j (k + vecSum wt) := by
  unfold diamondEvenPLeftRoot KBMap KWMap dyB dwW
    betaB gammaB xiW zetaW
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
    · simp only [cubeDiffI_apply_local, cubeDiffK_apply_local,
        diamondBRootCubeEquiv_apply, diamondWRootCubeEquiv_apply]
      rw [vecSum_headTail_symm hb, vecSum_headTail_symm hd]
    · intro p _ hp
      exact (hp (pVec_one_eq_zeroVec p)).elim
    · simp
  · intro p _ hp
    exact (hp (pVec_one_eq_zeroVec p)).elim
  · simp

private theorem sum_six_reorder
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

theorem diamondCubeReindex_rootPairing
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (R : RootTarget n b c d) (A : AFun4 n b c d) :
    coeffApplyA R A =
      ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        cubeDot
          (diamondARootCubeEquiv hb hc hd A yt zt wt)
          (diamondARootCubeEquiv hb hc hd R yt zt wt) := by
  rw [coeffApplyA_eq_sum]
  rw [sum_vec_headTail hb]
  simp_rw [sum_vec_headTail hc, sum_vec_headTail hd]
  simp_rw [cubeDot, Fintype.sum_prod_type]
  simp only [diamondARootCubeEquiv_apply]
  exact sum_six_reorder (fun i yt j zt k wt =>
    A ((diamondVecHeadTailEquiv hb).symm (i, yt))
        ((diamondVecHeadTailEquiv hc).symm (j, zt))
        ((diamondVecHeadTailEquiv hd).symm (k, wt)) *
      R ((diamondVecHeadTailEquiv hb).symm (i, yt))
        ((diamondVecHeadTailEquiv hc).symm (j, zt))
        ((diamondVecHeadTailEquiv hd).symm (k, wt)))

noncomputable def diamondEvenAxisSrcCoordEquiv
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Even n) (hk2 : 2 ≤ k) :
    (PVec n k → V) ≃ₗ[F]
      PointedEvenValueCoords
        (PVec n k) V (zeroVec : PVec n k) :=
  pointedSrcEvenValueEquiv
    (PVec n k) V (zeroVec : PVec n k) (even_card_PVec hn hk2)

noncomputable def diamondEvenAxisDualCoordEquiv
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Even n) (hk2 : 2 ≤ k) :
    (PVec n k → V) ≃ₗ[F]
      PointedEvenValueCoords
        (PVec n k) V (zeroVec : PVec n k) :=
  pointedDualEvenValueEquiv
    (PVec n k) V (zeroVec : PVec n k) (even_card_PVec hn hk2)

end

end Core4loop.SquareDiagonal.EvenP
