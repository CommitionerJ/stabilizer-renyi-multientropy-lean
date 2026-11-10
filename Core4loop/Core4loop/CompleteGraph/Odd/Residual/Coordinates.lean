import Core4loop.CompleteGraph.DirectWitt.AddedBWPhase
import Core4loop.CompleteGraph.CubeCompat.KappaCycle
import Core4loop.SquareDiagonal.DirectWitt.OddChannelProduct

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.Odd

open Core4loop
open Core4loop.CompleteGraph.CubeCompat
open Core4loop.SquareDiagonal.DirectWitt

noncomputable section

attribute [local instance] Fintype.ofFinite

/-- The literal B-W phase on the four supported odd channel rows. -/
noncomputable def k4OddChannelAddedQ
    {n a b c d : Nat} [NeZero n]
    (rows : DiamondOddChannelProduct n a b c d) : F :=
  k4CubeKappa
      (rows .ssss).1.2.1
      (rows .ssss).1.2.2 +
    (∑ zt : DiamondOddAxisTail n c,
      k4CubeKappa
        ((rows .ssts zt).2.1)
        (diamondOddAxisTailJ (CyclicCube n)
          (fun zt' => (rows .ssts zt').2.2) zt)) +
    (∑ pt : DiamondOddAxisTail n a,
      k4CubeKappa
        (((rows .tsss).1 pt).1)
        (diamondOddAxisTailJ (CyclicCube n)
          (fun pt' => ((rows .tsss).1 pt').2) pt)) +
    ∑ pt : DiamondOddAxisTail n a,
      ∑ zt : DiamondOddAxisTail n c,
        k4CubeKappa
          ((rows .tsts pt zt).1)
          (diamondOddTensorTailJ
            (zeroVec : PVec n a)
            (zeroVec : PVec n c)
            (fun pt' zt' => (rows .tsts pt' zt').2)
            pt zt)

private noncomputable def k4CubeKappaBilin
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n →ₗ[F] F where
  toFun B :=
    { toFun := fun W => k4CubeKappa B W
      map_add' := by
        intro W₁ W₂
        unfold k4CubeKappa
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro q _
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro r W
        change k4CubeKappa B (r • W) = r • k4CubeKappa B W
        unfold k4CubeKappa
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring }
  map_add' := by
    intro B₁ B₂
    apply LinearMap.ext
    intro W
    change
      k4CubeKappa (B₁ + B₂) W =
        k4CubeKappa B₁ W + k4CubeKappa B₂ W
    unfold k4CubeKappa
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro r B
    apply LinearMap.ext
    intro W
    change k4CubeKappa (r • B) W = r • k4CubeKappa B W
    unfold k4CubeKappa
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring

@[simp] private theorem k4CubeKappaBilin_apply
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappaBilin B W = k4CubeKappa B W :=
  rfl

private theorem k4Odd_vecSum_headTail_symm
    {n k : Nat} [NeZero n] (hk : 0 < k)
    (head : I n) (tail : PVec n k) :
    vecSum ((diamondOddVecHeadTailEquiv hk).symm (head, tail)) =
      head + vecSum tail := by
  cases k with
  | zero => omega
  | succ k =>
      exact vecSum_vecCons head tail

private theorem k4Odd_sum_vec_headTail
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

private theorem k4Odd_sum_six_reorder
    {α β γ δ ε ζ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [Fintype ζ]
    (f : α → β → γ → δ → ε → ζ → F) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, ∑ e : ε, ∑ z : ζ,
        f a b c d e z) =
      ∑ b : β, ∑ d : δ, ∑ z : ζ, ∑ a : α, ∑ c : γ, ∑ e : ε,
        f a b c d e z := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ a : α, ∑ c : γ, ∑ d : δ, ∑ e : ε, ∑ z : ζ,
        f a b c d e z) =
        ∑ a : α, ∑ d : δ, ∑ c : γ, ∑ e : ε, ∑ z : ζ,
          f a b c d e z := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ d : δ, ∑ a : α, ∑ c : γ, ∑ e : ε, ∑ z : ζ,
          f a b c d e z := by
      rw [Finset.sum_comm]
    _ = ∑ d : δ, ∑ z : ζ, ∑ a : α, ∑ c : γ, ∑ e : ε,
          f a b c d e z := by
      apply Finset.sum_congr rfl
      intro d _
      calc
        (∑ a : α, ∑ c : γ, ∑ e : ε, ∑ z : ζ,
            f a b c d e z) =
            ∑ a : α, ∑ c : γ, ∑ z : ζ, ∑ e : ε,
              f a b c d e z := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]
        _ = ∑ a : α, ∑ z : ζ, ∑ c : γ, ∑ e : ε,
              f a b c d e z := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
        _ = ∑ z : ζ, ∑ a : α, ∑ c : γ, ∑ e : ε,
              f a b c d e z := by
          rw [Finset.sum_comm]

private theorem k4BW_gauged_cube
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (p : PVec n a) (yt : PVec n b)
    (zt : PVec n c) (wt : PVec n d) :
    (∑ i : I n, ∑ j : I n, ∑ k : I n,
      (diamondOddBPassiveCubeEquiv hc hd B p zt wt
            (i + vecSum yt) j k *
          diamondOddWPassiveCubeEquiv hb hc W p yt zt
            i j (k + vecSum wt) +
        diamondOddBPassiveCubeEquiv hc hd B p zt wt
            (i + vecSum yt + 1) j k *
          diamondOddWPassiveCubeEquiv hb hc W p yt zt
            i j (k + vecSum wt + 1))) =
      k4CubeKappa
        (diamondOddBGaugeEquiv hc hd B p zt wt)
        (diamondOddWGaugeEquiv hb hc W p yt zt) := by
  unfold k4CubeKappa
  have hpack (f : I n → I n → I n → F) :
      (∑ i, ∑ j, ∑ k, f i j k) =
        ∑ q : I n × I n × I n, f q.1 q.2.1 q.2.2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.sum_prod_type]
  rw [hpack]
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.addRight (vecSum yt))
      (Equiv.prodCongr (Equiv.addRight (vecSum zt))
        (Equiv.addRight (vecSum wt)))
  apply Fintype.sum_equiv e
  intro q
  simp [e, sub_eq_add_neg]

private theorem k4BWPhaseClean_eq_gauged
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    k4BWPhaseClean B W =
      ∑ p : PVec n a,
        ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
          k4CubeKappa
            (diamondOddBGaugeEquiv hc hd B p zt wt)
            (diamondOddWGaugeEquiv hb hc W p yt zt) := by
  unfold k4BWPhaseClean betaB gammaB xiW zetaW
  apply Finset.sum_congr rfl
  intro p _
  rw [k4Odd_sum_vec_headTail hb]
  simp_rw [k4Odd_sum_vec_headTail hc, k4Odd_sum_vec_headTail hd]
  rw [k4Odd_sum_six_reorder]
  apply Finset.sum_congr rfl
  intro yt _
  apply Finset.sum_congr rfl
  intro zt _
  apply Finset.sum_congr rfl
  intro wt _
  simp_rw [← diamondOddBPassiveCubeEquiv_apply,
    ← diamondOddWPassiveCubeEquiv_apply]
  simp_rw [k4Odd_vecSum_headTail_symm hb,
    k4Odd_vecSum_headTail_symm hd]
  exact k4BW_gauged_cube hb hc hd B W p yt zt wt

private theorem k4BW_gauged_eq_folded
    {n a b c d : Nat} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (∑ p : PVec n a,
      ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        k4CubeKappa
          (diamondOddBGaugeEquiv hc hd B p zt wt)
          (diamondOddWGaugeEquiv hb hc W p yt zt)) =
      ∑ p : PVec n a, ∑ zt : PVec n c,
        k4CubeKappa
          (∑ wt : PVec n d,
            diamondOddBGaugeEquiv hc hd B p zt wt)
          (∑ yt : PVec n b,
            diamondOddWGaugeEquiv hb hc W p yt zt) := by
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro zt _
  change
    (∑ yt : PVec n b, ∑ wt : PVec n d,
      k4CubeKappaBilin
        (diamondOddBGaugeEquiv hc hd B p zt wt)
        (diamondOddWGaugeEquiv hb hc W p yt zt)) =
      k4CubeKappaBilin
        (∑ wt : PVec n d,
          diamondOddBGaugeEquiv hc hd B p zt wt)
        (∑ yt : PVec n b,
          diamondOddWGaugeEquiv hb hc W p yt zt)
  rw [Finset.sum_comm]
  calc
    (∑ wt : PVec n d, ∑ yt : PVec n b,
        k4CubeKappaBilin
          (diamondOddBGaugeEquiv hc hd B p zt wt)
          (diamondOddWGaugeEquiv hb hc W p yt zt)) =
        ∑ wt : PVec n d,
          k4CubeKappaBilin
            (diamondOddBGaugeEquiv hc hd B p zt wt)
            (∑ yt : PVec n b,
              diamondOddWGaugeEquiv hb hc W p yt zt) := by
      apply Finset.sum_congr rfl
      intro wt _
      exact
        (map_sum
          (k4CubeKappaBilin
            (diamondOddBGaugeEquiv hc hd B p zt wt))
          (fun yt : PVec n b =>
            diamondOddWGaugeEquiv hb hc W p yt zt)
          Finset.univ).symm
    _ = _ := by
      exact
        (map_sum
          (LinearMap.flip k4CubeKappaBilin
            (∑ yt : PVec n b,
              diamondOddWGaugeEquiv hb hc W p yt zt))
          (fun wt : PVec n d =>
            diamondOddBGaugeEquiv hc hd B p zt wt)
          Finset.univ).symm

private theorem k4OddAxis_pairing
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (beta : V →ₗ[F] V →ₗ[F] F)
    (f g : PVec n k → V) :
    (∑ s, beta (f s) (g s)) =
      beta
          (diamondOddAxisSrcChannelEquiv V hn f diamondOddChannelS)
          (diamondOddAxisSrcChannelEquiv V hn g diamondOddChannelS) +
        ∑ t : DiamondOddAxisTail n k,
          beta
            (diamondOddAxisSrcChannelEquiv V hn f
              (diamondOddChannelT t))
            (diamondOddAxisTailJ V
              (fun v =>
                diamondOddAxisSrcChannelEquiv V hn g
                  (diamondOddChannelT v)) t) := by
  rw [pointedOddValue_pairing_source_J
    (zeroVec : PVec n k) (odd_card_PVec hn) beta f g]
  congr 1
  refine @Fintype.sum_equiv
    (DiamondOddAxisTail n k) (DiamondOddAxisTail n k) F
    ?_ ?_ ?_ (Equiv.refl _) _ _ ?_
  intro t
  congr 1

private theorem k4OddAxisSrc_tailJ_comm
    {n k₁ k₂ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (g : DiamondOddAxisTail n k₁ → PVec n k₂ → V)
    (t₁ : DiamondOddAxisTail n k₁)
    (c₂ : DiamondOddAxisChannel n k₂) :
    diamondOddAxisSrcChannelEquiv V hn
        (diamondOddAxisTailJ (PVec n k₂ → V) g t₁) c₂ =
      diamondOddAxisTailJ V
        (fun v =>
          diamondOddAxisSrcChannelEquiv V hn (g v) c₂) t₁ := by
  rw [diamondOddAxisTailJ_apply, diamondOddAxisTailJ_apply]
  simp only [map_add, map_sum, Pi.add_apply, Finset.sum_apply]

private noncomputable def k4OddSumPiBilin
    (S V : Type*) [Fintype S]
    [AddCommGroup V] [Module F V]
    (beta : V →ₗ[F] V →ₗ[F] F) :
    (S → V) →ₗ[F] (S → V) →ₗ[F] F where
  toFun f :=
    { toFun := fun g => ∑ s, beta (f s) (g s)
      map_add' := by
        intro g h
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r g
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply,
          Finset.smul_sum] }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro h
    change
      (∑ s, beta (f s + g s) (h s)) =
        (∑ s, beta (f s) (h s)) + ∑ s, beta (g s) (h s)
    simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  map_smul' := by
    intro r f
    apply LinearMap.ext
    intro g
    change
      (∑ s, beta (r • f s) (g s)) =
        r • ∑ s, beta (f s) (g s)
    simp only [map_smul, LinearMap.smul_apply,
      Finset.smul_sum]

private noncomputable def k4OddTwoSrc
    {n k₁ k₂ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → V)
    (c₁ : DiamondOddAxisChannel n k₁)
    (c₂ : DiamondOddAxisChannel n k₂) : V :=
  diamondOddAxisSrcChannelEquiv V hn
    (diamondOddAxisSrcChannelEquiv (PVec n k₂ → V) hn f c₁) c₂

private theorem k4OddTailJ_commute
    {n k₁ k₂ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (f : DiamondOddAxisTail n k₁ → DiamondOddAxisTail n k₂ → V)
    (t₁ : DiamondOddAxisTail n k₁)
    (t₂ : DiamondOddAxisTail n k₂) :
    diamondOddAxisTailJ V
        (fun v₂ =>
          diamondOddAxisTailJ V (fun v₁ => f v₁ v₂) t₁) t₂ =
      diamondOddTensorTailJ
        (zeroVec : PVec n k₁) (zeroVec : PVec n k₂)
        f t₁ t₂ := by
  simp only [diamondOddAxisTailJ, diamondOddTensorTailJ,
    oddValueTailJ_apply, Pi.add_apply, Finset.sum_apply,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  abel_nf

private theorem k4OddTwo_axis_pairing
    {n k₁ k₂ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (beta : V →ₗ[F] V →ₗ[F] F)
    (f g : PVec n k₁ → PVec n k₂ → V) :
    (∑ s₁, ∑ s₂, beta (f s₁ s₂) (g s₁ s₂)) =
      beta
          (k4OddTwoSrc V hn f
            diamondOddChannelS diamondOddChannelS)
          (k4OddTwoSrc V hn g
            diamondOddChannelS diamondOddChannelS) +
        (∑ t₂ : DiamondOddAxisTail n k₂,
          beta
            (k4OddTwoSrc V hn f diamondOddChannelS
              (diamondOddChannelT t₂))
            (diamondOddAxisTailJ V
              (fun v =>
                k4OddTwoSrc V hn g diamondOddChannelS
                  (diamondOddChannelT v)) t₂)) +
        (∑ t₁ : DiamondOddAxisTail n k₁,
          beta
            (k4OddTwoSrc V hn f (diamondOddChannelT t₁)
              diamondOddChannelS)
            (diamondOddAxisTailJ V
              (fun v =>
                k4OddTwoSrc V hn g (diamondOddChannelT v)
                  diamondOddChannelS) t₁)) +
        ∑ t₁ : DiamondOddAxisTail n k₁,
          ∑ t₂ : DiamondOddAxisTail n k₂,
            beta
              (k4OddTwoSrc V hn f (diamondOddChannelT t₁)
                (diamondOddChannelT t₂))
              (diamondOddTensorTailJ
                (zeroVec : PVec n k₁) (zeroVec : PVec n k₂)
                (fun v₁ v₂ =>
                  k4OddTwoSrc V hn g (diamondOddChannelT v₁)
                    (diamondOddChannelT v₂)) t₁ t₂) := by
  change
    (∑ s₁,
      (k4OddSumPiBilin (PVec n k₂) V beta (f s₁)) (g s₁)) = _
  rw [k4OddAxis_pairing
    (V := PVec n k₂ → V) hn
    (k4OddSumPiBilin (PVec n k₂) V beta) f g]
  change
    (∑ s₂,
        beta
          ((diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → V) hn f diamondOddChannelS) s₂)
          ((diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → V) hn g diamondOddChannelS) s₂)) +
      (∑ t₁ : DiamondOddAxisTail n k₁,
        ∑ s₂,
          beta
            ((diamondOddAxisSrcChannelEquiv
              (PVec n k₂ → V) hn f
                (diamondOddChannelT t₁)) s₂)
            ((diamondOddAxisTailJ (PVec n k₂ → V)
              (fun v =>
                diamondOddAxisSrcChannelEquiv
                  (PVec n k₂ → V) hn g
                    (diamondOddChannelT v)) t₁) s₂)) = _
  rw [k4OddAxis_pairing V hn beta
    (diamondOddAxisSrcChannelEquiv
      (PVec n k₂ → V) hn f diamondOddChannelS)
    (diamondOddAxisSrcChannelEquiv
      (PVec n k₂ → V) hn g diamondOddChannelS)]
  simp only [k4OddTwoSrc]
  abel_nf
  rw [add_right_inj, add_right_inj]
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_equiv (Equiv.refl _) _ _ ?_
  intro t₁
  rw [k4OddAxis_pairing V hn beta
    (diamondOddAxisSrcChannelEquiv
      (PVec n k₂ → V) hn f (diamondOddChannelT t₁))
    (diamondOddAxisTailJ (PVec n k₂ → V)
      (fun v =>
        diamondOddAxisSrcChannelEquiv
          (PVec n k₂ → V) hn g (diamondOddChannelT v)) t₁)]
  rw [k4OddAxisSrc_tailJ_comm]
  congr 1
  apply Fintype.sum_equiv (Equiv.refl _) _ _ ?_
  intro t₂
  congr 1
  have hfun :
      (fun v₂ =>
        diamondOddAxisSrcChannelEquiv V hn
          (diamondOddAxisTailJ (PVec n k₂ → V)
            (fun v₁ =>
              diamondOddAxisSrcChannelEquiv
                (PVec n k₂ → V) hn g (diamondOddChannelT v₁)) t₁)
          (diamondOddChannelT v₂)) =
        (fun v₂ =>
          diamondOddAxisTailJ V
            (fun v₁ =>
              k4OddTwoSrc V hn g (diamondOddChannelT v₁)
                (diamondOddChannelT v₂)) t₁) := by
    funext v₂
    simpa only [k4OddTwoSrc] using
      k4OddAxisSrc_tailJ_comm V hn
        (fun v₁ =>
          diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → V) hn g (diamondOddChannelT v₁))
        t₁ (diamondOddChannelT v₂)
  rw [hfun]
  exact k4OddTailJ_commute V
    (fun v₁ v₂ =>
      k4OddTwoSrc V hn g (diamondOddChannelT v₁)
        (diamondOddChannelT v₂)) t₁ t₂

@[simp] private theorem k4OddAxisSrcChannelEquiv_pi_apply
    {n k : Nat} [NeZero n]
    (X V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (f : PVec n k → X → V)
    (q : DiamondOddAxisChannel n k) (x : X) :
    diamondOddAxisSrcChannelEquiv (X → V) hn f q x =
      diamondOddAxisSrcChannelEquiv V hn (fun s => f s x) q := by
  cases q with
  | none =>
      change
        diamondOddAxisSrcChannelEquiv (X → V) hn f
            diamondOddChannelS x =
          diamondOddAxisSrcChannelEquiv V hn (fun s => f s x)
            diamondOddChannelS
      simp only [diamondOddAxisSrcChannelEquiv_apply_S,
        Finset.sum_apply]
  | some t =>
      change
        diamondOddAxisSrcChannelEquiv (X → V) hn f
            (diamondOddChannelT t) x =
          diamondOddAxisSrcChannelEquiv V hn (fun s => f s x)
            (diamondOddChannelT t)
      simp only [diamondOddAxisSrcChannelEquiv_apply_T,
        Pi.add_apply, Finset.sum_apply]

private theorem k4OddTriple_sum_middle
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → PVec n k₃ → V)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₃ : DiamondOddAxisChannel n k₃) :
    diamondOddTripleSrcChannelEquiv V hn f
        q₁ diamondOddChannelS q₃ =
      diamondOddAxisSrcChannelEquiv V hn
        (fun x₃ =>
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => ∑ x₂, f x₁ x₂ x₃) q₁) q₃ := by
  change
    diamondOddAxisSrcChannelEquiv V hn
        (diamondOddAxisSrcChannelEquiv
          (PVec n k₃ → V) hn
          (diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → PVec n k₃ → V) hn f q₁)
          diamondOddChannelS) q₃ =
      _
  rw [diamondOddAxisSrcChannelEquiv_apply_S]
  apply congrArg
    (fun g : PVec n k₃ → V =>
      diamondOddAxisSrcChannelEquiv V hn g q₃)
  funext x₃
  cases q₁ with
  | none =>
      change
        (∑ x₂,
          diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → PVec n k₃ → V) hn f
              diamondOddChannelS x₂) x₃ =
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => ∑ x₂, f x₁ x₂ x₃)
              diamondOddChannelS
      simp only [diamondOddAxisSrcChannelEquiv_apply_S,
        Finset.sum_apply]
      rw [Finset.sum_comm]
  | some t =>
      change
        (∑ x₂,
          diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → PVec n k₃ → V) hn f
              (diamondOddChannelT t) x₂) x₃ =
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => ∑ x₂, f x₁ x₂ x₃)
              (diamondOddChannelT t)
      simp only [diamondOddAxisSrcChannelEquiv_apply_T,
        Finset.sum_apply, Pi.add_apply]
      rw [Finset.sum_add_distrib, Finset.sum_comm]

private theorem k4OddTriple_sum_last
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → PVec n k₃ → V)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₂ : DiamondOddAxisChannel n k₂) :
    diamondOddTripleSrcChannelEquiv V hn f
        q₁ q₂ diamondOddChannelS =
      diamondOddAxisSrcChannelEquiv V hn
        (fun x₂ =>
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => ∑ x₃, f x₁ x₂ x₃) q₁) q₂ := by
  change
    diamondOddAxisSrcChannelEquiv V hn
        (diamondOddAxisSrcChannelEquiv
          (PVec n k₃ → V) hn
          (diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → PVec n k₃ → V) hn f q₁) q₂)
        diamondOddChannelS =
      _
  rw [diamondOddAxisSrcChannelEquiv_apply_S]
  simp_rw [k4OddAxisSrcChannelEquiv_pi_apply]
  cases q₂ with
  | none =>
      change
        (∑ x₃, ∑ x₂,
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => f x₁ x₂ x₃) q₁) =
          ∑ x₂,
            diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => ∑ x₃, f x₁ x₂ x₃) q₁
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x₂ _
      cases q₁ with
      | none =>
          change
            (∑ x₃, ∑ x₁, f x₁ x₂ x₃) =
              ∑ x₁, ∑ x₃, f x₁ x₂ x₃
          rw [Finset.sum_comm]
      | some t =>
          change
            (∑ x₃,
              (f t.1 x₂ x₃ + ∑ x₁, f x₁ x₂ x₃)) =
              (∑ x₃, f t.1 x₂ x₃) +
                ∑ x₁, ∑ x₃, f x₁ x₂ x₃
          rw [Finset.sum_add_distrib, Finset.sum_comm]
  | some t =>
      change
        (∑ x₃,
          (diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => f x₁ t.1 x₃) q₁ +
            ∑ x₂,
              diamondOddAxisSrcChannelEquiv V hn
                (fun x₁ => f x₁ x₂ x₃) q₁)) =
          diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => ∑ x₃, f x₁ t.1 x₃) q₁ +
            ∑ x₂,
              diamondOddAxisSrcChannelEquiv V hn
                (fun x₁ => ∑ x₃, f x₁ x₂ x₃) q₁
      rw [Finset.sum_add_distrib]
      congr 1
      · cases q₁ with
        | none =>
            change
              (∑ x₃, ∑ x₁, f x₁ t.1 x₃) =
                ∑ x₁, ∑ x₃, f x₁ t.1 x₃
            rw [Finset.sum_comm]
        | some u =>
            change
              (∑ x₃,
                (f u.1 t.1 x₃ + ∑ x₁, f x₁ t.1 x₃)) =
                (∑ x₃, f u.1 t.1 x₃) +
                  ∑ x₁, ∑ x₃, f x₁ t.1 x₃
            rw [Finset.sum_add_distrib, Finset.sum_comm]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x₂ _
        cases q₁ with
        | none =>
            change
              (∑ x₃, ∑ x₁, f x₁ x₂ x₃) =
                ∑ x₁, ∑ x₃, f x₁ x₂ x₃
            rw [Finset.sum_comm]
        | some u =>
            change
              (∑ x₃,
                (f u.1 x₂ x₃ + ∑ x₁, f x₁ x₂ x₃)) =
                (∑ x₃, f u.1 x₂ x₃) +
                  ∑ x₁, ∑ x₃, f x₁ x₂ x₃
            rw [Finset.sum_add_distrib, Finset.sum_comm]

private theorem k4OddTwoSrc_sum_middle
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → PVec n k₃ → V)
    (c₁ : DiamondOddAxisChannel n k₁)
    (c₃ : DiamondOddAxisChannel n k₃) :
    k4OddTwoSrc V hn
        (fun x₁ x₃ => ∑ x₂, f x₁ x₂ x₃) c₁ c₃ =
      diamondOddTripleSrcChannelEquiv V hn f
        c₁ diamondOddChannelS c₃ := by
  unfold k4OddTwoSrc
  rw [k4OddTriple_sum_middle]
  apply congrArg
    (fun g : PVec n k₃ → V =>
      diamondOddAxisSrcChannelEquiv V hn g c₃)
  funext x₃
  exact k4OddAxisSrcChannelEquiv_pi_apply
    (PVec n k₃) V hn
      (fun x₁ x₃ => ∑ x₂, f x₁ x₂ x₃) c₁ x₃

private theorem k4OddTwoSrc_sum_last
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → PVec n k₃ → V)
    (c₁ : DiamondOddAxisChannel n k₁)
    (c₂ : DiamondOddAxisChannel n k₂) :
    k4OddTwoSrc V hn
        (fun x₁ x₂ => ∑ x₃, f x₁ x₂ x₃) c₁ c₂ =
      diamondOddTripleSrcChannelEquiv V hn f
        c₁ c₂ diamondOddChannelS := by
  rw [k4OddTriple_sum_last]
  unfold k4OddTwoSrc
  apply congrArg
    (fun g : PVec n k₂ → V =>
      diamondOddAxisSrcChannelEquiv V hn g c₂)
  funext x₂
  exact k4OddAxisSrcChannelEquiv_pi_apply
    (PVec n k₂) V hn
      (fun x₁ x₂ => ∑ x₃, f x₁ x₂ x₃) c₁ x₂

private noncomputable def k4OddPointedAddedQ
    {n a b c d : Nat} [NeZero n]
    (v : DiamondOddPointedAmbient n a b c d) : F :=
  k4CubeKappa
      (v.2.1 diamondOddChannelS diamondOddChannelS
        diamondOddChannelS)
      (v.2.2 diamondOddChannelS diamondOddChannelS
        diamondOddChannelS) +
    (∑ zt : DiamondOddAxisTail n c,
      k4CubeKappa
        (v.2.1 diamondOddChannelS (diamondOddChannelT zt)
          diamondOddChannelS)
        (diamondOddAxisTailJ (CyclicCube n)
          (fun zt' =>
            v.2.2 diamondOddChannelS diamondOddChannelS
              (diamondOddChannelT zt')) zt)) +
    (∑ pt : DiamondOddAxisTail n a,
      k4CubeKappa
        (v.2.1 (diamondOddChannelT pt) diamondOddChannelS
          diamondOddChannelS)
        (diamondOddAxisTailJ (CyclicCube n)
          (fun pt' =>
            v.2.2 (diamondOddChannelT pt') diamondOddChannelS
              diamondOddChannelS) pt)) +
    ∑ pt : DiamondOddAxisTail n a,
      ∑ zt : DiamondOddAxisTail n c,
        k4CubeKappa
          (v.2.1 (diamondOddChannelT pt)
            (diamondOddChannelT zt) diamondOddChannelS)
          (diamondOddTensorTailJ
            (zeroVec : PVec n a)
            (zeroVec : PVec n c)
            (fun pt' zt' =>
              v.2.2 (diamondOddChannelT pt')
                diamondOddChannelS (diamondOddChannelT zt'))
            pt zt)

private theorem k4BW_folded_eq_pointed
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (u : DiamondOddLiteralAmbient n a b c d) :
    (∑ p : PVec n a, ∑ zt : PVec n c,
      k4CubeKappa
        (∑ wt : PVec n d, u.2.1 p zt wt)
        (∑ yt : PVec n b, u.2.2 p yt zt)) =
      k4OddPointedAddedQ (diamondOddPointedAmbientEquiv hn u) := by
  change
    (∑ p : PVec n a, ∑ zt : PVec n c,
      k4CubeKappaBilin
        (∑ wt : PVec n d, u.2.1 p zt wt)
        (∑ yt : PVec n b, u.2.2 p yt zt)) = _
  rw [k4OddTwo_axis_pairing
    (CyclicCube n) hn k4CubeKappaBilin
    (fun p zt => ∑ wt, u.2.1 p zt wt)
    (fun p zt => ∑ yt, u.2.2 p yt zt)]
  simp only [k4CubeKappaBilin_apply]
  have hB
      (cp : DiamondOddAxisChannel n a)
      (cz : DiamondOddAxisChannel n c) :
      k4OddTwoSrc (CyclicCube n) hn
          (fun p zt => ∑ wt, u.2.1 p zt wt) cp cz =
        diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.1
          cp cz diamondOddChannelS :=
    k4OddTwoSrc_sum_last (CyclicCube n) hn u.2.1 cp cz
  have hW
      (cp : DiamondOddAxisChannel n a)
      (cz : DiamondOddAxisChannel n c) :
      k4OddTwoSrc (CyclicCube n) hn
          (fun p zt => ∑ yt, u.2.2 p yt zt) cp cz =
        diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.2
          cp diamondOddChannelS cz :=
    k4OddTwoSrc_sum_middle (CyclicCube n) hn u.2.2 cp cz
  simp_rw [hB, hW]
  rw [diamondOddPointedAmbientEquiv_apply]
  rfl

private theorem k4OddPointedAddedQ_eq_channel
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n)
    (x : DiamondOddPointedSource n a b c d hn) :
    k4OddPointedAddedQ x.1 =
      k4OddChannelAddedQ (diamondOddChannelProductEquiv hn x) := by
  unfold k4OddPointedAddedQ k4OddChannelAddedQ
  simp only [diamondOddChannelProductEquiv_apply_SSSS,
    diamondOddChannelProductEquiv_apply_SSTS,
    diamondOddChannelProductEquiv_apply_TSSS,
    diamondOddChannelProductEquiv_apply_TSTS]

private theorem k4BWPhaseClean_eq_pointed
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n)
    (A : AFun4 n b c d)
    (B : BFun4 n a c d)
    (W : WFun4 n a b c) :
    k4BWPhaseClean B W =
      k4OddPointedAddedQ
        (diamondOddPointedAmbientEquiv hn
          (diamondOddABWGaugeEquiv hb hc hd (A, B, W))) := by
  rw [k4BWPhaseClean_eq_gauged hb hc hd,
    k4BW_gauged_eq_folded B W hb hc hd]
  simpa only [diamondOddABWGaugeEquiv_apply] using
    k4BW_folded_eq_pointed hn
      (diamondOddABWGaugeEquiv hb hc hd (A, B, W))

theorem k4BWPhaseClean_eq_oddChannelAddedQ
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n)
    (x : K4PreCSource n a b c d) :
    k4BWPhaseClean x.1.2.1 x.1.2.2 =
      k4OddChannelAddedQ
        (diamondOddChannelProductEquiv hn
          (diamondOddPreCPointedSourceEquiv hb hc hd hn
            (k4PreCSourceEquivDiamond x))) := by
  let y := k4PreCSourceEquivDiamond x
  calc
    k4BWPhaseClean x.1.2.1 x.1.2.2 =
        k4OddPointedAddedQ
          (diamondOddPointedAmbientEquiv hn
            (diamondOddABWGaugeEquiv hb hc hd y.1)) := by
      simpa only [y, k4PreCSourceEquivDiamond_apply_A,
        k4PreCSourceEquivDiamond_apply_B,
        k4PreCSourceEquivDiamond_apply_W] using
        k4BWPhaseClean_eq_pointed hb hc hd hn
          x.1.1 x.1.2.1 x.1.2.2
    _ = k4OddPointedAddedQ
          (diamondOddPreCPointedSourceEquiv hb hc hd hn y).1 := by
      rw [diamondOddPreCPointedSourceEquiv_apply,
        diamondOddLiteralPointedSourceEquiv_apply,
        diamondOddLiteralSourceEquiv_apply]
    _ = _ :=
      k4OddPointedAddedQ_eq_channel hn
        (diamondOddPreCPointedSourceEquiv hb hc hd hn y)

end

end Core4loop.CompleteGraph.Odd
