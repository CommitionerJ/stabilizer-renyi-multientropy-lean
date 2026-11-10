import Core4loop.CompleteGraph.Odd.Residual.Coordinates
import Core4loop.CompleteGraph.Odd.ScalarQZero
import Core4loop.CompleteGraph.Odd.ConstrainedCurl
import Core4loop.CompleteGraph.Odd.LeftKernelQZero
import Core4loop.CompleteGraph.Odd.FreeCross
import Core4loop.SquareDiagonal.DirectWitt.OddResidual

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.Odd

open Core4loop
open Core4loop.CompleteGraph.CubeCompat
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.DirectWitt

noncomputable section

attribute [local instance] Fintype.ofFinite

@[reducible] private noncomputable def k4OddResidualRowFintype
    {n a b c d : Nat} [NeZero n] (r : DiamondOddChannelRow) :
    Fintype ↥(DiamondOddChannelRowSpace n a b c d r) := by
  cases r <;> simp only [DiamondOddChannelRowSpace] <;>
    infer_instance

/-! ## SSSS: transport to the actual complete-graph singleton source -/

private instance k4OddSSSSAxisTailIsEmpty
    {n : Nat} [NeZero n] :
    IsEmpty (DiamondOddAxisTail n 1) where
  false t := t.2 (by
    funext i
    exact Fin.elim0 i)

private noncomputable def k4OddSSSSRows
    {n : Nat} [NeZero n]
    (x : DiamondOddScalarSource n) :
    DiamondOddChannelProduct n 1 1 1 1 := by
  intro r
  cases r with
  | ssss => exact x
  | ssst => exact 0
  | ssts => exact 0
  | sstt => exact 0
  | stss => exact 0
  | stst => exact 0
  | stts => exact 0
  | sttt => exact 0
  | tsss => exact 0
  | tsst => exact 0
  | tsts => exact 0
  | tstt => exact 0
  | ttss => exact 0
  | ttst => exact 0
  | ttts => exact 0
  | tttt => exact 0

private noncomputable def k4OddSSSSSource
    {n : Nat} [NeZero n]
    (hn : Odd n) (x : DiamondOddScalarSource n) :
    K4PreCSource n 1 1 1 1 :=
  (k4PreCSourceEquivDiamond (n := n) (a := 1) (b := 1)
      (c := 1) (d := 1)).symm
    ((diamondOddPreCPointedSourceEquiv Nat.zero_lt_one Nat.zero_lt_one
        Nat.zero_lt_one hn).symm
      ((diamondOddChannelProductEquiv hn).symm (k4OddSSSSRows x)))

private theorem k4OddSSSS_preC_phase
    {n : Nat} [NeZero n]
    (hn : Odd n) (x : DiamondOddScalarSource n) :
    k4PreCQ (k4OddSSSSSource hn x) =
      diamondOddScalarQ x +
        k4CubeKappa x.1.2.1 x.1.2.2 := by
  rw [k4PreCQ_transport]
  rw [diamondPreCQ_eq_oddPointedQ Nat.zero_lt_one Nat.zero_lt_one
    Nat.zero_lt_one hn]
  rw [diamondOddPointedQ_eq_channelReducedQ]
  rw [k4BWPhaseClean_eq_oddChannelAddedQ Nat.zero_lt_one Nat.zero_lt_one
    Nat.zero_lt_one hn]
  simp only [k4OddSSSSSource, LinearEquiv.apply_symm_apply]
  simp [diamondOddChannelReducedQ, k4OddChannelAddedQ,
    k4OddSSSSRows, diamondOddChannelPhaseSSSS,
    diamondOddChannelPhaseSSTS, diamondOddChannelPhaseSSTT,
    diamondOddChannelPhaseSTTS]

private theorem k4OddSSSSQ_zero
    {n : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Odd n)
    (x : DiamondOddScalarSource n) :
    diamondOddScalarQ x +
        k4CubeKappa x.1.2.1 x.1.2.2 = 0 := by
  rw [← k4OddSSSS_preC_phase hn x]
  exact
    CompleteGraph.ScalarCycle.k4ScalarQ_zero hn2
      (k4OddSSSSSource hn x)

/-! ## Four K4 row evaluators -/

private noncomputable def k4OddSSTSAddedQ
    {n c : Nat} [NeZero n]
    (u : DiamondOddAxisTail n c → DiamondEOOOLeftAmbient n) : F :=
  ∑ t : DiamondOddAxisTail n c,
    k4CubeKappa (u t).1
      (diamondOddAxisTailJ (CyclicCube n) (fun s => (u s).2) t)

private theorem sum_bitSign_zero_eq_pow_finrank
    {V : Type*}
    [AddCommGroup V] [Module F V] [Fintype V] :
    (∑ _x : V, bitSign 0) =
      (2 : Int) ^ Module.finrank F V := by
  simp only [bitSign_zero, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact_mod_cast (Module.card_eq_pow_finrank (K := F) (V := V))

private theorem sum_bitSign_k4OddSSSSRow_eq_pow
    {n : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Odd n) :
    (∑ x : DiamondOddScalarSource n,
      bitSign
        (diamondOddScalarQ x +
          k4CubeKappa x.1.2.1 x.1.2.2)) =
      (2 : Int) ^ Module.finrank F (DiamondOddScalarSource n) := by
  simp_rw [k4OddSSSSQ_zero hn2 hn]
  exact sum_bitSign_zero_eq_pow_finrank

private theorem sum_bitSign_bilinear_add_left_eq_pow_of_zero_on_ker
    {U V : Type*}
    [AddCommGroup U] [Module F U] [Fintype U]
    [AddCommGroup V] [Module F V] [Fintype V]
    (L : U →ₗ[F] Module.Dual F V)
    (g : U → F)
    (hg : ∀ u, u ∈ LinearMap.ker L → g u = 0) :
    (∑ z : U × V, bitSign (L z.1 z.2 + g z.1)) =
      (2 : Int) ^
        (Module.finrank F (LinearMap.ker L) +
          Module.finrank F V) := by
  calc
    (∑ z : U × V, bitSign (L z.1 z.2 + g z.1)) =
        ∑ z : U × V, bitSign (L z.1 z.2) := by
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro u _
      change
        (∑ y : V, bitSign (L u y + g u)) =
          ∑ y : V, bitSign (L u y)
      rw [sum_bitSign_linearMap_add_const, sum_bitSign_linearMap]
      by_cases hu : L u = 0
      · have hgu : g u = 0 := hg u (LinearMap.mem_ker.mpr hu)
        simp only [hu, if_pos, hgu, bitSign_zero, mul_one]
      · simp [hu]
    _ = (2 : Int) ^
          (Module.finrank F (LinearMap.ker L) +
            Module.finrank F V) :=
      sum_bitSign_bilinear_eq_pow L

private theorem sum_bitSign_k4OddSSTSRow_eq_pow
    {n c : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Odd n) :
    (∑ x : DiamondOddAxisTail n c → DiamondOddScalarAmbient n,
      bitSign
        (diamondOddSSTSCross hn
            (diamondOddSSTSRowEquiv x).1
            (diamondOddSSTSRowEquiv x).2 +
          k4OddSSTSAddedQ (diamondOddSSTSRowEquiv x).1)) =
      (2 : Int) ^
        (Module.finrank F
            (LinearMap.ker (diamondOddSSTSCross (c := c) hn)) +
          Module.finrank F
            (DiamondOddAxisTail n c → CyclicCube n)) := by
  calc
    _ = ∑ z :
          (DiamondOddAxisTail n c → DiamondEOOOLeftAmbient n) ×
            (DiamondOddAxisTail n c → CyclicCube n),
        bitSign
          (diamondOddSSTSCross hn z.1 z.2 +
            k4OddSSTSAddedQ z.1) := by
      exact Fintype.sum_equiv
        (diamondOddSSTSRowEquiv (n := n) (c := c)).toEquiv
        _ _ (fun _ => rfl)
    _ = _ := by
      apply sum_bitSign_bilinear_add_left_eq_pow_of_zero_on_ker
      intro u hu
      exact k4OddSSTS_addedPhase_zero_on_crossKernel hn2 hn u hu

private theorem k4OddTSSSRowQ_zero
    {n a : Nat} [NeZero n]
    (hn2 : 2 <= n)
    (x : DiamondOddTSSSSource n a) :
    (∑ pt : DiamondOddAxisTail n a,
      k4CubeKappa (x.1 pt).1
        (diamondOddAxisTailJ (CyclicCube n)
          (fun pt' => (x.1 pt').2) pt)) = 0 :=
  k4OddTSSS_addedPhase_zero hn2 x

private theorem sum_bitSign_k4OddTSSSRow_eq_pow
    {n a : Nat} [NeZero n]
    (hn2 : 2 <= n) :
    (∑ x : DiamondOddTSSSSource n a,
      bitSign
        (∑ pt : DiamondOddAxisTail n a,
          k4CubeKappa (x.1 pt).1
            (diamondOddAxisTailJ (CyclicCube n)
              (fun pt' => (x.1 pt').2) pt))) =
      (2 : Int) ^ Module.finrank F (DiamondOddTSSSSource n a) := by
  simp_rw [k4OddTSSSRowQ_zero hn2]
  exact sum_bitSign_zero_eq_pow_finrank

private noncomputable def k4OddTSTSRowEquiv
    {n a c : Nat} [NeZero n] :
    (DiamondOddAxisTail n a →
        DiamondOddAxisTail n c → (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      (K4OddTSTSFamily n a c × K4OddTSTSFamily n a c) where
  toFun x := (fun pt zt => (x pt zt).1, fun pt zt => (x pt zt).2)
  invFun x := fun pt zt => (x.1 pt zt, x.2 pt zt)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sum_bitSign_k4OddTSTSRow_eq_pow
    {n a c : Nat} [NeZero n] (hn : Odd n) :
    (∑ x : DiamondOddAxisTail n a →
          DiamondOddAxisTail n c → (CyclicCube n × CyclicCube n),
      bitSign
        (∑ pt : DiamondOddAxisTail n a,
          ∑ zt : DiamondOddAxisTail n c,
            k4CubeKappa (x pt zt).1
              (diamondOddTensorTailJ
                (zeroVec : PVec n a)
                (zeroVec : PVec n c)
                (fun pt' zt' => (x pt' zt').2) pt zt))) =
      (2 : Int) ^
        ((n ^ (a - 1) - 1) *
          (n ^ (c - 1) - 1) *
            (n ^ 3 + n ^ 2)) := by
  calc
    _ = ∑ z : K4OddTSTSFamily n a c × K4OddTSTSFamily n a c,
        bitSign
          (∑ pt : DiamondOddAxisTail n a,
            ∑ zt : DiamondOddAxisTail n c,
              k4CubeKappa (z.1 pt zt)
                (diamondOddTensorTailJ
                  (zeroVec : PVec n a)
                  (zeroVec : PVec n c)
                  z.2 pt zt)) := by
      exact Fintype.sum_equiv
        (k4OddTSTSRowEquiv (n := n) (a := a) (c := c)).toEquiv
        _ _ (fun _ => rfl)
    _ = _ := sum_bitSign_k4OddTSTS_eq_pow hn

/-! ## Literal K4 row phase, exponent, and half-rank -/

def k4OddHalfRankNat (n a b c d : Nat) : Nat :=
  (n ^ (c - 1) - 1) * (n * (n - 1) * (n + 1)) +
    (n ^ (c - 1) - 1) * (n ^ (d - 1) - 1) *
      (n ^ 2 * (n - 1)) +
    (n ^ (b - 1) - 1) * (n ^ (c - 1) - 1) *
      (n ^ 2 * (n - 1)) +
    (n ^ (a - 1) - 1) * (n ^ (c - 1) - 1) *
      (n ^ 2 * (n - 1))

private noncomputable def k4OddChannelRowQ
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    (r : DiamondOddChannelRow) →
      ↥(DiamondOddChannelRowSpace n a b c d r) → F := by
  intro r
  cases r with
  | ssss =>
      exact fun x =>
        diamondOddScalarQ x +
          k4CubeKappa x.1.2.1 x.1.2.2
  | ssst => exact diamondOddChannelRowQ hn .ssst
  | ssts =>
      exact fun x =>
        diamondOddSSTSCross hn
            (diamondOddSSTSRowEquiv x).1
            (diamondOddSSTSRowEquiv x).2 +
          k4OddSSTSAddedQ (diamondOddSSTSRowEquiv x).1
  | sstt => exact diamondOddChannelRowQ hn .sstt
  | stss => exact diamondOddChannelRowQ hn .stss
  | stst => exact diamondOddChannelRowQ hn .stst
  | stts => exact diamondOddChannelRowQ hn .stts
  | sttt => exact diamondOddChannelRowQ hn .sttt
  | tsss =>
      exact fun x =>
        ∑ pt : DiamondOddAxisTail n a,
          k4CubeKappa (x.1 pt).1
            (diamondOddAxisTailJ (CyclicCube n)
              (fun pt' => (x.1 pt').2) pt)
  | tsst => exact diamondOddChannelRowQ hn .tsst
  | tsts =>
      exact fun x =>
        ∑ pt : DiamondOddAxisTail n a,
          ∑ zt : DiamondOddAxisTail n c,
            k4CubeKappa (x pt zt).1
              (diamondOddTensorTailJ
                (zeroVec : PVec n a)
                (zeroVec : PVec n c)
                (fun pt' zt' => (x pt' zt').2) pt zt)
  | tstt => exact diamondOddChannelRowQ hn .tstt
  | ttss => exact diamondOddChannelRowQ hn .ttss
  | ttst => exact diamondOddChannelRowQ hn .ttst
  | ttts => exact diamondOddChannelRowQ hn .ttts
  | tttt => exact diamondOddChannelRowQ hn .tttt

private noncomputable def k4OddChannelRowHalfRank
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddChannelRow → Nat
  | .ssss => 0
  | .tsts =>
      (n ^ (a - 1) - 1) * (n ^ (c - 1) - 1) *
        (n ^ 2 * (n - 1))
  | r =>
      diamondOddChannelRowHalfRank
        (b := b) (c := c) (d := d) hn r

private noncomputable def k4OddChannelRowExponent
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddChannelRow → Nat
  | .ssss => Module.finrank F (DiamondOddScalarSource n)
  | .tsts =>
      (n ^ (a - 1) - 1) * (n ^ (c - 1) - 1) *
        (n ^ 3 + n ^ 2)
  | .sstt =>
      (n ^ (c - 1) - 1) * (n ^ (d - 1) - 1) *
        (n ^ 3 + n ^ 2)
  | .stts =>
      (n ^ (b - 1) - 1) * (n ^ (c - 1) - 1) *
        (n ^ 3 + n ^ 2)
  | r =>
      diamondOddChannelRowExponent
        (a := a) (b := b) (c := c) (d := d) hn r

noncomputable def k4OddResidualExponent
    {n a b c d : Nat} [NeZero n] (hn : Odd n) : Nat :=
  ∑ r : DiamondOddChannelRow,
    k4OddChannelRowExponent
      (a := a) (b := b) (c := c) (d := d) hn r

private theorem k4OddChannelRow_univ :
    (Finset.univ : Finset DiamondOddChannelRow) =
      {.ssss, .ssst, .ssts, .sstt,
       .stss, .stst, .stts, .sttt,
       .tsss, .tsst, .tsts, .tstt,
       .ttss, .ttst, .ttts, .tttt} := by
  ext r
  cases r <;> simp

private theorem k4OddChannelPhase_eq_sum_rowQ
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (rows : DiamondOddChannelProduct n a b c d) :
    diamondOddChannelReducedQ rows + k4OddChannelAddedQ rows =
      ∑ r : DiamondOddChannelRow,
        k4OddChannelRowQ hn r (rows r) := by
  rw [diamondOddChannelReducedQ_eq_sum_rowQ hn rows]
  rw [k4OddChannelRow_univ]
  simp [diamondOddChannelRowQ, k4OddChannelRowQ,
    k4OddChannelAddedQ, k4OddSSTSAddedQ,
    diamondOddSSTSRowEquiv]
  abel

/-! ## Row evaluation and exact row dimensions -/

attribute [local instance] k4OddResidualRowFintype

private theorem finrank_k4OddCyclicCube
    {n : Nat} [NeZero n] :
    Module.finrank F (CyclicCube n) = n ^ 3 := by
  simp [CyclicCube, Module.finrank_pi_fintype, I, ZMod.card,
    pow_succ, mul_assoc]

private theorem finrank_k4OddAxisTailPi
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] :
    Module.finrank F (DiamondOddAxisTail n k → V) =
      (n ^ (k - 1) - 1) * Module.finrank F V := by
  rw [Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  congr 1
  have htailNatCard :
      Nat.card
          (PointedTail (PVec n k) (zeroVec : PVec n k)) =
        Nat.card (PVec n k) - 1 := by
    simpa only [← Nat.card_eq_fintype_card] using
      (card_pointedTail (zeroVec : PVec n k))
  calc
    Fintype.card (DiamondOddAxisTail n k) =
        Nat.card (DiamondOddAxisTail n k) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (PVec n k) - 1 := by
      simpa only [DiamondOddAxisTail] using htailNatCard
    _ = Fintype.card (PVec n k) - 1 := by
      rw [Nat.card_eq_fintype_card]
    _ = n ^ (k - 1) - 1 := by
      rw [card_vec]

private theorem finrank_k4OddTensorTailPi
    {n k l : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] :
    Module.finrank F
        (DiamondOddAxisTail n k → DiamondOddAxisTail n l → V) =
      (n ^ (k - 1) - 1) * (n ^ (l - 1) - 1) *
        Module.finrank F V := by
  rw [finrank_k4OddAxisTailPi, finrank_k4OddAxisTailPi]
  ring

private theorem finrank_k4OddTSTSRow
    {n a c : Nat} [NeZero n] :
    Module.finrank F
        (DiamondOddAxisTail n a →
          DiamondOddAxisTail n c → (CyclicCube n × CyclicCube n)) =
      2 * ((n ^ (a - 1) - 1) * (n ^ (c - 1) - 1) * n ^ 3) := by
  rw [finrank_k4OddTensorTailPi, Module.finrank_prod,
    finrank_k4OddCyclicCube]
  ring

private theorem k4OddResidual_sum_cross_eq_closed_pow
    {U V : Type*}
    [AddCommGroup U] [Module F U] [Fintype U]
    [AddCommGroup V] [Module F V] [Fintype V]
    (L : U →ₗ[F] Module.Dual F V)
    (e : Nat)
    (htotal :
      Module.finrank F (LinearMap.range L) + e =
        Module.finrank F U + Module.finrank F V) :
    (∑ z : U × V, bitSign (L z.1 z.2)) = (2 : Int) ^ e := by
  calc
    _ = (2 : Int) ^
          (Module.finrank F (LinearMap.ker L) +
            Module.finrank F V) :=
      sum_bitSign_bilinear_eq_pow L
    _ = _ := by
      congr 1
      have hrank := LinearMap.finrank_range_add_finrank_ker L
      omega

private theorem sum_bitSign_k4OddSSTTRow_eq_pow
    {n c d : Nat} [NeZero n] (hn : Odd n) :
    (∑ x : DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → (CyclicCube n × CyclicCube n),
      bitSign
        (diamondOddSSTTCross hn
          (diamondOddSSTTRowEquiv x).1
          (diamondOddSSTTRowEquiv x).2)) =
      (2 : Int) ^
        ((n ^ (c - 1) - 1) * (n ^ (d - 1) - 1) *
          (n ^ 3 + n ^ 2)) := by
  calc
    _ = ∑ z :
          (DiamondOddAxisTail n c →
            DiamondOddAxisTail n d → CyclicCube n) ×
          (DiamondOddAxisTail n c →
            DiamondOddAxisTail n d → CyclicCube n),
        bitSign (diamondOddSSTTCross hn z.1 z.2) := by
      exact Fintype.sum_equiv
        (diamondOddSSTTRowEquiv (n := n) (c := c) (d := d)).toEquiv
        _ _ (fun _ => rfl)
    _ = _ := by
      apply k4OddResidual_sum_cross_eq_closed_pow
      rw [rank_diamondOddSSTTCross,
        finrank_k4OddTensorTailPi, finrank_k4OddCyclicCube]
      obtain ⟨m, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      simp only [Nat.succ_eq_add_one, Nat.succ_sub_one]
      ring

private theorem sum_bitSign_k4OddSTTSRow_eq_pow
    {n b c : Nat} [NeZero n] (hn : Odd n) :
    (∑ x : DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → (CyclicCube n × CyclicCube n),
      bitSign
        (diamondOddSTTSCross hn
          (diamondOddSTTSRowEquiv x).1
          (diamondOddSTTSRowEquiv x).2)) =
      (2 : Int) ^
        ((n ^ (b - 1) - 1) * (n ^ (c - 1) - 1) *
          (n ^ 3 + n ^ 2)) := by
  calc
    _ = ∑ z :
          (DiamondOddAxisTail n b →
            DiamondOddAxisTail n c → CyclicCube n) ×
          (DiamondOddAxisTail n b →
            DiamondOddAxisTail n c → CyclicCube n),
        bitSign (diamondOddSTTSCross hn z.1 z.2) := by
      exact Fintype.sum_equiv
        (diamondOddSTTSRowEquiv (n := n) (b := b) (c := c)).toEquiv
        _ _ (fun _ => rfl)
    _ = _ := by
      apply k4OddResidual_sum_cross_eq_closed_pow
      rw [rank_diamondOddSTTSCross,
        finrank_k4OddTensorTailPi, finrank_k4OddCyclicCube]
      obtain ⟨m, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      simp only [Nat.succ_eq_add_one, Nat.succ_sub_one]
      ring

set_option maxHeartbeats 1000000 in
-- Explicitly normalizing all sixteen dependent row spaces needs a larger budget.
private theorem k4OddChannelRow_sum_eq_pow
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Odd n)
    (r : DiamondOddChannelRow) :
    (∑ x : ↥(DiamondOddChannelRowSpace n a b c d r),
        bitSign (k4OddChannelRowQ hn r x)) =
      (2 : Int) ^
        k4OddChannelRowExponent
          (a := a) (b := b) (c := c) (d := d) hn r := by
  cases r <;>
    simp only [DiamondOddChannelRowSpace, k4OddChannelRowQ,
      k4OddChannelRowExponent]
  case ssss => exact sum_bitSign_k4OddSSSSRow_eq_pow hn2 hn
  case ssst => exact sum_bitSign_zero_eq_pow_finrank
  case ssts => exact sum_bitSign_k4OddSSTSRow_eq_pow hn2 hn
  case sstt => exact sum_bitSign_k4OddSSTTRow_eq_pow hn
  case stss => exact sum_bitSign_zero_eq_pow_finrank
  case stst => exact sum_bitSign_zero_eq_pow_finrank
  case stts => exact sum_bitSign_k4OddSTTSRow_eq_pow hn
  case sttt => exact sum_bitSign_zero_eq_pow_finrank
  case tsss => exact sum_bitSign_k4OddTSSSRow_eq_pow hn2
  case tsst => exact sum_bitSign_zero_eq_pow_finrank
  case tsts => exact sum_bitSign_k4OddTSTSRow_eq_pow hn
  case tstt => exact sum_bitSign_zero_eq_pow_finrank
  case ttss => exact sum_bitSign_zero_eq_pow_finrank
  case ttst => exact sum_bitSign_zero_eq_pow_finrank
  case ttts => exact sum_bitSign_zero_eq_pow_finrank
  case tttt => exact sum_bitSign_zero_eq_pow_finrank

private theorem k4OddChannelRowExponent_add_halfRank
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (r : DiamondOddChannelRow) :
    k4OddChannelRowExponent
          (a := a) (b := b) (c := c) (d := d) hn r +
        k4OddChannelRowHalfRank
          (a := a) (b := b) (c := c) (d := d) hn r =
      Module.finrank F
        ↥(DiamondOddChannelRowSpace n a b c d r) := by
  cases r <;>
    simp only [DiamondOddChannelRowSpace,
      k4OddChannelRowExponent, k4OddChannelRowHalfRank]
  case ssss => rfl
  case tsts =>
    apply Eq.trans _ finrank_k4OddTSTSRow.symm
    obtain ⟨m, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    simp only [Nat.succ_eq_add_one, Nat.succ_sub_one]
    ring
  case sstt =>
    change
      (n ^ (c - 1) - 1) * (n ^ (d - 1) - 1) *
            (n ^ 3 + n ^ 2) +
          Module.finrank F
            (LinearMap.range
              (diamondOddSSTTCross (c := c) (d := d) hn)) = _
    rw [rank_diamondOddSSTTCross]
    apply Eq.trans _ finrank_k4OddTSTSRow.symm
    obtain ⟨m, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    simp only [Nat.succ_eq_add_one, Nat.succ_sub_one]
    ring
  case stts =>
    change
      (n ^ (b - 1) - 1) * (n ^ (c - 1) - 1) *
            (n ^ 3 + n ^ 2) +
          Module.finrank F
            (LinearMap.range
              (diamondOddSTTSCross (b := b) (c := c) hn)) = _
    rw [rank_diamondOddSTTSCross]
    apply Eq.trans _ finrank_k4OddTSTSRow.symm
    obtain ⟨m, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    simp only [Nat.succ_eq_add_one, Nat.succ_sub_one]
    ring
  case ssst => rfl
  case ssts => exact diamondOddChannelRowExponent_add_halfRank hn .ssts
  case stss => rfl
  case stst => rfl
  case sttt => rfl
  case tsss => rfl
  case tsst => rfl
  case tstt => rfl
  case ttss => rfl
  case ttst => rfl
  case ttts => rfl
  case tttt => rfl

private theorem k4OddHalfRankNat_eq_sum_rowHalfRank
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    k4OddHalfRankNat n a b c d =
      ∑ r : DiamondOddChannelRow,
        k4OddChannelRowHalfRank
          (a := a) (b := b) (c := c) (d := d) hn r := by
  rw [k4OddChannelRow_univ]
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton,
    or_self, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton]
  simp only [k4OddChannelRowHalfRank,
    diamondOddChannelRowHalfRank, add_zero, zero_add]
  rw [rank_diamondOddSSTSCross,
    rank_diamondOddSSTTCross, rank_diamondOddSTTSCross]
  unfold k4OddHalfRankNat
  ring

/-! ## Dependent-product factorization -/

private theorem k4OddResidual_bitSign_sum_eq_prod
    {iota : Type*} [Fintype iota] (q : iota → F) :
    bitSign (∑ i, q i) = ∏ i, bitSign (q i) := by
  classical
  induction (Finset.univ : Finset iota) using Finset.induction_on with
  | empty => simp [bitSign_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, bitSign_add, ih]

private theorem k4OddResidual_sum_pi_bitSign_eq_prod
    {iota : Type*} [Fintype iota]
    {X : iota → Type*} [∀ i, Fintype (X i)]
    (q : ∀ i, X i → F) :
    (∑ x : ∀ i, X i, bitSign (∑ i, q i (x i))) =
      ∏ i, ∑ y : X i, bitSign (q i y) := by
  classical
  simp_rw [k4OddResidual_bitSign_sum_eq_prod]
  convert (Fintype.prod_sum (fun i y => bitSign (q i y))).symm using 1
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _
    rfl

private theorem k4OddResidual_actual_factorization
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) :
    (∑ rows : DiamondOddChannelProduct n a b c d,
        bitSign
          (∑ r : DiamondOddChannelRow,
            k4OddChannelRowQ hn r (rows r))) =
      ∏ r : DiamondOddChannelRow,
        ∑ x : ↥(DiamondOddChannelRowSpace n a b c d r),
          bitSign (k4OddChannelRowQ hn r x) := by
  convert
    k4OddResidual_sum_pi_bitSign_eq_prod
      (X := fun r => ↥(DiamondOddChannelRowSpace n a b c d r))
      (k4OddChannelRowQ hn) using 1
  apply Finset.sum_congr
  · ext rows
    simp
  · intro rows _
    rfl

private theorem k4OddResidual_prod_pow_eq_pow_sum
    {iota : Type*} [Fintype iota] (e : iota → Nat) :
    ∏ i, (2 : Int) ^ e i = (2 : Int) ^ ∑ i, e i := by
  classical
  induction (Finset.univ : Finset iota) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, pow_add]

/-! ## Literal K4 source transport -/

private noncomputable local instance k4OddResidualPreCSourceFintype
    {n a b c d : Nat} [NeZero n] :
    Fintype (K4PreCSource n a b c d) :=
  Fintype.ofFinite _

private noncomputable def k4OddPreCChannelEquiv
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    K4PreCSource n a b c d ≃ₗ[F]
      DiamondOddChannelProduct n a b c d :=
  k4PreCSourceEquivDiamond |>.trans
    ((diamondOddPreCPointedSourceEquiv hb hc hd hn).trans
      (diamondOddChannelProductEquiv hn))

private theorem k4PreCQ_eq_sum_oddChannelRowQ
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) (x : K4PreCSource n a b c d) :
    k4PreCQ x =
      ∑ r : DiamondOddChannelRow,
        k4OddChannelRowQ hn r (k4OddPreCChannelEquiv hb hc hd hn x r) := by
  rw [k4PreCQ_transport]
  rw [diamondPreCQ_eq_oddPointedQ hb hc hd hn]
  rw [diamondOddPointedQ_eq_channelReducedQ]
  rw [k4BWPhaseClean_eq_oddChannelAddedQ hb hc hd hn]
  exact k4OddChannelPhase_eq_sum_rowQ hn _

private theorem k4OddResidual_source_sum_transport
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    (∑ x : K4PreCSource n a b c d, bitSign (k4PreCQ x)) =
      ∑ rows : DiamondOddChannelProduct n a b c d,
        bitSign
          (∑ r : DiamondOddChannelRow,
            k4OddChannelRowQ hn r (rows r)) := by
  exact Fintype.sum_equiv
    (k4OddPreCChannelEquiv hb hc hd hn).toEquiv
    (fun x : K4PreCSource n a b c d => bitSign (k4PreCQ x))
    (fun rows : DiamondOddChannelProduct n a b c d =>
      bitSign (∑ r, k4OddChannelRowQ hn r (rows r)))
    (fun x => by
      change
        bitSign (k4PreCQ x) =
          bitSign
            (∑ r, k4OddChannelRowQ hn r
              (k4OddPreCChannelEquiv hb hc hd hn x r))
      rw [k4PreCQ_eq_sum_oddChannelRowQ hb hc hd hn x])

theorem sum_bitSign_k4PreCQ_eq_pow_odd_all_large
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Odd n)
    (_ha2 : 2 <= a) (hb2 : 2 <= b)
    (hc2 : 2 <= c) (hd2 : 2 <= d) :
    (∑ x : K4PreCSource n a b c d, bitSign (k4PreCQ x)) =
      (2 : Int) ^
        k4OddResidualExponent
          (a := a) (b := b) (c := c) (d := d) hn := by
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  have hd : 0 < d := by omega
  rw [k4OddResidual_source_sum_transport hb hc hd hn]
  rw [k4OddResidual_actual_factorization hn]
  simp_rw [k4OddChannelRow_sum_eq_pow hn2 hn]
  rw [k4OddResidual_prod_pow_eq_pow_sum]
  rfl

private theorem
    k4OddResidual_sum_exponent_add_sum_halfRank_eq_source_finrank
    {iota S : Type*} [Fintype iota]
    [AddCommGroup S] [Module F S]
    (X : iota → ModuleCat F)
    [∀ i, FiniteDimensional F (X i : Type)]
    (rowExponent rowHalfRank : iota → Nat)
    (hrow : ∀ i,
      rowExponent i + rowHalfRank i =
        Module.finrank F (X i : Type))
    (e : S ≃ₗ[F] ((i : iota) → (X i : Type))) :
    (∑ i, rowExponent i) + (∑ i, rowHalfRank i) =
      Module.finrank F S := by
  rw [LinearEquiv.finrank_eq e]
  rw [Module.finrank_pi_fintype, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]

theorem k4OddResidualExponent_add_halfRank_eq_source
    {n a b c d : Nat} [NeZero n]
    (_hn2 : 2 <= n) (hn : Odd n)
    (_ha2 : 2 <= a) (hb2 : 2 <= b)
    (hc2 : 2 <= c) (hd2 : 2 <= d) :
    k4OddResidualExponent
          (a := a) (b := b) (c := c) (d := d) hn +
        k4OddHalfRankNat n a b c d =
      Module.finrank F (K4PreCSource n a b c d) := by
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  have hd : 0 < d := by omega
  unfold k4OddResidualExponent
  rw [k4OddHalfRankNat_eq_sum_rowHalfRank hn]
  exact
    k4OddResidual_sum_exponent_add_sum_halfRank_eq_source_finrank
      (X := DiamondOddChannelRowSpace n a b c d)
      (k4OddChannelRowExponent
        (a := a) (b := b) (c := c) (d := d) hn)
      (k4OddChannelRowHalfRank
        (a := a) (b := b) (c := c) (d := d) hn)
      (k4OddChannelRowExponent_add_halfRank hn)
      (k4OddPreCChannelEquiv hb hc hd hn)

end

end Core4loop.CompleteGraph.Odd
