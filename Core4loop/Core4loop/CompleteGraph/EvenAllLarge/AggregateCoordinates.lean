import Core4loop.CompleteGraph.EvenAllLarge.BaseQZero
import Core4loop.SquareDiagonal.EvenP.TotalEEEE.LeftSource

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.DirectWitt
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.CubeCompat

noncomputable section

attribute [local instance] Fintype.ofFinite

/-! ## Public linear forms of the literal local operators -/

noncomputable abbrev k4AggregatePDiff
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n :=
  cubeDiffP

noncomputable abbrev k4AggregateRDiff
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n :=
  cubeDiffR

@[simp] theorem k4AggregatePDiff_apply
    {n : Nat} [NeZero n] (B : CyclicCube n) (i j k : I n) :
    k4AggregatePDiff B i j k =
      B i j k + B (i + 1) (j - 1) k := by
  change B i j k + B (i + 1) (j + (-1)) (k + 0) = _
  simp [sub_eq_add_neg]

@[simp] theorem k4AggregateRDiff_apply
    {n : Nat} [NeZero n] (W : CyclicCube n) (i j k : I n) :
    k4AggregateRDiff W i j k =
      W i j k + W i (j - 1) (k + 1) := by
  change W i j k + W (i + 0) (j + (-1)) (k + 1) = _
  simp [sub_eq_add_neg]

theorem k4CubeKappa_add_left_public
    {n : Nat} [NeZero n] (B B' W : CyclicCube n) :
    k4CubeKappa (B + B') W =
      k4CubeKappa B W + k4CubeKappa B' W := by
  unfold k4CubeKappa
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  abel

theorem k4CubeKappa_add_right_public
    {n : Nat} [NeZero n] (B W W' : CyclicCube n) :
    k4CubeKappa B (W + W') =
      k4CubeKappa B W + k4CubeKappa B W' := by
  unfold k4CubeKappa
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  abel

private theorem k4Aggregate_F_eq_zero_or_one (x : F) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem k4CubeKappa_smul_left_public
    {n : Nat} [NeZero n] (r : F) (B W : CyclicCube n) :
    k4CubeKappa (r • B) W = r * k4CubeKappa B W := by
  rcases k4Aggregate_F_eq_zero_or_one r with rfl | rfl
  · simp [k4CubeKappa]
  · simp

theorem k4CubeKappa_smul_right_public
    {n : Nat} [NeZero n] (r : F) (B W : CyclicCube n) :
    k4CubeKappa B (r • W) = r * k4CubeKappa B W := by
  rcases k4Aggregate_F_eq_zero_or_one r with rfl | rfl
  · simp [k4CubeKappa]
  · simp

noncomputable def k4CubeKappaLinear
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) :=
  LinearMap.mk₂ F k4CubeKappa
    k4CubeKappa_add_left_public
    k4CubeKappa_smul_left_public
    k4CubeKappa_add_right_public
    k4CubeKappa_smul_right_public

@[simp] theorem k4CubeKappaLinear_apply
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappaLinear B W = k4CubeKappa B W := rfl

/-! ## Aggregate cell maps -/

noncomputable def k4BaseBAggregateRaw
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    BFun4 n 1 c d →ₗ[F] (PVec n c → CyclicCube n) where
  toFun B zt :=
    ∑ wt : PVec n d, k4BaseBCell hc hd B zt wt
  map_add' B B' := by
    funext zt i j k
    simp only [k4BaseBCell, map_add, Pi.add_apply,
      Finset.sum_apply, Finset.sum_add_distrib]
  map_smul' r B := by
    funext zt i j k
    simp only [k4BaseBCell, map_smul, Pi.smul_apply,
      Finset.sum_apply, RingHom.id_apply, Finset.smul_sum]

noncomputable def k4BaseWAggregateRaw
    {n b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    WFun4 n 1 b c →ₗ[F] (PVec n c → CyclicCube n) where
  toFun W zt :=
    ∑ yt : PVec n b, k4BaseWCell hb hc W yt zt
  map_add' W W' := by
    funext zt i j k
    simp only [k4BaseWCell, map_add, Pi.add_apply,
      Finset.sum_apply, Finset.sum_add_distrib]
  map_smul' r W := by
    funext zt i j k
    simp only [k4BaseWCell, map_smul, Pi.smul_apply,
      Finset.sum_apply, RingHom.id_apply, Finset.smul_sum]

@[simp] theorem k4BaseBAggregateRaw_apply
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (zt : PVec n c) :
    k4BaseBAggregateRaw hc hd B zt =
      ∑ wt : PVec n d, k4BaseBCell hc hd B zt wt := rfl

@[simp] theorem k4BaseWAggregateRaw_apply
    {n b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (W : WFun4 n 1 b c) (zt : PVec n c) :
    k4BaseWAggregateRaw hb hc W zt =
      ∑ yt : PVec n b, k4BaseWCell hb hc W yt zt := rfl

/-! ## The two exact aggregate kernel carriers -/

noncomputable def k4BAggregateConstraint
    {n c : Nat} [NeZero n] :
    (PVec n c → CyclicCube n) →ₗ[F] CyclicCube n :=
  k4AggregatePDiff.comp
    (fintypeSumLinearMap (S := PVec n c) (V := CyclicCube n))

noncomputable def k4WAggregateConstraint
    {n c : Nat} [NeZero n] :
    (PVec n c → CyclicCube n) →ₗ[F] CyclicCube n :=
  k4AggregateRDiff.comp
    (fintypeSumLinearMap (S := PVec n c) (V := CyclicCube n))

noncomputable abbrev K4BAggregateLeft
    (n c : Nat) [NeZero n] :=
  LinearMap.ker (k4BAggregateConstraint (n := n) (c := c))

noncomputable abbrev K4WAggregateLeft
    (n c : Nat) [NeZero n] :=
  LinearMap.ker (k4WAggregateConstraint (n := n) (c := c))

@[simp] theorem k4BAggregateConstraint_apply
    {n c : Nat} [NeZero n]
    (Bbar : PVec n c → CyclicCube n) :
    k4BAggregateConstraint Bbar =
      k4AggregatePDiff (∑ zt, Bbar zt) := rfl

@[simp] theorem k4WAggregateConstraint_apply
    {n c : Nat} [NeZero n]
    (Wbar : PVec n c → CyclicCube n) :
    k4WAggregateConstraint Wbar =
      k4AggregateRDiff (∑ zt, Wbar zt) := rfl

/-! ## Public reproof of the literal source cell equation -/

theorem k4Base_source_cell_sum_zero_public
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d)
    (yt : PVec n b) (wt : PVec n d) :
    (∑ zt : PVec n c,
      (k4AggregatePDiff (k4BaseBCell hc hd sigma.1.1 zt wt) +
        k4AggregateRDiff (k4BaseWCell hb hc sigma.1.2 yt zt))) = 0 := by
  have hpre :
      diamondPreCMap
          (n := n) (a := 1) (b := b) (c := c) (d := d)
          ((0 : AFun4 n b c d), sigma.1.1, sigma.1.2) = 0 := by
    apply (diamondPreCMap_eq_zero_iff_constraint
      (0 : AFun4 n b c d) sigma.1.1 sigma.1.2).mpr
    have hsquare :
        squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)
          (sigma.1.1, sigma.1.2) = 0 := sigma.2
    simpa only [map_zero] using hsquare.symm
  have hodd :=
    (diamondPreCMap_eq_zero_iff_oddLiteralSourceMap hb hc hd
      ((0 : AFun4 n b c d), sigma.1.1, sigma.1.2)).mp hpre
  funext i j k
  have hp := congrFun
    (congrFun (congrFun (congrFun (congrFun (congrFun hodd
      (zeroVec : PVec n 1)) yt) wt) i) j) k
  rw [diamondOddLiteralSourceMap_apply_pointwise] at hp
  simp only [diamondOddABWGaugeEquiv_apply,
    diamondOddAGaugeEquiv_apply, diamondOddBGaugeEquiv_apply,
    diamondOddWGaugeEquiv_apply, diamondOddAPassiveCubeEquiv_apply,
    Pi.zero_apply, zero_add] at hp
  simp only [Finset.sum_apply, Pi.add_apply,
    k4AggregatePDiff_apply, k4AggregateRDiff_apply,
    k4BaseBCell, k4BaseWCell,
    diamondOddBGaugeEquiv_apply, diamondOddWGaugeEquiv_apply,
    Pi.zero_apply]
  simpa only [add_assoc] using hp

def k4BasePRow
    {n b c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d) (wt : PVec n d) :
    CyclicCube n :=
  ∑ zt : PVec n c,
    k4AggregatePDiff (k4BaseBCell hc hd sigma.1.1 zt wt)

def k4BaseRRow
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (sigma : K4EvenPLeft n b c d) (yt : PVec n b) :
    CyclicCube n :=
  ∑ zt : PVec n c,
    k4AggregateRDiff (k4BaseWCell hb hc sigma.1.2 yt zt)

theorem k4BasePRow_add_RRow_zero
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d)
    (yt : PVec n b) (wt : PVec n d) :
    k4BasePRow hc hd sigma wt + k4BaseRRow hb hc sigma yt = 0 := by
  simpa only [k4BasePRow, k4BaseRRow,
    Finset.sum_add_distrib] using
    k4Base_source_cell_sum_zero_public hb hc hd sigma yt wt

theorem k4Base_sum_PRow_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d) :
    (∑ wt : PVec n d, k4BasePRow hc (by omega) sigma wt) = 0 := by
  let R0 : CyclicCube n :=
    k4BaseRRow hb hc sigma (zeroVec : PVec n b)
  have hrow (wt : PVec n d) :
      k4BasePRow hc (by omega) sigma wt = R0 := by
    exact (add_eq_zero_iff_eq_of_F_module _ _).mp
      (k4BasePRow_add_RRow_zero hb hc (by omega) sigma zeroVec wt)
  calc
    (∑ wt : PVec n d, k4BasePRow hc (by omega) sigma wt) =
        ∑ _wt : PVec n d, R0 := by
          apply Finset.sum_congr rfl
          intro wt _
          exact hrow wt
    _ = 0 := by
      funext i j k
      simp only [Finset.sum_apply, Finset.sum_const, nsmul_eq_mul]
      change (Fintype.card (PVec n d) : F) * R0 i j k = 0
      rw [natCast_even_eq_zero_F (even_card_PVec hn hd2), zero_mul]

theorem k4Base_sum_RRow_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d) :
    (∑ yt : PVec n b, k4BaseRRow (by omega) hc sigma yt) = 0 := by
  let P0 : CyclicCube n :=
    k4BasePRow hc hd sigma (zeroVec : PVec n d)
  have hrow (yt : PVec n b) :
      k4BaseRRow (by omega) hc sigma yt = P0 := by
    apply (add_eq_zero_iff_eq_of_F_module _ _).mp
    simpa only [add_comm] using
      (k4BasePRow_add_RRow_zero (by omega) hc hd sigma yt zeroVec)
  calc
    (∑ yt : PVec n b, k4BaseRRow (by omega) hc sigma yt) =
        ∑ _yt : PVec n b, P0 := by
          apply Finset.sum_congr rfl
          intro yt _
          exact hrow yt
    _ = 0 := by
      funext i j k
      simp only [Finset.sum_apply, Finset.sum_const, nsmul_eq_mul]
      change (Fintype.card (PVec n b) : F) * P0 i j k = 0
      rw [natCast_even_eq_zero_F (even_card_PVec hn hb2), zero_mul]

noncomputable def k4EvenPLeftBLinear
    {n b c d : Nat} [NeZero n] :
    K4EvenPLeft n b c d →ₗ[F] BFun4 n 1 c d where
  toFun sigma := sigma.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4EvenPLeftWLinear
    {n b c d : Nat} [NeZero n] :
    K4EvenPLeft n b c d →ₗ[F] WFun4 n 1 b c where
  toFun sigma := sigma.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4EvenPBAggregateRaw
    {n b c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    K4EvenPLeft n b c d →ₗ[F] (PVec n c → CyclicCube n) :=
  (k4BaseBAggregateRaw hc hd).comp k4EvenPLeftBLinear

noncomputable def k4EvenPWAggregateRaw
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    K4EvenPLeft n b c d →ₗ[F] (PVec n c → CyclicCube n) :=
  (k4BaseWAggregateRaw hb hc).comp k4EvenPLeftWLinear

theorem k4EvenPBAggregateRaw_mem
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d) :
    k4EvenPBAggregateRaw hc (by omega) sigma ∈
      K4BAggregateLeft n c := by
  apply LinearMap.mem_ker.mpr
  rw [k4BAggregateConstraint_apply]
  rw [map_sum]
  simp_rw [k4EvenPBAggregateRaw, LinearMap.comp_apply,
    k4EvenPLeftBLinear, k4BaseBAggregateRaw_apply, map_sum]
  rw [Finset.sum_comm]
  exact k4Base_sum_PRow_zero hn hb hc hd2 sigma

theorem k4EvenPWAggregateRaw_mem
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d) :
    k4EvenPWAggregateRaw (by omega) hc sigma ∈
      K4WAggregateLeft n c := by
  apply LinearMap.mem_ker.mpr
  rw [k4WAggregateConstraint_apply]
  rw [map_sum]
  simp_rw [k4EvenPWAggregateRaw, LinearMap.comp_apply,
    k4EvenPLeftWLinear, k4BaseWAggregateRaw_apply, map_sum]
  rw [Finset.sum_comm]
  exact k4Base_sum_RRow_zero hn hb2 hc hd sigma

noncomputable def k4EvenPBAggregate
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c) (hd2 : 2 ≤ d) :
    K4EvenPLeft n b c d →ₗ[F] K4BAggregateLeft n c :=
  LinearMap.codRestrict (K4BAggregateLeft n c)
    (k4EvenPBAggregateRaw hc (by omega))
    (k4EvenPBAggregateRaw_mem hn hb hc hd2)

noncomputable def k4EvenPWAggregate
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd : 0 < d) :
    K4EvenPLeft n b c d →ₗ[F] K4WAggregateLeft n c :=
  LinearMap.codRestrict (K4WAggregateLeft n c)
    (k4EvenPWAggregateRaw (by omega) hc)
    (k4EvenPWAggregateRaw_mem hn hb2 hc hd)

noncomputable def k4EvenPAggregate
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd2 : 2 ≤ d) :
    K4EvenPLeft n b c d →ₗ[F]
      (K4BAggregateLeft n c × K4WAggregateLeft n c) :=
  LinearMap.prod
    (k4EvenPBAggregate hn (by omega) hc hd2)
    (k4EvenPWAggregate hn hb2 hc (by omega))

/-! ## Explicit distinguished-tail lift -/

noncomputable def k4BOneTailFamily
    {n c d : Nat} [NeZero n] :
    (PVec n c → CyclicCube n) →ₗ[F]
      (PVec n c → PVec n d → CyclicCube n) where
  toFun Bbar zt wt :=
    if wt = zeroVec then Bbar zt else 0
  map_add' B B' := by
    funext zt wt
    by_cases hwt : wt = zeroVec <;> simp [hwt]
  map_smul' r B := by
    funext zt wt
    by_cases hwt : wt = zeroVec <;> simp [hwt]

noncomputable def k4WOneTailFamily
    {n b c : Nat} [NeZero n] :
    (PVec n c → CyclicCube n) →ₗ[F]
      (PVec n b → PVec n c → CyclicCube n) where
  toFun Wbar yt zt :=
    if yt = zeroVec then Wbar zt else 0
  map_add' W W' := by
    funext yt zt
    by_cases hyt : yt = zeroVec <;> simp [hyt]
  map_smul' r W := by
    funext yt zt
    by_cases hyt : yt = zeroVec <;> simp [hyt]

noncomputable def k4AggregateOneTailFamily
    {n b c d : Nat} [NeZero n] :
    (K4BAggregateLeft n c × K4WAggregateLeft n c) →ₗ[F]
      ((PVec n c → PVec n d → CyclicCube n) ×
        (PVec n b → PVec n c → CyclicCube n)) where
  toFun x := (k4BOneTailFamily x.1.1, k4WOneTailFamily x.2.1)
  map_add' x y := by
    apply Prod.ext
    · exact (k4BOneTailFamily (n := n) (c := c) (d := d)).map_add x.1 y.1
    · exact (k4WOneTailFamily (n := n) (b := b) (c := c)).map_add x.2 y.2
  map_smul' r x := by
    apply Prod.ext
    · exact (k4BOneTailFamily (n := n) (c := c) (d := d)).map_smul r x.1
    · exact (k4WOneTailFamily (n := n) (b := b) (c := c)).map_smul r x.2

noncomputable def k4AggregateLiftRaw
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (K4BAggregateLeft n c × K4WAggregateLeft n c) →ₗ[F]
      K4EvenPSlice n b c d :=
  (literalGaugeEquiv hb hc hd).symm.toLinearMap.comp
    k4AggregateOneTailFamily

theorem k4AggregateLiftRaw_gauge
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    literalGaugeEquiv hb hc hd (k4AggregateLiftRaw hb hc hd x) =
      k4AggregateOneTailFamily x := by
  exact (literalGaugeEquiv hb hc hd).apply_symm_apply
    (k4AggregateOneTailFamily x)

theorem k4AggregateLiftRaw_mem
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    k4AggregateLiftRaw hb hc hd x ∈ K4EvenPLeft n b c d := by
  rw [literal_mem_iff_uniform hb hc hd]
  intro yt wt
  rw [k4AggregateLiftRaw_gauge]
  have hB :
      cubeDiffP (∑ zt : PVec n c, x.1.1 zt) = 0 := by
    exact LinearMap.mem_ker.mp x.1.2
  have hW :
      cubeDiffR (∑ zt : PVec n c, x.2.1 zt) = 0 := by
    exact LinearMap.mem_ker.mp x.2.2
  by_cases hwt : wt = zeroVec
  · by_cases hyt : yt = zeroVec
    · simp only [k4AggregateOneTailFamily, LinearMap.coe_mk,
        AddHom.coe_mk, k4BOneTailFamily, k4WOneTailFamily,
        hwt, hyt, ↓reduceIte, hB, hW, add_zero]
    · simp only [k4AggregateOneTailFamily, LinearMap.coe_mk,
        AddHom.coe_mk, k4BOneTailFamily, k4WOneTailFamily,
        hwt, hyt, ↓reduceIte, Finset.sum_const_zero, map_zero, hB,
        add_zero]
  · by_cases hyt : yt = zeroVec
    · simp only [k4AggregateOneTailFamily, LinearMap.coe_mk,
        AddHom.coe_mk, k4BOneTailFamily, k4WOneTailFamily,
        hwt, hyt, ↓reduceIte, Finset.sum_const_zero, map_zero, hW,
        zero_add]
    · simp only [k4AggregateOneTailFamily, LinearMap.coe_mk,
        AddHom.coe_mk, k4BOneTailFamily, k4WOneTailFamily,
        hwt, hyt, ↓reduceIte, Finset.sum_const_zero, map_zero, add_zero]

noncomputable def k4AggregateLift
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (K4BAggregateLeft n c × K4WAggregateLeft n c) →ₗ[F]
      K4EvenPLeft n b c d :=
  LinearMap.codRestrict (K4EvenPLeft n b c d)
    (k4AggregateLiftRaw hb hc hd)
    (k4AggregateLiftRaw_mem hb hc hd)

theorem k4BaseBCell_aggregateLift
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c)
    (zt : PVec n c) (wt : PVec n d) :
    k4BaseBCell hc hd (k4AggregateLift hb hc hd x).1.1 zt wt =
      if wt = zeroVec then x.1.1 zt else 0 := by
  change
    (literalGaugeEquiv hb hc hd (k4AggregateLiftRaw hb hc hd x)).1 zt wt = _
  rw [k4AggregateLiftRaw_gauge]
  rfl

theorem k4BaseWCell_aggregateLift
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c)
    (yt : PVec n b) (zt : PVec n c) :
    k4BaseWCell hb hc (k4AggregateLift hb hc hd x).1.2 yt zt =
      if yt = zeroVec then x.2.1 zt else 0 := by
  change
    (literalGaugeEquiv hb hc hd (k4AggregateLiftRaw hb hc hd x)).2 yt zt = _
  rw [k4AggregateLiftRaw_gauge]
  rfl

theorem k4EvenPBAggregateRaw_lift
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    k4EvenPBAggregateRaw hc hd (k4AggregateLift hb hc hd x) = x.1.1 := by
  funext zt
  simp only [k4EvenPBAggregateRaw, LinearMap.comp_apply,
    k4EvenPLeftBLinear, k4BaseBAggregateRaw_apply]
  calc
    (∑ wt : PVec n d,
      k4BaseBCell hc hd (k4AggregateLift hb hc hd x).1.1 zt wt) =
        ∑ wt : PVec n d,
          if wt = zeroVec then x.1.1 zt else 0 := by
            apply Finset.sum_congr rfl
            intro wt _
            exact k4BaseBCell_aggregateLift hb hc hd x zt wt
    _ = x.1.1 zt := by
      rw [Finset.sum_eq_single (zeroVec : PVec n d)]
      · simp
      · intro wt _ hwt
        simp [hwt]
      · simp

theorem k4EvenPWAggregateRaw_lift
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    k4EvenPWAggregateRaw hb hc (k4AggregateLift hb hc hd x) = x.2.1 := by
  funext zt
  simp only [k4EvenPWAggregateRaw, LinearMap.comp_apply,
    k4EvenPLeftWLinear, k4BaseWAggregateRaw_apply]
  calc
    (∑ yt : PVec n b,
      k4BaseWCell hb hc (k4AggregateLift hb hc hd x).1.2 yt zt) =
        ∑ yt : PVec n b,
          if yt = zeroVec then x.2.1 zt else 0 := by
            apply Finset.sum_congr rfl
            intro yt _
            exact k4BaseWCell_aggregateLift hb hc hd x yt zt
    _ = x.2.1 zt := by
      rw [Finset.sum_eq_single (zeroVec : PVec n b)]
      · simp
      · intro yt _ hyt
        simp [hyt]
      · simp

@[simp] theorem k4EvenPAggregate_lift
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd2 : 2 ≤ d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    k4EvenPAggregate hn hb2 hc hd2
        (k4AggregateLift (by omega) hc (by omega) x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    exact k4EvenPBAggregateRaw_lift (by omega) hc (by omega) x
  · apply Subtype.ext
    exact k4EvenPWAggregateRaw_lift (by omega) hc (by omega) x

theorem k4EvenPAggregate_surjective
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd2 : 2 ≤ d) :
    Function.Surjective (k4EvenPAggregate hn hb2 hc hd2) := by
  intro x
  exact ⟨k4AggregateLift (by omega) hc (by omega) x,
    k4EvenPAggregate_lift hn hb2 hc hd2 x⟩

/-! ## Exact aggregate phase and hyperbolic polar -/

theorem k4CubeKappa_sum_left_public
    {n : Nat} [NeZero n]
    {S : Type*} [Fintype S]
    (B : S → CyclicCube n) (W : CyclicCube n) :
    k4CubeKappa (∑ s, B s) W = ∑ s, k4CubeKappa (B s) W := by
  classical
  let U : Finset S := Finset.univ
  change k4CubeKappa (∑ s ∈ U, B s) W =
    ∑ s ∈ U, k4CubeKappa (B s) W
  induction U using Finset.induction_on with
  | empty => simp [k4CubeKappa]
  | @insert a U ha ih =>
      simp only [Finset.sum_insert ha]
      rw [k4CubeKappa_add_left_public, ih]

theorem k4CubeKappa_sum_right_public
    {n : Nat} [NeZero n]
    {S : Type*} [Fintype S]
    (B : CyclicCube n) (W : S → CyclicCube n) :
    k4CubeKappa B (∑ s, W s) = ∑ s, k4CubeKappa B (W s) := by
  change (k4CubeKappaLinear B) (∑ s, W s) = _
  rw [map_sum]
  simp only [k4CubeKappaLinear_apply]

def k4AggregateKappaScalar
    {n c : Nat} [NeZero n]
    (Bbar Wbar : PVec n c → CyclicCube n) : F :=
  ∑ zt : PVec n c, k4CubeKappa (Bbar zt) (Wbar zt)

theorem k4AggregateKappaScalar_add_left
    {n c : Nat} [NeZero n]
    (B B' W : PVec n c → CyclicCube n) :
    k4AggregateKappaScalar (B + B') W =
      k4AggregateKappaScalar B W + k4AggregateKappaScalar B' W := by
  unfold k4AggregateKappaScalar
  simp only [Pi.add_apply, k4CubeKappa_add_left_public,
    Finset.sum_add_distrib]

theorem k4AggregateKappaScalar_add_right
    {n c : Nat} [NeZero n]
    (B W W' : PVec n c → CyclicCube n) :
    k4AggregateKappaScalar B (W + W') =
      k4AggregateKappaScalar B W + k4AggregateKappaScalar B W' := by
  unfold k4AggregateKappaScalar
  simp only [Pi.add_apply, k4CubeKappa_add_right_public,
    Finset.sum_add_distrib]

theorem k4AggregateKappaScalar_smul_left
    {n c : Nat} [NeZero n]
    (r : F) (B W : PVec n c → CyclicCube n) :
    k4AggregateKappaScalar (r • B) W =
      r * k4AggregateKappaScalar B W := by
  unfold k4AggregateKappaScalar
  simp only [Pi.smul_apply, k4CubeKappa_smul_left_public,
    Finset.mul_sum]

theorem k4AggregateKappaScalar_smul_right
    {n c : Nat} [NeZero n]
    (r : F) (B W : PVec n c → CyclicCube n) :
    k4AggregateKappaScalar B (r • W) =
      r * k4AggregateKappaScalar B W := by
  unfold k4AggregateKappaScalar
  simp only [Pi.smul_apply, k4CubeKappa_smul_right_public,
    Finset.mul_sum]

noncomputable def k4AggregateKappaLinear
    {n c : Nat} [NeZero n] :
    (PVec n c → CyclicCube n) →ₗ[F]
      Module.Dual F (PVec n c → CyclicCube n) :=
  LinearMap.mk₂ F k4AggregateKappaScalar
    k4AggregateKappaScalar_add_left
    k4AggregateKappaScalar_smul_left
    k4AggregateKappaScalar_add_right
    k4AggregateKappaScalar_smul_right

@[simp] theorem k4AggregateKappaLinear_apply
    {n c : Nat} [NeZero n]
    (B W : PVec n c → CyclicCube n) :
    k4AggregateKappaLinear B W = k4AggregateKappaScalar B W := rfl

noncomputable def k4ZAggregateCross
    {n c : Nat} [NeZero n] :
    K4BAggregateLeft n c →ₗ[F] Module.Dual F (K4WAggregateLeft n c) :=
  (LinearMap.dualMap (K4WAggregateLeft n c).subtype).comp
    (k4AggregateKappaLinear.comp (K4BAggregateLeft n c).subtype)

@[simp] theorem k4ZAggregateCross_apply
    {n c : Nat} [NeZero n]
    (B : K4BAggregateLeft n c) (W : K4WAggregateLeft n c) :
    k4ZAggregateCross B W = k4AggregateKappaScalar B.1 W.1 := rfl

def k4AggregatePolarScalar
    {n c : Nat} [NeZero n]
    (x y : K4BAggregateLeft n c × K4WAggregateLeft n c) : F :=
  k4ZAggregateCross x.1 y.2 + k4ZAggregateCross y.1 x.2

private theorem k4AggregatePolarScalar_add_left
    {n c : Nat} [NeZero n]
    (x x' y : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    k4AggregatePolarScalar (x + x') y =
      k4AggregatePolarScalar x y + k4AggregatePolarScalar x' y := by
  simp only [k4AggregatePolarScalar, Prod.fst_add, Prod.snd_add, map_add,
    LinearMap.add_apply]
  abel

private theorem k4AggregatePolarScalar_add_right
    {n c : Nat} [NeZero n]
    (x y y' : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    k4AggregatePolarScalar x (y + y') =
      k4AggregatePolarScalar x y + k4AggregatePolarScalar x y' := by
  simp only [k4AggregatePolarScalar, Prod.fst_add, Prod.snd_add, map_add,
    LinearMap.add_apply]
  abel

private theorem k4AggregatePolarScalar_smul_left
    {n c : Nat} [NeZero n]
    (r : F) (x y : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    k4AggregatePolarScalar (r • x) y =
      r * k4AggregatePolarScalar x y := by
  simp only [k4AggregatePolarScalar, Prod.smul_fst, Prod.smul_snd,
    map_smul, LinearMap.smul_apply, smul_eq_mul, mul_add]

private theorem k4AggregatePolarScalar_smul_right
    {n c : Nat} [NeZero n]
    (r : F) (x y : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    k4AggregatePolarScalar x (r • y) =
      r * k4AggregatePolarScalar x y := by
  simp only [k4AggregatePolarScalar, Prod.smul_fst, Prod.smul_snd,
    map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

noncomputable def k4AggregateHyperbolicPolar
    {n c : Nat} [NeZero n] :
    (K4BAggregateLeft n c × K4WAggregateLeft n c) →ₗ[F]
      Module.Dual F (K4BAggregateLeft n c × K4WAggregateLeft n c) :=
  LinearMap.mk₂ F k4AggregatePolarScalar
    k4AggregatePolarScalar_add_left
    k4AggregatePolarScalar_smul_left
    k4AggregatePolarScalar_add_right
    k4AggregatePolarScalar_smul_right

@[simp] theorem k4AggregateHyperbolicPolar_apply
    {n c : Nat} [NeZero n]
    (x y : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    k4AggregateHyperbolicPolar x y = k4AggregatePolarScalar x y := rfl

theorem k4BWSlice_eq_aggregate_kappa
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (W : WFun4 n 1 b c) :
    k4BWSlice B W =
      k4AggregateKappaScalar
        (k4BaseBAggregateRaw hc hd B)
        (k4BaseWAggregateRaw hb hc W) := by
  rw [k4BWSlice_eq_sum_cell_kappa hb hc hd]
  unfold k4AggregateKappaScalar
  simp_rw [k4BaseBAggregateRaw_apply, k4BaseWAggregateRaw_apply,
    k4CubeKappa_sum_left_public, k4CubeKappa_sum_right_public]
  calc
    (∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
      k4CubeKappa (k4BaseBCell hc hd B zt wt)
        (k4BaseWCell hb hc W yt zt)) =
      ∑ zt : PVec n c, ∑ yt : PVec n b, ∑ wt : PVec n d,
        k4CubeKappa (k4BaseBCell hc hd B zt wt)
          (k4BaseWCell hb hc W yt zt) := by
        rw [Finset.sum_comm]
    _ = ∑ zt : PVec n c, ∑ wt : PVec n d, ∑ yt : PVec n b,
        k4CubeKappa (k4BaseBCell hc hd B zt wt)
          (k4BaseWCell hb hc W yt zt) := by
        apply Finset.sum_congr rfl
        intro zt _
        rw [Finset.sum_comm]

theorem k4EvenPSlicePolar_eq_aggregatePolar
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd2 : 2 ≤ d)
    (sigma tau : K4EvenPLeft n b c d) :
    k4EvenPSlicePolar sigma.1 tau.1 =
      k4AggregatePolarScalar
        (k4EvenPAggregate hn hb2 hc hd2 sigma)
        (k4EvenPAggregate hn hb2 hc hd2 tau) := by
  unfold k4EvenPSlicePolar k4AggregatePolarScalar
  rw [k4BWSlice_eq_aggregate_kappa (by omega) hc (by omega),
    k4BWSlice_eq_aggregate_kappa (by omega) hc (by omega)]
  rfl

theorem k4EvenPGPolar_factor_through_aggregate
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd2 : 2 ≤ d) :
    k4EvenPGPolar (n := n) (b := b) (c := c) (d := d) =
      (LinearMap.dualMap (k4EvenPAggregate hn hb2 hc hd2)).comp
        (k4AggregateHyperbolicPolar.comp
          (k4EvenPAggregate hn hb2 hc hd2)) := by
  apply LinearMap.ext
  intro sigma
  apply LinearMap.ext
  intro tau
  exact k4EvenPSlicePolar_eq_aggregatePolar hn hb2 hc hd2 sigma tau

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
