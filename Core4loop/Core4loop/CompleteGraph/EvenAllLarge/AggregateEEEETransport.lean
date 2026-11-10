import Core4loop.CompleteGraph.EvenAllLarge.BaseMixedOverlap

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal

noncomputable section

attribute [local instance] Fintype.ofFinite

private noncomputable def eeeeNestedSrcRead
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U]
    (hS : Even (Fintype.card S))
    (hT : Even (Fintype.card T))
    (f : S → T → U) :
    TotalEOEEInternal.TailCoordHelpers.NestedSrcEvenTarget
      S T U s0 t0 :=
  let x := pointedSrcEvenValueEquiv S (T → U) s0 hS f
  let x₀ := pointedSrcEvenValueEquiv T U t0 hT x.1.1
  let x₁ := pointedSrcEvenValueEquiv T U t0 hT x.1.2
  let xt :=
    TotalEOEEInternal.TailCoordHelpers.tailZeroCongr s0
      (pointedSrcEvenValueEquiv T U t0 hT) x.2
  let tTail :=
    (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
      (S := T) (U := U) (V := U) t0).symm (x₀.2, x₁.2)
  let sTail :=
    TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
      (S := S) (U := U × U)
      (V := PointedValueTailZero T U t0) s0 xt
  ((x₀.1, x₁.1), (tTail, (sTail.1, sTail.2)))

private theorem bNestedCoords_eq_eeeeNestedSrcRead
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (B : BFun4 n 1 c d) :
    bNestedCoords hn hc2 hd2 B =
      eeeeNestedSrcRead
        (PVec n c) (PVec n d) (CyclicCube n)
        (zeroVec : PVec n c) (zeroVec : PVec n d)
        (even_card_PVec hn hc2) (even_card_PVec hn hd2)
        (TotalEOEEInternal.bGaugedRootFamilyEquiv
          (by omega : 0 < c) (by omega : 0 < d) B) := by
  rfl

private theorem wNestedCoords_eq_eeeeNestedSrcRead
    {n b c : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (W : WFun4 n 1 b c) :
    wNestedCoords hn hb2 hc2 W =
      eeeeNestedSrcRead
        (PVec n b) (PVec n c) (CyclicCube n)
        (zeroVec : PVec n b) (zeroVec : PVec n c)
        (even_card_PVec hn hb2) (even_card_PVec hn hc2)
        (wGaugedYZFamilyEquiv
          (by omega : 0 < b) (by omega : 0 < c) W) := by
  rfl

private theorem eeeeRead_scalar
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d) :
    let q := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma
    q.1.1 =
      ((bNestedCoords hn hc2 hd2 sigma.1.1).1,
        (wNestedCoords hn hb2 hc2 sigma.1.2).1) := by
  rfl

private theorem eeeeRead_Z
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d)
    (t : PointedTail (PVec n c) zeroVec) :
    let q := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma
    q.2.2.2.1.1 t =
      (((bNestedCoords hn hc2 hd2 sigma.1.1).2.2.1.1 t),
        ((wNestedCoords hn hb2 hc2 sigma.1.2).2.1.1 t)) := by
  rfl

private theorem oddVecHeadTail_eq_evenVecHeadTail
    {n k : Nat} [NeZero n] (hk : 0 < k) :
    SquareDiagonal.DirectWitt.diamondOddVecHeadTailEquiv
        (n := n) (k := k) hk =
      diamondVecHeadTailEquiv (n := n) (k := k) hk := by
  cases k with
  | zero => omega
  | succ k => rfl

private theorem k4BaseBCell_eq_bGauged
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d) :
    k4BaseBCell hc hd B zt wt =
      TotalEOEEInternal.bGaugedRootFamilyEquiv hc hd B zt wt := by
  funext i j k
  simp only [k4BaseBCell,
    SquareDiagonal.DirectWitt.diamondOddBGaugeEquiv_apply,
    SquareDiagonal.DirectWitt.diamondOddBPassiveCubeEquiv_apply,
    TotalEOEEInternal.bGaugedRootFamilyEquiv_apply,
    diamondBRootCubeEquiv_apply]
  rw [oddVecHeadTail_eq_evenVecHeadTail (n := n) hc,
    oddVecHeadTail_eq_evenVecHeadTail (n := n) hd]

private theorem k4BaseWCell_eq_wGauged
    {n b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (W : WFun4 n 1 b c) (yt : PVec n b) (zt : PVec n c) :
    k4BaseWCell hb hc W yt zt =
      wGaugedYZFamilyEquiv hb hc W yt zt := by
  funext i j k
  simp only [k4BaseWCell,
    SquareDiagonal.DirectWitt.diamondOddWGaugeEquiv_apply,
    SquareDiagonal.DirectWitt.diamondOddWPassiveCubeEquiv_apply,
    wGaugedYZFamilyEquiv_apply,
    diamondWRootCubeEquiv_apply]
  rw [oddVecHeadTail_eq_evenVecHeadTail (n := n) hb,
    oddVecHeadTail_eq_evenVecHeadTail (n := n) hc]

private theorem eeeeCast_odd_eq_one
    {m : Nat} (hm : Odd m) : (m : F) = 1 := by
  rcases hm with ⟨q, hq⟩
  rw [hq]
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem eeeeSum_const_odd
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = v := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    eeeeCast_odd_eq_one hodd, one_smul]

private theorem eeeeSum_at_point_add_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommMonoid V] (f : S → V) :
    (∑ s, f s) = f s0 + ∑ t : PointedTail S s0, f t.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset S))
      (p := fun s : S => s = s0) f).symm
  calc
    (∑ s, f s) =
        (∑ s ∈ (Finset.univ : Finset S) with s = s0, f s) +
          ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
            simpa using hpart
    _ = f s0 +
        ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
          congr 1
          rw [Finset.sum_eq_single s0]
          · intro s hs hne
            exact (hne (Finset.mem_filter.mp hs).2).elim
          · simp
    _ = f s0 + ∑ t : PointedTail S s0, f t.1 := by
          congr 1
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset S))
              (p := fun s : S => s ≠ s0) (f := f)).symm

private theorem eeeeAdd_self
    {V : Type*} [AddCommGroup V] [Module F V] (x : V) :
    x + x = 0 :=
  (add_eq_zero_iff_eq_of_F_module x x).2 rfl

private theorem scalarB00_mem
    {n b c d : Nat} [NeZero n]
    (q : SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d) :
    q.1.1.1.1.1 ∈ LinearMap.ker (cubeDiffP (n := n)) := by
  apply LinearMap.mem_ker.mpr
  have h := congrArg (fun x => x.1.1) (LinearMap.mem_ker.mp q.1.2)
  change cubeDiffP q.1.1.1.1.1 = 0 at h
  exact h

private theorem scalarW00_mem
    {n b c d : Nat} [NeZero n]
    (q : SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d) :
    q.1.1.2.1.1 ∈ LinearMap.ker (cubeDiffR (n := n)) := by
  apply LinearMap.mem_ker.mpr
  have h := congrArg (fun x => x.1.2) (LinearMap.mem_ker.mp q.1.2)
  change cubeDiffR q.1.1.2.1.1 = 0 at h
  exact h

private theorem ztailBSigma_mem
    {n b c d : Nat} [NeZero n]
    (q : SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d) :
    (fun zt => (q.2.2.2.1.1 zt).1.1) ∈
      DiamondEvenAxisValueTailZero n c (CyclicCube n) := by
  apply LinearMap.mem_ker.mpr
  have h := LinearMap.mem_ker.mp q.2.2.2.1.2
  simpa only [fintypeSumLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    Prod.fst_sum] using congrArg (fun x => x.1.1) h

private theorem ztailWSigma_mem
    {n b c d : Nat} [NeZero n]
    (q : SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d) :
    (fun zt => (q.2.2.2.1.1 zt).2.1) ∈
      DiamondEvenAxisValueTailZero n c (CyclicCube n) := by
  apply LinearMap.mem_ker.mpr
  have h := LinearMap.mem_ker.mp q.2.2.2.1.2
  simpa only [fintypeSumLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    Prod.fst_sum, Prod.snd_sum] using
    congrArg (fun x => x.2.1) h

noncomputable def k4AggregateEEEERead
    {n b c d : Nat} [NeZero n] :
    SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d →ₗ[F]
      (K4BAggregateCoords n c × K4WAggregateCoords n c) where
  toFun q :=
    (((⟨q.1.1.1.1.1, scalarB00_mem q⟩, q.1.1.1.2.1),
        ⟨(fun zt => (q.2.2.2.1.1 zt).1.1), ztailBSigma_mem q⟩),
      ((q.1.1.2.1.1 + q.1.1.2.1.2,
          ⟨q.1.1.2.1.1, scalarW00_mem q⟩),
        ⟨(fun zt => (q.2.2.2.1.1 zt).2.1), ztailWSigma_mem q⟩))
  map_add' q q' := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl
      · apply Subtype.ext
        rfl
    · apply Prod.ext
      · apply Prod.ext
        · change
            (q.1.1.2.1.1 + q'.1.1.2.1.1) +
                (q.1.1.2.1.2 + q'.1.1.2.1.2) =
              (q.1.1.2.1.1 + q.1.1.2.1.2) +
                (q'.1.1.2.1.1 + q'.1.1.2.1.2)
          abel
        · apply Subtype.ext
          rfl
      · apply Subtype.ext
        rfl
  map_smul' r q := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl
      · apply Subtype.ext
        rfl
    · apply Prod.ext
      · apply Prod.ext
        · simp [smul_add]
        · apply Subtype.ext
          rfl
      · apply Subtype.ext
        rfl

set_option linter.flexible false in
-- The proof deliberately unfolds a formula-level nested finite-source coordinate.
set_option synthInstance.maxHeartbeats 2000000 in
-- Unfolding the nested pointed-source equivalences needs a larger instance budget.
private theorem aggregateB00_eq_eeee
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d) :
    let A := k4EvenPAggregate hn hb2 (by omega : 0 < c) hd2 sigma
    let q := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma
    (k4BAggregateCoordEquiv hn hc2 A.1).1.1.1 =
      q.1.1.1.1.1 := by
  dsimp only
  rw [eeeeRead_scalar]
  rw [bNestedCoords_eq_eeeeNestedSrcRead]
  simp [eeeeNestedSrcRead, k4BAggregateCoordEquiv,
    k4EvenPAggregate, k4EvenPBAggregate,
    k4EvenPBAggregateRaw, k4EvenPLeftBLinear,
    k4BaseBAggregateRaw, diamondEvenAxisSrcCoordEquiv,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply]
  simp_rw [k4BaseBCell_eq_bGauged]
  exact Finset.sum_comm

set_option linter.flexible false in
-- The proof deliberately unfolds a formula-level nested finite-source coordinate.
set_option synthInstance.maxHeartbeats 2000000 in
-- Unfolding the nested pointed-source equivalences needs a larger instance budget.
private theorem aggregateB10_eq_eeee
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d) :
    let A := k4EvenPAggregate hn hb2 (by omega : 0 < c) hd2 sigma
    let q := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma
    (k4BAggregateCoordEquiv hn hc2 A.1).1.2 =
      q.1.1.1.2.1 := by
  dsimp only
  rw [eeeeRead_scalar]
  rw [bNestedCoords_eq_eeeeNestedSrcRead]
  simp [eeeeNestedSrcRead, k4BAggregateCoordEquiv,
    k4EvenPAggregate, k4EvenPBAggregate,
    k4EvenPBAggregateRaw, k4EvenPLeftBLinear,
    k4BaseBAggregateRaw, diamondEvenAxisSrcCoordEquiv,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply]
  simp_rw [k4BaseBCell_eq_bGauged]
  exact Finset.sum_comm

set_option linter.flexible false in
-- The proof deliberately unfolds a formula-level nested finite-tail coordinate.
set_option synthInstance.maxHeartbeats 2000000 in
-- Unfolding the nested pointed-tail equivalences needs a larger instance budget.
private theorem aggregateBZ_eq_eeee
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d)
    (t : PointedTail (PVec n c) zeroVec) :
    let A := k4EvenPAggregate hn hb2 (by omega : 0 < c) hd2 sigma
    let q := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma
    (k4BAggregateCoordEquiv hn hc2 A.1).2.1 t =
      (q.2.2.2.1.1 t).1.1 := by
  dsimp only
  rw [eeeeRead_Z]
  rw [bNestedCoords_eq_eeeeNestedSrcRead]
  simp [eeeeNestedSrcRead, k4BAggregateCoordEquiv,
    k4EvenPAggregate, k4EvenPBAggregate,
    k4EvenPBAggregateRaw, k4EvenPLeftBLinear,
    k4BaseBAggregateRaw, diamondEvenAxisSrcCoordEquiv,
    TotalEOEEInternal.TailCoordHelpers.tailZeroCongr,
    TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K,
    pointedSrcEvenValueEquiv_apply_tail, Finset.sum_apply]
  simp_rw [k4BaseBCell_eq_bGauged]
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

set_option maxHeartbeats 2000000 in
-- Normalizing the two nested finite source sums needs a larger tactic budget.
set_option synthInstance.maxHeartbeats 2000000 in
-- The nested pointed-source coordinate types need a larger instance budget.
private theorem wNestedPointSum_eq_zeroSlice
    {n b c : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (W : WFun4 n 1 b c) :
    (wNestedCoords hn hb2 hc2 W).1.1.1 +
        (wNestedCoords hn hb2 hc2 W).1.1.2 =
      ∑ yt : PVec n b,
        wGaugedYZFamilyEquiv (by omega) (by omega) W yt zeroVec := by
  rw [wNestedCoords_eq_eeeeNestedSrcRead]
  simp only [eeeeNestedSrcRead,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply]
  let f : PVec n c → CyclicCube n := fun zt =>
    ∑ yt : PVec n b,
      wGaugedYZFamilyEquiv (by omega) (by omega) W yt zt
  change (∑ zt, f zt) +
      (∑ t : PointedTail (PVec n c) zeroVec, f t.1) = f zeroVec
  rw [eeeeSum_at_point_add_tail
    (S := PVec n c) (V := CyclicCube n)
    (zeroVec : PVec n c) f]
  rw [add_assoc, eeeeAdd_self, add_zero]

set_option maxHeartbeats 2000000 in
-- Normalizing the nested finite total sum needs a larger tactic budget.
set_option synthInstance.maxHeartbeats 2000000 in
-- The nested pointed-source coordinate types need a larger instance budget.
private theorem wNestedW00_eq_total
    {n b c : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (W : WFun4 n 1 b c) :
    (wNestedCoords hn hb2 hc2 W).1.1.1 =
      ∑ zt : PVec n c, ∑ yt : PVec n b,
        wGaugedYZFamilyEquiv (by omega) (by omega) W yt zt := by
  rw [wNestedCoords_eq_eeeeNestedSrcRead]
  simp [eeeeNestedSrcRead,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply]

set_option maxHeartbeats 2000000 in
-- Rewriting the literal W-cell finite sum needs a larger tactic budget.
set_option synthInstance.maxHeartbeats 2000000 in
-- The nested EEEE source projection needs a larger instance budget.
private theorem aggregateWPoint_eq_eeee
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d) :
    let A := k4EvenPAggregate hn hb2 (by omega : 0 < c) hd2 sigma
    let q := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma
    (k4WAggregateCoordEquiv hn hc2 A.2).1.1 =
      q.1.1.2.1.1 + q.1.1.2.1.2 := by
  dsimp only
  rw [eeeeRead_scalar]
  change (∑ yt : PVec n b,
      k4BaseWCell (by omega) (by omega) sigma.1.2 yt zeroVec) =
    (wNestedCoords hn hb2 hc2 sigma.1.2).1.1.1 +
      (wNestedCoords hn hb2 hc2 sigma.1.2).1.1.2
  simp_rw [k4BaseWCell_eq_wGauged]
  exact (wNestedPointSum_eq_zeroSlice
    hn hb2 hc2 sigma.1.2).symm

set_option maxHeartbeats 2000000 in
-- Rewriting the dual-head total sum needs a larger tactic budget.
set_option synthInstance.maxHeartbeats 2000000 in
-- The dual coordinate equivalence needs a larger instance budget.
private theorem aggregateW00_eq_eeee
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d) :
    let A := k4EvenPAggregate hn hb2 (by omega : 0 < c) hd2 sigma
    let q := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma
    (k4WAggregateCoordEquiv hn hc2 A.2).1.2.1 =
      q.1.1.2.1.1 := by
  dsimp only
  rw [eeeeRead_scalar]
  let f : PVec n c → CyclicCube n := fun zt =>
    ∑ yt : PVec n b,
      k4BaseWCell (by omega) (by omega) sigma.1.2 yt zt
  change (diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2 f).1.2 =
    (wNestedCoords hn hb2 hc2 sigma.1.2).1.1.1
  rw [TotalEEEERightInternal.axisDualHead_eq_totalSum]
  dsimp only [f]
  simp_rw [k4BaseWCell_eq_wGauged]
  exact (wNestedW00_eq_total hn hb2 hc2 sigma.1.2).symm

set_option linter.flexible false in
-- The proof deliberately unfolds the dual tail to expose its literal finite sums.
set_option synthInstance.maxHeartbeats 2000000 in
-- The nested dual-tail coordinate normalization needs a larger instance budget.
private theorem aggregateWZ_eq_eeee
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d)
    (t : PointedTail (PVec n c) zeroVec) :
    let A := k4EvenPAggregate hn hb2 (by omega : 0 < c) hd2 sigma
    let q := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma
    (k4WAggregateCoordEquiv hn hc2 A.2).2.1 t =
      (q.2.2.2.1.1 t).2.1 := by
  dsimp only
  rw [eeeeRead_Z]
  rw [wNestedCoords_eq_eeeeNestedSrcRead]
  simp [eeeeNestedSrcRead, k4WAggregateCoordEquiv,
    k4EvenPAggregate, k4EvenPWAggregate,
    k4EvenPWAggregateRaw, k4EvenPLeftWLinear,
    k4BaseWAggregateRaw, diamondEvenAxisDualCoordEquiv,
    diamondEvenAxisSrcCoordEquiv,
    TotalEOEEInternal.TailCoordHelpers.tailZeroCongr,
    TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K,
    pointedSrcEvenValueEquiv_apply_tail, Finset.sum_apply]
  simp_rw [k4BaseWCell_eq_wGauged]
  let f : PVec n c → CyclicCube n := fun zt =>
    ∑ yt : PVec n b,
      wGaugedYZFamilyEquiv (by omega) (by omega) sigma.1.2 yt zt
  change f t.1 + f zeroVec +
      (∑ u : PointedTail (PVec n c) zeroVec,
        (f u.1 + f zeroVec)) =
    f t.1 + ∑ u : PointedTail (PVec n c) zeroVec, f u.1
  rw [Finset.sum_add_distrib,
    eeeeSum_const_odd (odd_card_diamondEvenAxisTailIndex hn hc2)]
  calc
    f t.1 + f zeroVec +
          ((∑ u : PointedTail (PVec n c) zeroVec, f u.1) +
            f zeroVec) =
        f t.1 + (∑ u : PointedTail (PVec n c) zeroVec, f u.1) +
          (f zeroVec + f zeroVec) := by abel
    _ = f t.1 + ∑ u : PointedTail (PVec n c) zeroVec, f u.1 := by
      rw [eeeeAdd_self, add_zero]

set_option maxHeartbeats 12000000 in
-- Product extensionality unfolds six high-dimensional coordinate identities.
private theorem k4AggregateEEEERead_intertwines_internal
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d) :
    ((k4BAggregateCoordEquiv hn hc2)
        (k4EvenPAggregate hn hb2 (by omega) hd2 sigma).1,
      (k4WAggregateCoordEquiv hn hc2)
        (k4EvenPAggregate hn hb2 (by omega) hd2 sigma).2) =
      k4AggregateEEEERead
        (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma) := by
  simp only [k4AggregateEEEERead]
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact aggregateB00_eq_eeee hn hb2 hc2 hd2 sigma
      · exact aggregateB10_eq_eeee hn hb2 hc2 hd2 sigma
    · apply Subtype.ext
      funext t
      exact aggregateBZ_eq_eeee hn hb2 hc2 hd2 sigma t
  · apply Prod.ext
    · apply Prod.ext
      · exact aggregateWPoint_eq_eeee hn hb2 hc2 hd2 sigma
      · apply Subtype.ext
        exact aggregateW00_eq_eeee hn hb2 hc2 hd2 sigma
    · apply Subtype.ext
      funext t
      exact aggregateWZ_eq_eeee hn hb2 hc2 hd2 sigma t

theorem k4AggregateEEEERead_intertwines
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d) :
    k4AggregateEEEERead
        (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma) =
      ((k4BAggregateCoordEquiv hn hc2)
          (k4EvenPAggregate hn hb2 (by omega) hd2 sigma).1,
        (k4WAggregateCoordEquiv hn hc2)
          (k4EvenPAggregate hn hb2 (by omega) hd2 sigma).2) :=
  (k4AggregateEEEERead_intertwines_internal
    hn hb2 hc2 hd2 sigma).symm

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
