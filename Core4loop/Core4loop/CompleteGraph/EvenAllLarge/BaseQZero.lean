import Core4loop.CompleteGraph.CubeCompat.KappaCycle
import Core4loop.CompleteGraph.ScalarCycle.CycleCertificate
import Core4loop.CompleteGraph.EvenAllLarge.SameCCarrier
import Core4loop.CompleteGraph.DirectWitt.AddedBWPhase
import Core4loop.SquareDiagonal.DirectWitt.OddLiteralReindex
import Core4loop.SquareDiagonal.EvenP.CubeOrbit
import Core4loop.SquareDiagonal.CPhaseAdjoint

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.DirectWitt
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.ScalarCycle
open Core4loop.CompleteGraph.CubeCompat

noncomputable section

attribute [local instance] Fintype.ofFinite

private abbrev CubeIndex (n : Nat) := I n × I n × I n

private def pDiff {n : Nat} [NeZero n] (B : CyclicCube n) : CyclicCube n :=
  fun i j k => B i j k + B (i + 1) (j - 1) k

private def rDiff {n : Nat} [NeZero n] (W : CyclicCube n) : CyclicCube n :=
  fun i j k => W i j k + W i (j - 1) (k + 1)

private theorem cubePair_add_right
    {n : Nat} [NeZero n] (X Y Z : CyclicCube n) :
    cubePair X (Y + Z) = cubePair X Y + cubePair X Z := by
  unfold cubePair
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem cubePair_add_left
    {n : Nat} [NeZero n] (X Y Z : CyclicCube n) :
    cubePair (X + Y) Z = cubePair X Z + cubePair Y Z := by
  unfold cubePair
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem cubePair_eq_indexSum
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubePair X Y =
      ∑ q : CubeIndex n, X q.1 q.2.1 q.2.2 * Y q.1 q.2.1 q.2.2 := by
  unfold cubePair
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  calc
    (∑ y : I n, ∑ z : I n, ∑ x : I n,
        X x y z * Y x y z) =
        ∑ y : I n, ∑ x : I n, ∑ z : I n,
          X x y z * Y x y z := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = ∑ x : I n, ∑ y : I n, ∑ z : I n,
          X x y z * Y x y z := by
      rw [Finset.sum_comm]

private theorem kappa_eq_yzx
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappa B W =
      ∑ y : I n, ∑ z : I n, ∑ x : I n,
        (B x y z * W x y z +
          B (x + 1) y z * W x y (z + 1)) := by
  unfold k4CubeKappa
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  calc
    (∑ x : I n, ∑ y : I n, ∑ z : I n,
        (B x y z * W x y z +
          B (x + 1) y z * W x y (z + 1))) =
      ∑ y : I n, ∑ x : I n, ∑ z : I n,
        (B x y z * W x y z +
          B (x + 1) y z * W x y (z + 1)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]

private theorem cubePair_shiftP
    {n : Nat} [NeZero n] (C B : CyclicCube n) :
    cubePair C (pDiff B) =
      ∑ q : CubeIndex n,
        (C q.2.2 q.1 q.2.1 * B q.2.2 q.1 q.2.1 +
          C q.2.2 (q.1 + 1) q.2.1 * B (q.2.2 + 1) q.1 q.2.1) := by
  unfold cubePair
  simp only [pDiff]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib]
  congr 1
  let f : I n → F := fun j =>
    ∑ z : I n, ∑ i : I n,
      C i j z * B (i + 1) (j - 1) z
  have hs := sum_shift (n := n) (1 : I n) f
  simpa only [f, add_sub_cancel_right] using hs.symm

private theorem cubePair_shiftR
    {n : Nat} [NeZero n] (C W : CyclicCube n) :
    cubePair C (rDiff W) =
      ∑ q : CubeIndex n,
        (C q.2.2 q.1 q.2.1 * W q.2.2 q.1 q.2.1 +
          C q.2.2 (q.1 + 1) q.2.1 * W q.2.2 q.1 (q.2.1 + 1)) := by
  unfold cubePair
  simp only [rDiff]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib]
  congr 1
  let f : I n → F := fun j =>
    ∑ z : I n, ∑ i : I n,
      C i j z * W i (j - 1) (z + 1)
  have hs := sum_shift (n := n) (1 : I n) f
  simpa only [f, add_sub_cancel_right] using hs.symm

private theorem sum_B_square_step_zero
    {n : Nat} [NeZero n] (B : CyclicCube n) :
    (∑ y : I n, ∑ z : I n, ∑ x : I n,
      (B x y z * B x y z +
        B (x + 1) y z * B (x + 1) y z)) = 0 := by
  simp_rw [Finset.sum_add_distrib]
  have hs (y z : I n) :
      (∑ x : I n, B (x + 1) y z * B (x + 1) y z) =
        ∑ x : I n, B x y z * B x y z := by
    simpa only using
      (sum_shift (n := n) (1 : I n)
        (fun x => B x y z * B x y z))
  simp_rw [hs]
  simp only [F_add_self]

private theorem cycleQ_main_eq_kappa_add_pPair
    {n : Nat} [NeZero n] (B C W : CyclicCube n)
    (hcl : k4Closure B C W) :
    cubePair (B + C + W) (cyclicDiffX B) =
      k4CubeKappa B W + cubePair C (pDiff B) := by
  rw [kappa_eq_yzx, cubePair_shiftP]
  simp_rw [Fintype.sum_prod_type]
  unfold cubePair
  simp only [Pi.add_apply, cyclicDiffX]
  let M : I n → I n → I n → F := fun y z x =>
    (B x y z * W x y z +
      B (x + 1) y z * W x y (z + 1)) +
    (C x y z * B x y z +
      C x (y + 1) z * B (x + 1) y z)
  let Sq : I n → I n → I n → F := fun y z x =>
    B x y z * B x y z +
      B (x + 1) y z * B (x + 1) y z
  calc
    (∑ y : I n, ∑ z : I n, ∑ x : I n,
      (B x y z + C x y z + W x y z) *
        (B x y z + B (x + 1) y z)) =
      ∑ y : I n, ∑ z : I n, ∑ x : I n,
        (M y z x + Sq y z x) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x _
      have h := hcl x y z
      simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ] at h
      have hb1 :
          B (x + 1) y z =
            B x y z + C x y z + C x (y + 1) z +
              W x y z + W x y (z + 1) := by
        calc
          B (x + 1) y z = B (x + 1) y z + 0 := by rw [add_zero]
          _ = B (x + 1) y z +
              ((B x y z + B (x + 1) y z) +
                (C x y z + C x (y + 1) z) +
                (W x y z + W x y (z + 1))) := by rw [h]
          _ = _ := by
            ring_nf
            simp only [show (2 : F) = 0 by decide, mul_zero, zero_add]
      dsimp [M, Sq]
      rw [hb1]
      ring_nf
      simp only [show (2 : F) = 0 by decide, show (3 : F) = 1 by decide,
        show (4 : F) = 0 by decide, mul_zero, mul_one, add_zero]
    _ =
      (∑ y : I n, ∑ z : I n, ∑ x : I n, M y z x) +
      ∑ y : I n, ∑ z : I n, ∑ x : I n, Sq y z x := by
      simp only [Finset.sum_add_distrib]
    _ = ∑ y : I n, ∑ z : I n, ∑ x : I n, M y z x := by
      rw [show (∑ y : I n, ∑ z : I n, ∑ x : I n, Sq y z x) = 0 by
        simpa only [Sq] using sum_B_square_step_zero B]
      rw [add_zero]
    _ =
      (∑ y : I n, ∑ z : I n, ∑ x : I n,
        (B x y z * W x y z +
          B (x + 1) y z * W x y (z + 1))) +
      ∑ y : I n, ∑ z : I n, ∑ x : I n,
        (C x y z * B x y z +
          C x (y + 1) z * B (x + 1) y z) := by
      simp only [M, Finset.sum_add_distrib]

private theorem cycleQ_eq_kappa_add_sourcePair_of_closure
    {n : Nat} [NeZero n] (B C W : CyclicCube n)
    (hcl : k4Closure B C W) :
    cycleQ B C W =
      k4CubeKappa B W + cubePair C (pDiff B + rDiff W) := by
  unfold cycleQ
  rw [cycleQ_main_eq_kappa_add_pPair B C W hcl]
  have hK : cubeTyInvTzSum W = rDiff W := by
    rfl
  rw [hK, cubePair_add_right]
  abel

/-! Specialization to the literal K4 all-large Base slice. -/

noncomputable def k4BaseBCell
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d) :
    CyclicCube n :=
  diamondOddBGaugeEquiv hc hd B (zeroVec : PVec n 1) zt wt

noncomputable def k4BaseCCell
    {n b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (C : CFun4 n 1 b d) (yt : PVec n b) (wt : PVec n d) :
    CyclicCube n :=
  diamondOddCGaugeEquiv hb hd C (zeroVec : PVec n 1) yt wt

noncomputable def k4BaseWCell
    {n b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (W : WFun4 n 1 b c) (yt : PVec n b) (zt : PVec n c) :
    CyclicCube n :=
  diamondOddWGaugeEquiv hb hc W (zeroVec : PVec n 1) yt zt

private theorem vecSum_headTail_symm
    {n k : Nat} [NeZero n] (hk : 0 < k)
    (head : I n) (tail : PVec n k) :
    vecSum ((diamondOddVecHeadTailEquiv hk).symm (head, tail)) =
      head + vecSum tail := by
  cases k with
  | zero => omega
  | succ k => exact vecSum_vecCons head tail

private theorem sum_vec_headTail
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
        f (fun x => f ((diamondOddVecHeadTailEquiv hk).symm x)) ?_
      intro v
      exact congrArg f
        ((diamondOddVecHeadTailEquiv hk).symm_apply_apply v).symm
    _ = _ := by rw [Fintype.sum_prod_type]

private theorem sum_six_reorder
    {alpha beta gamma delta epsilon zeta : Type*}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    [Fintype delta] [Fintype epsilon] [Fintype zeta]
    (f : alpha → beta → gamma → delta → epsilon → zeta → F) :
    (∑ a : alpha, ∑ b : beta, ∑ c : gamma,
      ∑ d : delta, ∑ e : epsilon, ∑ z : zeta, f a b c d e z) =
      ∑ b : beta, ∑ d : delta, ∑ z : zeta,
        ∑ a : alpha, ∑ c : gamma, ∑ e : epsilon, f a b c d e z := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ a : alpha, ∑ c : gamma, ∑ d : delta,
      ∑ e : epsilon, ∑ z : zeta, f a b c d e z) =
        ∑ a : alpha, ∑ d : delta, ∑ c : gamma,
          ∑ e : epsilon, ∑ z : zeta, f a b c d e z := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ d : delta, ∑ a : alpha, ∑ c : gamma,
          ∑ e : epsilon, ∑ z : zeta, f a b c d e z := by
      rw [Finset.sum_comm]
    _ = ∑ d : delta, ∑ z : zeta, ∑ a : alpha,
          ∑ c : gamma, ∑ e : epsilon, f a b c d e z := by
      apply Finset.sum_congr rfl
      intro d _
      calc
        (∑ a : alpha, ∑ c : gamma, ∑ e : epsilon,
          ∑ z : zeta, f a b c d e z) =
            ∑ a : alpha, ∑ c : gamma, ∑ z : zeta,
              ∑ e : epsilon, f a b c d e z := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]
        _ = ∑ a : alpha, ∑ z : zeta, ∑ c : gamma,
              ∑ e : epsilon, f a b c d e z := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
        _ = ∑ z : zeta, ∑ a : alpha, ∑ c : gamma,
              ∑ e : epsilon, f a b c d e z := by
          rw [Finset.sum_comm]

private theorem bw_gauged_cube
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (W : WFun4 n 1 b c)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d) :
    (∑ i : I n, ∑ j : I n, ∑ k : I n,
      (diamondOddBPassiveCubeEquiv hc hd B (zeroVec : PVec n 1) zt wt
            (i + vecSum yt) j k *
          diamondOddWPassiveCubeEquiv hb hc W (zeroVec : PVec n 1) yt zt
            i j (k + vecSum wt) +
        diamondOddBPassiveCubeEquiv hc hd B (zeroVec : PVec n 1) zt wt
            (i + vecSum yt + 1) j k *
          diamondOddWPassiveCubeEquiv hb hc W (zeroVec : PVec n 1) yt zt
            i j (k + vecSum wt + 1))) =
      k4CubeKappa
        (k4BaseBCell hc hd B zt wt)
        (k4BaseWCell hb hc W yt zt) := by
  unfold k4CubeKappa k4BaseBCell k4BaseWCell
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

theorem k4BWSlice_eq_sum_cell_kappa
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (W : WFun4 n 1 b c) :
    k4BWSlice B W =
      ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        k4CubeKappa
          (k4BaseBCell hc hd B zt wt)
          (k4BaseWCell hb hc W yt zt) := by
  unfold k4BWSlice betaB gammaB xiW zetaW
  rw [sum_vec_headTail hb]
  simp_rw [sum_vec_headTail hc, sum_vec_headTail hd]
  rw [sum_six_reorder]
  apply Finset.sum_congr rfl
  intro yt _
  apply Finset.sum_congr rfl
  intro zt _
  apply Finset.sum_congr rfl
  intro wt _
  simp_rw [← diamondOddBPassiveCubeEquiv_apply,
    ← diamondOddWPassiveCubeEquiv_apply]
  simp_rw [vecSum_headTail_symm hb, vecSum_headTail_symm hd]
  exact bw_gauged_cube hb hc hd B W yt zt wt

private theorem k4Base_source_cell_sum_zero
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d)
    (yt : PVec n b) (wt : PVec n d) :
    (∑ zt : PVec n c,
      (pDiff (k4BaseBCell hc hd sigma.1.1 zt wt) +
        rDiff (k4BaseWCell hb hc sigma.1.2 yt zt))) = 0 := by
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
  simp only [Finset.sum_apply, Pi.add_apply, pDiff, rDiff,
    k4BaseBCell, k4BaseWCell,
    diamondOddBGaugeEquiv_apply, diamondOddWGaugeEquiv_apply,
    Pi.zero_apply]
  simpa only [add_assoc] using hp

private noncomputable def cubePairRightLinear
    {n : Nat} [NeZero n] (C : CyclicCube n) : CyclicCube n →ₗ[F] F where
  toFun X := cubePair C X
  map_add' X Y := cubePair_add_right C X Y
  map_smul' r X := by
    unfold cubePair
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro x _
    simp only [RingHom.id_apply]
    ring

@[simp] private theorem cubePairRightLinear_apply
    {n : Nat} [NeZero n] (C X : CyclicCube n) :
    cubePairRightLinear C X = cubePair C X := rfl

private theorem k4Base_sourcePair_sum_zt_zero
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d)
    (yt : PVec n b) (wt : PVec n d) :
    (∑ zt : PVec n c,
      cubePair (k4BaseCCell hb hd C yt wt)
        (pDiff (k4BaseBCell hc hd sigma.1.1 zt wt) +
          rDiff (k4BaseWCell hb hc sigma.1.2 yt zt))) = 0 := by
  change
    (∑ zt : PVec n c,
      cubePairRightLinear (k4BaseCCell hb hd C yt wt)
        (pDiff (k4BaseBCell hc hd sigma.1.1 zt wt) +
          rDiff (k4BaseWCell hb hc sigma.1.2 yt zt))) = 0
  rw [← map_sum]
  rw [k4Base_source_cell_sum_zero hb hc hd sigma yt wt]
  exact map_zero (cubePairRightLinear (k4BaseCCell hb hd C yt wt))

private theorem k4Base_sourcePair_total_zero
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    (∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
      cubePair (k4BaseCCell hb hd C yt wt)
        (pDiff (k4BaseBCell hc hd sigma.1.1 zt wt) +
          rDiff (k4BaseWCell hb hc sigma.1.2 yt zt))) = 0 := by
  apply Finset.sum_eq_zero
  intro yt _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro wt _
  exact k4Base_sourcePair_sum_zt_zero hb hc hd sigma C yt wt

def K4BaseCycleReduction
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) : Prop :=
  k4BWSlice sigma.1.1 sigma.1.2 =
    ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
      cycleQ
        (k4BaseBCell hc hd sigma.1.1 zt wt)
        (k4BaseCCell hb hd C yt wt)
        (k4BaseWCell hb hc sigma.1.2 yt zt)

theorem k4Base_cycleReduction_of_cell_closure
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d)
    (hcl : ∀ (yt : PVec n b) (zt : PVec n c) (wt : PVec n d),
      k4Closure
        (k4BaseBCell hc hd sigma.1.1 zt wt)
        (k4BaseCCell hb hd C yt wt)
        (k4BaseWCell hb hc sigma.1.2 yt zt)) :
    K4BaseCycleReduction hb hc hd sigma C := by
  unfold K4BaseCycleReduction
  rw [k4BWSlice_eq_sum_cell_kappa hb hc hd]
  symm
  calc
    (∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
      cycleQ
        (k4BaseBCell hc hd sigma.1.1 zt wt)
        (k4BaseCCell hb hd C yt wt)
        (k4BaseWCell hb hc sigma.1.2 yt zt)) =
      ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        (k4CubeKappa
            (k4BaseBCell hc hd sigma.1.1 zt wt)
            (k4BaseWCell hb hc sigma.1.2 yt zt) +
          cubePair (k4BaseCCell hb hd C yt wt)
            (pDiff (k4BaseBCell hc hd sigma.1.1 zt wt) +
              rDiff (k4BaseWCell hb hc sigma.1.2 yt zt))) := by
      apply Finset.sum_congr rfl
      intro yt _
      apply Finset.sum_congr rfl
      intro zt _
      apply Finset.sum_congr rfl
      intro wt _
      exact cycleQ_eq_kappa_add_sourcePair_of_closure _ _ _
        (hcl yt zt wt)
    _ =
      (∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        k4CubeKappa
          (k4BaseBCell hc hd sigma.1.1 zt wt)
          (k4BaseWCell hb hc sigma.1.2 yt zt)) +
      ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        cubePair (k4BaseCCell hb hd C yt wt)
          (pDiff (k4BaseBCell hc hd sigma.1.1 zt wt) +
            rDiff (k4BaseWCell hb hc sigma.1.2 yt zt)) := by
      simp only [Finset.sum_add_distrib]
    _ =
      ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        k4CubeKappa
          (k4BaseBCell hc hd sigma.1.1 zt wt)
          (k4BaseWCell hb hc sigma.1.2 yt zt) := by
      rw [k4Base_sourcePair_total_zero hb hc hd sigma C, add_zero]

/-! The already-compiled D-A-to-cell-closure bridge, repeated here so that
the independent artifact closes the actual kernel theorem end to end. -/

private theorem coeffApply_comm
    {iota : Type*} [Fintype iota] (f g : iota → F) :
    coeffApply f g = coeffApply g f := by
  unfold coeffApply
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem coeffApplyA_add_left
    {n b c d : Nat} [NeZero n]
    (f g : RootTarget n b c d) (A : AFun4 n b c d) :
    coeffApplyA (f + g) A = coeffApplyA f A + coeffApplyA g A := by
  rw [coeffApplyA_eq_sum, coeffApplyA_eq_sum, coeffApplyA_eq_sum]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem sqdiagRootCoeffApply_eq_coeffApplyA
    {n b c d : Nat} [NeZero n]
    (A R : RootTarget n b c d) :
    sqdiagRootCoeffApply A R = coeffApplyA R A := by
  unfold sqdiagRootCoeffApply
  rw [coeffApplyA_eq_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem k4Base_DA_iff_KCMap_eq_root
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    K4DACoeffEquation sigma C ↔
      KCMap (n := n) (a := 1) (b := b) (c := c) (d := d) C =
        KBMap (n := n) (a := 1) (b := b) (c := c) (d := d) sigma.1.1 +
        KWMap (n := n) (a := 1) (b := b) (c := c) (d := d) sigma.1.2 := by
  constructor
  · intro h
    let R : RootTarget n b c d :=
      KCMap (n := n) (a := 1) (b := b) (c := c) (d := d) C +
        (KBMap (n := n) (a := 1) (b := b) (c := c) (d := d) sigma.1.1 +
          KWMap (n := n) (a := 1) (b := b) (c := c) (d := d) sigma.1.2)
    have hR : R = 0 :=
      (sqdiagRootCoeffApply_forall_eq_zero_iff R).mp (by
        intro A
        have hA := h A
        rw [k4BaseCFunDotDual_apply, coeffApply_comm] at hA
        rw [coeffApply_diamondEvenPAConstraint_eq_coeffApplyA_KCMap] at hA
        change coeffApplyA
          (KCMap (n := n) (a := 1) (b := b) (c := c) (d := d) C) A =
          k4EvenPBaseRootScalar sigma A at hA
        unfold k4EvenPBaseRootScalar at hA
        rw [sqdiagRootCoeffApply_eq_coeffApplyA, coeffApplyA_add_left]
        rw [hA]
        exact F_add_self _)
    apply (add_eq_zero_iff_eq_of_F_module _ _).mp
    exact hR
  · intro h A
    rw [k4BaseCFunDotDual_apply, coeffApply_comm]
    rw [coeffApply_diamondEvenPAConstraint_eq_coeffApplyA_KCMap]
    unfold k4EvenPBaseRoot k4EvenPBaseRootScalar
    rw [h]
    rfl

@[simp] private theorem sum_PVec_one
    {n : Nat} [NeZero n] (f : PVec n 1 → F) :
    (∑ p : PVec n 1, f p) = f (zeroVec : PVec n 1) := by
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro p _ hp
    exact False.elim (hp (pVec_one_eq_zeroVec p))
  · simp

theorem k4Base_DA_gives_cell_closure
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d)
    (hDA : K4DACoeffEquation sigma C)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d) :
    k4Closure
      (k4BaseBCell hc hd sigma.1.1 zt wt)
      (k4BaseCCell hb hd C yt wt)
      (k4BaseWCell hb hc sigma.1.2 yt zt) := by
  have hroot := (k4Base_DA_iff_KCMap_eq_root sigma C).mp hDA
  intro i j k
  have hp := congrFun (congrFun (congrFun hroot
    ((diamondOddVecHeadTailEquiv hb).symm (i - vecSum yt, yt)))
    ((diamondOddVecHeadTailEquiv hc).symm (j - vecSum zt, zt)))
    ((diamondOddVecHeadTailEquiv hd).symm (k - vecSum wt, wt))
  change
    (∑ p : PVec n 1,
      (C p
          ((diamondOddVecHeadTailEquiv hb).symm (i - vecSum yt, yt))
          (vecSum ((diamondOddVecHeadTailEquiv hc).symm
            (j - vecSum zt, zt)))
          ((diamondOddVecHeadTailEquiv hd).symm (k - vecSum wt, wt)) +
        C p
          ((diamondOddVecHeadTailEquiv hb).symm (i - vecSum yt, yt))
          (vecSum ((diamondOddVecHeadTailEquiv hc).symm
            (j - vecSum zt, zt)) + 1)
          ((diamondOddVecHeadTailEquiv hd).symm (k - vecSum wt, wt)))) =
      (∑ p : PVec n 1,
        (sigma.1.1 p
            (vecSum ((diamondOddVecHeadTailEquiv hb).symm
              (i - vecSum yt, yt)))
            ((diamondOddVecHeadTailEquiv hc).symm (j - vecSum zt, zt))
            ((diamondOddVecHeadTailEquiv hd).symm (k - vecSum wt, wt)) +
          sigma.1.1 p
            (vecSum ((diamondOddVecHeadTailEquiv hb).symm
              (i - vecSum yt, yt)) + 1)
            ((diamondOddVecHeadTailEquiv hc).symm (j - vecSum zt, zt))
            ((diamondOddVecHeadTailEquiv hd).symm (k - vecSum wt, wt)))) +
      (∑ p : PVec n 1,
        (sigma.1.2 p
            ((diamondOddVecHeadTailEquiv hb).symm (i - vecSum yt, yt))
            ((diamondOddVecHeadTailEquiv hc).symm (j - vecSum zt, zt))
            (vecSum ((diamondOddVecHeadTailEquiv hd).symm
              (k - vecSum wt, wt))) +
          sigma.1.2 p
            ((diamondOddVecHeadTailEquiv hb).symm (i - vecSum yt, yt))
            ((diamondOddVecHeadTailEquiv hc).symm (j - vecSum zt, zt))
            (vecSum ((diamondOddVecHeadTailEquiv hd).symm
              (k - vecSum wt, wt)) + 1))) at hp
  unfold k4BaseBCell k4BaseCCell k4BaseWCell
  unfold cyclicDiffX cyclicDiffY cyclicDiffZ
  simp only [diamondOddBGaugeEquiv_apply, diamondOddCGaugeEquiv_apply,
    diamondOddWGaugeEquiv_apply, diamondOddBPassiveCubeEquiv_apply,
    diamondOddCPassiveCubeEquiv_apply,
    diamondOddWPassiveCubeEquiv_apply]
  simp only [sum_PVec_one, vecSum_headTail_symm] at hp
  simp only [sub_add_cancel] at hp
  let bval : F :=
    sigma.1.1 zeroVec i
        ((diamondOddVecHeadTailEquiv hc).symm (j - vecSum zt, zt))
        ((diamondOddVecHeadTailEquiv hd).symm (k - vecSum wt, wt)) +
      sigma.1.1 zeroVec (i + 1)
        ((diamondOddVecHeadTailEquiv hc).symm (j - vecSum zt, zt))
        ((diamondOddVecHeadTailEquiv hd).symm (k - vecSum wt, wt))
  let cval : F :=
    C zeroVec
        ((diamondOddVecHeadTailEquiv hb).symm (i - vecSum yt, yt)) j
        ((diamondOddVecHeadTailEquiv hd).symm (k - vecSum wt, wt)) +
      C zeroVec
        ((diamondOddVecHeadTailEquiv hb).symm (i - vecSum yt, yt)) (j + 1)
        ((diamondOddVecHeadTailEquiv hd).symm (k - vecSum wt, wt))
  let wval : F :=
    sigma.1.2 zeroVec
        ((diamondOddVecHeadTailEquiv hb).symm (i - vecSum yt, yt))
        ((diamondOddVecHeadTailEquiv hc).symm (j - vecSum zt, zt)) k +
      sigma.1.2 zeroVec
        ((diamondOddVecHeadTailEquiv hb).symm (i - vecSum yt, yt))
        ((diamondOddVecHeadTailEquiv hc).symm (j - vecSum zt, zt)) (k + 1)
  change bval + cval + wval = 0
  have hpval : cval = bval + wval := by exact hp
  calc
    bval + cval + wval = cval + (bval + wval) := by abel
    _ = cval + cval := by rw [← hpval]
    _ = 0 := F_add_self _

theorem k4Base_cycleReduction
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d)
    (hsame : K4BaseSameCIndexed sigma C) :
    K4BaseCycleReduction hb hc hd sigma C := by
  apply k4Base_cycleReduction_of_cell_closure hb hc hd sigma C
  intro yt zt wt
  exact k4Base_DA_gives_cell_closure hb hc hd sigma C hsame.1 yt zt wt

theorem k4EvenPBase_qzero_on_ker
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : K4EvenPLeft n b c d)
    (hsigma : sigma ∈ LinearMap.ker
      (k4EvenPBaseCross (n := n) (b := b) (c := c) (d := d))) :
    k4BWSlice sigma.1.1 sigma.1.2 = 0 := by
  rcases (k4Base_exists_sameCIndexed_iff_mem_ker_baseCross sigma).mpr hsigma with
    ⟨C, hsame⟩
  rw [k4Base_cycleReduction hb hc hd sigma C hsame]
  apply Finset.sum_eq_zero
  intro yt _
  apply Finset.sum_eq_zero
  intro zt _
  apply Finset.sum_eq_zero
  intro wt _
  exact cycleQ_zero_of_closure hn2 _ _ _
    (k4Base_DA_gives_cell_closure hb hc hd sigma C hsame.1 yt zt wt)

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
