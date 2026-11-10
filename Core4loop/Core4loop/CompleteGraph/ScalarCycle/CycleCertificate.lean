import Core4loop.ZeroSumSpaces.ExplicitCyclicPrefix

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.ScalarCycle

noncomputable section

abbrev K4Cube (n : ℕ) := CyclicCube n
private abbrev K4Cycle (n : ℕ) := K4Cube n × K4Cube n × K4Cube n

def cubeBackwardDiffX {n : ℕ} [NeZero n] (f : K4Cube n) : K4Cube n :=
  fun x y z => f x y z + f (x - 1) y z

def cubeBackwardDiffY {n : ℕ} [NeZero n] (f : K4Cube n) : K4Cube n :=
  fun x y z => f x y z + f x (y - 1) z

def cubeTyInvTzSum {n : ℕ} [NeZero n] (f : K4Cube n) : K4Cube n :=
  fun x y z => f x y z + f x (y - 1) (z + 1)

def k4SingletonRootRelation {n : ℕ} [NeZero n]
    (B W Z : K4Cube n) : Prop :=
  ∀ x y z, cyclicDiffX B x y z = cyclicDiffZ W x y z + Z x y z

def k4SingletonCompatRelation {n : ℕ} [NeZero n]
    (A B W : K4Cube n) : Prop :=
  ∀ x y z,
    B x y z + B (x + 1) (y - 1) z +
        W x y z + W x (y - 1) (z + 1) +
        cubeBackwardDiffY A x y z = 0

def k4SingletonDualBRelation {n : ℕ} [NeZero n]
    (R C W : K4Cube n) : Prop :=
  ∀ x y z,
    cubeBackwardDiffX R x y z +
        (C x y z + C (x - 1) (y + 1) z) +
        (W x y z + W (x - 1) y (z + 1)) = 0

def k4SingletonDualZRelation {n : ℕ} [NeZero n]
    (C Z : K4Cube n) : Prop :=
  ∀ x y z, cyclicDiffY C x y z = Z x y z

def k4SingletonZSumRelation {n : ℕ} [NeZero n] (Z : K4Cube n) : Prop :=
  ∀ x z, (∑ y : I n, Z x y z) = 0

def k4Closure {n : ℕ} [NeZero n] (B C W : K4Cube n) : Prop :=
  ∀ x y z,
    cyclicDiffX B x y z + cyclicDiffY C x y z +
      cyclicDiffZ W x y z = 0

noncomputable def cubePair {n : ℕ} [NeZero n]
    (f g : K4Cube n) : F :=
  ∑ y : I n, ∑ z : I n, ∑ x : I n, f x y z * g x y z

noncomputable def cycleQ {n : ℕ} [NeZero n]
    (B C W : K4Cube n) : F :=
  cubePair (B + C + W) (cyclicDiffX B) +
    cubePair C (cubeTyInvTzSum W)

noncomputable def k4SingletonDefect {n : ℕ} [NeZero n]
    (R C W : K4Cube n) : F :=
  cubePair R (cyclicDiffZ W) + cubePair R (cyclicDiffY C) +
    cubePair C (cubeTyInvTzSum W)

private theorem F_eq_of_add_eq_zero {a b : F} (h : a + b = 0) :
    a = b := by
  calc
    a = a + 0 := by rw [add_zero]
    _ = a + (b + b) := by rw [F_add_self]
    _ = (a + b) + b := by abel
    _ = b := by rw [h, zero_add]

private theorem relations_imply_closure
    {n : ℕ} [NeZero n] (_hn : 2 ≤ n)
    (B C W Z : K4Cube n)
    (hroot : k4SingletonRootRelation B W Z)
    (hdualZ : k4SingletonDualZRelation C Z) :
    k4Closure B C W := by
  dsimp [k4SingletonRootRelation] at hroot
  dsimp [k4SingletonDualZRelation] at hdualZ
  intro x y z
  have hr := hroot x y z
  have hz := hdualZ x y z
  simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ] at hr hz ⊢
  rw [hr, hz]
  calc
    (W x y z + W x y (z + 1) + Z x y z) + Z x y z +
          (W x y z + W x y (z + 1)) =
        (W x y z + W x y z) +
          (W x y (z + 1) + W x y (z + 1)) +
          (Z x y z + Z x y z) := by abel
    _ = 0 := by simp only [F_add_self, zero_add]

private theorem dualB_imply_R_gauge
    {n : ℕ} [NeZero n] (_hn : 2 ≤ n)
    (R B C W : K4Cube n)
    (hclosure : k4Closure B C W)
    (hdualB : k4SingletonDualBRelation R C W) :
    let v := fun y z =>
      R 0 y z + B 0 y z + C 0 y z + W 0 y z
    ∀ x y z,
      R x y z = B x y z + C x y z + W x y z + v y z := by
  let S : K4Cube n := fun x y z =>
    R x y z + B x y z + C x y z + W x y z
  have hstep : ∀ x y z, S (x + 1) y z = S x y z := by
    intro x y z
    have hd := hdualB (x + 1) y z
    have hc := hclosure x y z
    have hx : x + 1 - 1 = x := by abel
    simp only [cubeBackwardDiffX] at hd
    simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ] at hc
    rw [hx] at hd
    have hsum : S (x + 1) y z + S x y z = 0 := by
      dsimp [S]
      calc
        (R (x + 1) y z + B (x + 1) y z +
              C (x + 1) y z + W (x + 1) y z) +
            (R x y z + B x y z + C x y z + W x y z) =
            (R (x + 1) y z + R x y z +
                (C (x + 1) y z + C x (y + 1) z) +
                (W (x + 1) y z + W x y (z + 1))) +
              (B x y z + B (x + 1) y z +
                (C x y z + C x (y + 1) z) +
                (W x y z + W x y (z + 1))) := by
                  ring_nf
                  simp only [show (2 : F) = 0 by decide, mul_zero,
                    add_zero]
        _ = 0 := by rw [hd, hc, zero_add]
    exact F_eq_of_add_eq_zero hsum
  dsimp
  intro x y z
  have hconst : S x y z = S 0 y z :=
    zmod_step_const (fun t => S t y z) (fun t => hstep t y z) x
  dsimp [S] at hconst
  let T : F := B x y z + C x y z + W x y z
  calc
    R x y z = R x y z + 0 := by rw [add_zero]
    _ = R x y z + (T + T) := by rw [F_add_self]
    _ = (R x y z + B x y z + C x y z + W x y z) + T := by
      dsimp [T]
      abel
    _ = (R 0 y z + B 0 y z + C 0 y z + W 0 y z) + T := by
      rw [hconst]
    _ = B x y z + C x y z + W x y z +
          (R 0 y z + B 0 y z + C 0 y z + W 0 y z) := by
      dsimp [T]
      abel

private theorem cubePair_xConstant_cyclicDiffX
    {n : ℕ} [NeZero n] (v : I n → I n → F) (B : K4Cube n) :
    cubePair (fun _ y z => v y z) (cyclicDiffX B) = 0 := by
  classical
  unfold cubePair
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro z _
  calc
    (∑ x : I n, v y z * cyclicDiffX B x y z) =
        v y z * ((∑ x : I n, B x y z) +
          ∑ x : I n, B (x + 1) y z) := by
      simp only [cyclicDiffX, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
    _ = v y z * ((∑ x : I n, B x y z) +
          ∑ x : I n, B x y z) := by
      rw [sum_shift (n := n) (1 : I n) (fun x => B x y z)]
    _ = 0 := by rw [F_add_self, mul_zero]

private theorem defect_eq_cycleQ
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (R B C W Z : K4Cube n)
    (hroot : k4SingletonRootRelation B W Z)
    (hdualB : k4SingletonDualBRelation R C W)
    (hdualZ : k4SingletonDualZRelation C Z) :
    k4SingletonDefect R C W = cycleQ B C W := by
  have hcl := relations_imply_closure hn B C W Z hroot hdualZ
  have hgauge := dualB_imply_R_gauge hn R B C W hcl hdualB
  let v : I n → I n → F := fun y z =>
    R 0 y z + B 0 y z + C 0 y z + W 0 y z
  have hg : ∀ x y z,
      R x y z = B x y z + C x y z + W x y z + v y z := hgauge
  have hdx : ∀ x y z,
      cyclicDiffZ W x y z + cyclicDiffY C x y z =
        cyclicDiffX B x y z := by
    intro x y z
    apply F_eq_of_add_eq_zero
    simpa only [add_assoc, add_comm, add_left_comm] using hcl x y z
  have hfirst :
      cubePair R (cyclicDiffZ W) + cubePair R (cyclicDiffY C) =
        cubePair R (cyclicDiffX B) := by
    unfold cubePair
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [← mul_add, hdx]
  have hsplit :
      cubePair R (cyclicDiffX B) =
        cubePair (B + C + W) (cyclicDiffX B) +
          cubePair (fun _ y z => v y z) (cyclicDiffX B) := by
    unfold cubePair
    simp_rw [hg]
    simp only [Pi.add_apply]
    simp_rw [add_mul, Finset.sum_add_distrib]
  rw [k4SingletonDefect, hfirst, hsplit,
    cubePair_xConstant_cyclicDiffX]
  simp [cycleQ]

private def curlXY {n : ℕ} [NeZero n] (phi : K4Cube n) : K4Cycle n :=
  (cyclicDiffY phi, cyclicDiffX phi, 0)

private def curlXZ {n : ℕ} [NeZero n] (phi : K4Cube n) : K4Cycle n :=
  (cyclicDiffZ phi, 0, cyclicDiffX phi)

private def curlYZ {n : ℕ} [NeZero n] (phi : K4Cube n) : K4Cycle n :=
  (0, cyclicDiffZ phi, cyclicDiffY phi)

/-- All fields in the explicit all-n cycle decomposition.  Every intermediate
below is a local formula, so there is no second whole-source representation. -/
private structure K4ExplicitCycleData (n : ℕ) [NeZero n] where
  xy : K4Cube n
  xz : K4Cube n
  yz : K4Cube n
  ax : F
  ay : F
  az : F

private noncomputable def explicitCycleData
    {n : ℕ} [NeZero n] (B C W : K4Cube n) :
    K4ExplicitCycleData n := by
  let cBar : I n → I n → F := fun y z => ∑ x : I n, C x y z
  let wBar : I n → I n → F := fun y z => ∑ x : I n, W x y z
  let ay : F := ∑ z : I n, cBar 0 z
  let az : F := ∑ y : I n, wBar y 0
  let c0 : K4Cube n := fun x y z =>
    C x y z + ay * if x = 0 ∧ z = 0 then 1 else 0
  let w0 : K4Cube n := fun x y z =>
    W x y z + az * if x = 0 ∧ y = 0 then 1 else 0
  let c0Bar : I n → I n → F := fun y z => ∑ x : I n, c0 x y z
  let w0Bar : I n → I n → F := fun y z => ∑ x : I n, w0 x y z
  let psi : I n → I n → F := fun y z =>
    explicitCyclicPrefix (fun r => w0Bar r 0) y +
      explicitCyclicPrefix (fun s => c0Bar y s) z
  let phiYZ : K4Cube n := fun x y z => if x = 0 then psi y z else 0
  let c1 : K4Cube n := fun x y z =>
    c0 x y z + cyclicDiffZ phiYZ x y z
  let w1 : K4Cube n := fun x y z =>
    w0 x y z + cyclicDiffY phiYZ x y z
  let phiXY0 : K4Cube n := fun x y z =>
    explicitCyclicPrefix (fun t => c1 t y z) x
  let phiXZ0 : K4Cube n := fun x y z =>
    explicitCyclicPrefix (fun t => w1 t y z) x
  let b2 : K4Cube n := fun x y z =>
    B x y z + cyclicDiffY phiXY0 x y z +
      cyclicDiffZ phiXZ0 x y z
  let g : I n → I n → F := fun y z => b2 0 y z
  let ax : F := ∑ y : I n, ∑ z : I n, g y z
  let delta : I n → I n → F := fun y z =>
    if y = 0 ∧ z = 0 then 1 else 0
  let g0 : I n → I n → F := fun y z => g y z + ax * delta y z
  let row : I n → F := fun y => ∑ z : I n, g0 y z
  let u0 : I n → F := fun y => explicitCyclicPrefix row y
  let u : I n → I n → F := fun y z => if z = 0 then u0 y else 0
  let g1 : I n → I n → F := fun y z =>
    g0 y z + u y z + u (y + 1) z
  let v : I n → I n → F := fun y z =>
    explicitCyclicPrefix (g1 y) z
  exact
    { xy := fun x y z => phiXY0 x y z + u y z
      xz := fun x y z => phiXZ0 x y z + v y z
      yz := phiYZ
      ax := ax
      ay := ay
      az := az }

private noncomputable def explicitXY
    {n : ℕ} [NeZero n] (B C W : K4Cube n) : K4Cube n :=
  (explicitCycleData B C W).xy

private noncomputable def explicitXZ
    {n : ℕ} [NeZero n] (B C W : K4Cube n) : K4Cube n :=
  (explicitCycleData B C W).xz

private noncomputable def explicitYZ
    {n : ℕ} [NeZero n] (B C W : K4Cube n) : K4Cube n :=
  (explicitCycleData B C W).yz

private theorem xsum_closure
    {n : ℕ} [NeZero n] (B C W : K4Cube n)
    (hcl : k4Closure B C W) :
    ∀ y z,
      ((∑ x : I n, C x y z) + ∑ x : I n, C x (y + 1) z) +
        ((∑ x : I n, W x y z) + ∑ x : I n, W x y (z + 1)) = 0 := by
  classical
  intro y z
  have hs :
      (∑ x : I n,
        (cyclicDiffX B x y z + cyclicDiffY C x y z +
          cyclicDiffZ W x y z)) = 0 := by
    calc
      (∑ x : I n,
        (cyclicDiffX B x y z + cyclicDiffY C x y z +
          cyclicDiffZ W x y z)) = ∑ _x : I n, 0 := by
        apply Finset.sum_congr rfl
        intro x _
        exact hcl x y z
      _ = 0 := by simp
  simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ,
    Finset.sum_add_distrib] at hs
  have hB :
      (∑ x : I n, B x y z) + ∑ x : I n, B (x + 1) y z = 0 := by
    rw [sum_shift (n := n) (1 : I n) (fun x => B x y z)]
    exact F_add_self _
  rw [hB, zero_add] at hs
  exact hs

private theorem transverse_sums_and_closure
    {n : ℕ} [NeZero n] (B C W : K4Cube n)
    (hcl : k4Closure B C W) :
    let cBar : I n → I n → F := fun y z => ∑ x : I n, C x y z
    let wBar : I n → I n → F := fun y z => ∑ x : I n, W x y z
    let ay : F := ∑ z : I n, cBar 0 z
    let az : F := ∑ y : I n, wBar y 0
    let c0 : K4Cube n := fun x y z =>
      C x y z + ay * if x = 0 ∧ z = 0 then 1 else 0
    let w0 : K4Cube n := fun x y z =>
      W x y z + az * if x = 0 ∧ y = 0 then 1 else 0
    let c0Bar : I n → I n → F := fun y z => ∑ x : I n, c0 x y z
    let w0Bar : I n → I n → F := fun y z => ∑ x : I n, w0 x y z
    (∀ y, (∑ z : I n, c0Bar y z) = 0) ∧
      (∀ z, (∑ y : I n, w0Bar y z) = 0) ∧
      (∀ y z,
        c0Bar y z + c0Bar (y + 1) z +
          (w0Bar y z + w0Bar y (z + 1)) = 0) := by
  classical
  dsimp
  let cBar : I n → I n → F := fun y z => ∑ x : I n, C x y z
  let wBar : I n → I n → F := fun y z => ∑ x : I n, W x y z
  let ay : F := ∑ z : I n, cBar 0 z
  let az : F := ∑ y : I n, wBar y 0
  let c0 : K4Cube n := fun x y z =>
    C x y z + ay * if x = 0 ∧ z = 0 then 1 else 0
  let w0 : K4Cube n := fun x y z =>
    W x y z + az * if x = 0 ∧ y = 0 then 1 else 0
  let c0Bar : I n → I n → F := fun y z => ∑ x : I n, c0 x y z
  let w0Bar : I n → I n → F := fun y z => ∑ x : I n, w0 x y z
  have hbar : ∀ y z,
      cBar y z + cBar (y + 1) z +
        (wBar y z + wBar y (z + 1)) = 0 := by
    simpa [cBar, wBar, add_assoc] using xsum_closure B C W hcl
  have hrowStep : ∀ y,
      (∑ z : I n, cBar (y + 1) z) = ∑ z : I n, cBar y z := by
    intro y
    have hs : (∑ z : I n,
        (cBar y z + cBar (y + 1) z +
          (wBar y z + wBar y (z + 1)))) = 0 := by
      calc
        (∑ z : I n,
          (cBar y z + cBar (y + 1) z +
            (wBar y z + wBar y (z + 1)))) = ∑ _z : I n, 0 := by
          apply Finset.sum_congr rfl
          intro z _
          exact hbar y z
        _ = 0 := by simp
    simp only [Finset.sum_add_distrib] at hs
    have hw :
        (∑ z : I n, wBar y z) +
          (∑ z : I n, wBar y (z + 1)) = 0 := by
      rw [sum_shift (n := n) (1 : I n) (wBar y)]
      exact F_add_self _
    rw [hw, add_zero] at hs
    exact (F_eq_of_add_eq_zero hs).symm
  have hrow : ∀ y, (∑ z : I n, cBar y z) = ay := by
    intro y
    exact zmod_step_const
      (fun t => ∑ z : I n, cBar t z) hrowStep y
  have hcolStep : ∀ z,
      (∑ y : I n, wBar y (z + 1)) = ∑ y : I n, wBar y z := by
    intro z
    have hs : (∑ y : I n,
        (cBar y z + cBar (y + 1) z +
          (wBar y z + wBar y (z + 1)))) = 0 := by
      calc
        (∑ y : I n,
          (cBar y z + cBar (y + 1) z +
            (wBar y z + wBar y (z + 1)))) = ∑ _y : I n, 0 := by
          apply Finset.sum_congr rfl
          intro y _
          exact hbar y z
        _ = 0 := by simp
    simp only [Finset.sum_add_distrib] at hs
    have hc :
        (∑ y : I n, cBar y z) +
          (∑ y : I n, cBar (y + 1) z) = 0 := by
      rw [sum_shift (n := n) (1 : I n) (fun y => cBar y z)]
      exact F_add_self _
    rw [hc, zero_add] at hs
    exact (F_eq_of_add_eq_zero hs).symm
  have hcol : ∀ z, (∑ y : I n, wBar y z) = az := by
    intro z
    exact zmod_step_const
      (fun t => ∑ y : I n, wBar y t) hcolStep z
  have hdelta (a : F) :
      (∑ x : I n, if x = 0 then a else 0) = a := by
    rw [Finset.sum_eq_single (0 : I n)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hc0 : ∀ y z,
      c0Bar y z = cBar y z + ay * (if z = 0 then 1 else 0) := by
    intro y z
    by_cases hz : z = 0
    · subst z
      simp only [c0Bar, c0, cBar, and_true, mul_ite, mul_one,
        mul_zero, Finset.sum_add_distrib]
      rw [hdelta]
      simp
    · simp only [c0Bar, c0, cBar, hz, and_false, if_false,
        mul_zero, add_zero]
  have hw0 : ∀ y z,
      w0Bar y z = wBar y z + az * (if y = 0 then 1 else 0) := by
    intro y z
    by_cases hy : y = 0
    · subst y
      simp only [w0Bar, w0, wBar, and_true, mul_ite, mul_one,
        mul_zero, Finset.sum_add_distrib]
      rw [hdelta]
      simp
    · simp only [w0Bar, w0, wBar, hy, and_false, if_false,
        mul_zero, add_zero]
  change
    (∀ y, (∑ z : I n, c0Bar y z) = 0) ∧
      (∀ z, (∑ y : I n, w0Bar y z) = 0) ∧
      (∀ y z,
        c0Bar y z + c0Bar (y + 1) z +
          (w0Bar y z + w0Bar y (z + 1)) = 0)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    simp_rw [hc0]
    rw [Finset.sum_add_distrib, hrow]
    rw [← Finset.mul_sum]
    have hdeltaOne :
        (∑ z : I n, if z = 0 then (1 : F) else 0) = 1 :=
      hdelta 1
    rw [hdeltaOne]
    simp only [mul_one, F_add_self]
  · intro z
    simp_rw [hw0]
    rw [Finset.sum_add_distrib, hcol]
    rw [← Finset.mul_sum]
    have hdeltaOne :
        (∑ y : I n, if y = 0 then (1 : F) else 0) = 1 :=
      hdelta 1
    rw [hdeltaOne]
    simp only [mul_one, F_add_self]
  · intro y z
    rw [hc0, hc0, hw0, hw0]
    have hb := hbar y z
    ring_nf at hb ⊢
    simp only [show (2 : F) = 0 by decide, mul_zero, add_zero] at hb ⊢
    exact hb

private theorem correlated_potential_diffs
    {n : ℕ} [NeZero n] (B C W : K4Cube n)
    (hcl : k4Closure B C W) :
    let cBar : I n → I n → F := fun y z => ∑ x : I n, C x y z
    let wBar : I n → I n → F := fun y z => ∑ x : I n, W x y z
    let ay : F := ∑ z : I n, cBar 0 z
    let az : F := ∑ y : I n, wBar y 0
    let c0 : K4Cube n := fun x y z =>
      C x y z + ay * if x = 0 ∧ z = 0 then 1 else 0
    let w0 : K4Cube n := fun x y z =>
      W x y z + az * if x = 0 ∧ y = 0 then 1 else 0
    let c0Bar : I n → I n → F := fun y z => ∑ x : I n, c0 x y z
    let w0Bar : I n → I n → F := fun y z => ∑ x : I n, w0 x y z
    let psi : I n → I n → F := fun y z =>
      explicitCyclicPrefix (fun r => w0Bar r 0) y +
        explicitCyclicPrefix (fun s => c0Bar y s) z
    (∀ y z, psi y z + psi y (z + 1) = c0Bar y z) ∧
      (∀ y z, psi y z + psi (y + 1) z = w0Bar y z) := by
  classical
  dsimp
  let cBar : I n → I n → F := fun y z => ∑ x : I n, C x y z
  let wBar : I n → I n → F := fun y z => ∑ x : I n, W x y z
  let ay : F := ∑ z : I n, cBar 0 z
  let az : F := ∑ y : I n, wBar y 0
  let c0 : K4Cube n := fun x y z =>
    C x y z + ay * if x = 0 ∧ z = 0 then 1 else 0
  let w0 : K4Cube n := fun x y z =>
    W x y z + az * if x = 0 ∧ y = 0 then 1 else 0
  let c0Bar : I n → I n → F := fun y z => ∑ x : I n, c0 x y z
  let w0Bar : I n → I n → F := fun y z => ∑ x : I n, w0 x y z
  let psi : I n → I n → F := fun y z =>
    explicitCyclicPrefix (fun r => w0Bar r 0) y +
      explicitCyclicPrefix (fun s => c0Bar y s) z
  have ht := transverse_sums_and_closure B C W hcl
  change
    (∀ y, (∑ z : I n, c0Bar y z) = 0) ∧
      (∀ z, (∑ y : I n, w0Bar y z) = 0) ∧
      (∀ y z,
        c0Bar y z + c0Bar (y + 1) z +
          (w0Bar y z + w0Bar y (z + 1)) = 0) at ht
  rcases ht with ⟨hcSum, hwSum, htwo⟩
  have hprefixC : ∀ y z,
      explicitCyclicPrefix (fun s => c0Bar y s) z +
        explicitCyclicPrefix (fun s => c0Bar y s) (z + 1) =
          c0Bar y z := by
    intro y z
    let u : ZeroSumProfile n :=
      ⟨fun s => c0Bar y s, LinearMap.mem_ker.mpr (hcSum y)⟩
    exact congrFun (cycDiff_explicitCyclicPrimitive u) z
  have hprefixW : ∀ y,
      explicitCyclicPrefix (fun r => w0Bar r 0) y +
        explicitCyclicPrefix (fun r => w0Bar r 0) (y + 1) =
          w0Bar y 0 := by
    intro y
    let u : ZeroSumProfile n :=
      ⟨fun r => w0Bar r 0, LinearMap.mem_ker.mpr (hwSum 0)⟩
    exact congrFun (cycDiff_explicitCyclicPrimitive u) y
  have prefix_add (f g : Profile n) (t : I n) :
      explicitCyclicPrefix f t + explicitCyclicPrefix g t =
        explicitCyclicPrefix (f + g) t := by
    unfold explicitCyclicPrefix finPrefix
    rw [← Finset.sum_add_distrib]
    rfl
  change
    (∀ y z, psi y z + psi y (z + 1) = c0Bar y z) ∧
      (∀ y z, psi y z + psi (y + 1) z = w0Bar y z)
  refine ⟨?_, ?_⟩
  · intro y z
    dsimp [psi]
    calc
      explicitCyclicPrefix (fun r => w0Bar r 0) y +
            explicitCyclicPrefix (fun s => c0Bar y s) z +
          (explicitCyclicPrefix (fun r => w0Bar r 0) y +
            explicitCyclicPrefix (fun s => c0Bar y s) (z + 1)) =
          (explicitCyclicPrefix (fun r => w0Bar r 0) y +
              explicitCyclicPrefix (fun r => w0Bar r 0) y) +
            (explicitCyclicPrefix (fun s => c0Bar y s) z +
              explicitCyclicPrefix (fun s => c0Bar y s) (z + 1)) := by abel
      _ = c0Bar y z := by rw [F_add_self, zero_add, hprefixC]
  · intro y z
    dsimp [psi]
    have hd :
        ((fun s => c0Bar y s) + fun s => c0Bar (y + 1) s) =
          cycDiff (n := n) F (fun s => w0Bar y s) := by
      funext s
      simp only [Pi.add_apply, cycDiff_apply]
      apply F_eq_of_add_eq_zero
      exact htwo y s
    calc
      explicitCyclicPrefix (fun r => w0Bar r 0) y +
            explicitCyclicPrefix (fun s => c0Bar y s) z +
          (explicitCyclicPrefix (fun r => w0Bar r 0) (y + 1) +
            explicitCyclicPrefix (fun s => c0Bar (y + 1) s) z) =
          (explicitCyclicPrefix (fun r => w0Bar r 0) y +
              explicitCyclicPrefix (fun r => w0Bar r 0) (y + 1)) +
            (explicitCyclicPrefix (fun s => c0Bar y s) z +
              explicitCyclicPrefix (fun s => c0Bar (y + 1) s) z) := by abel
      _ = w0Bar y 0 +
          explicitCyclicPrefix
            ((fun s => c0Bar y s) + fun s => c0Bar (y + 1) s) z := by
        rw [hprefixW, prefix_add]
      _ = w0Bar y 0 +
          explicitCyclicPrefix
            (cycDiff (n := n) F (fun s => w0Bar y s)) z := by rw [hd]
      _ = w0Bar y 0 + (w0Bar y 0 + w0Bar y z) := by
        rw [explicitCyclicPrefix_cycDiff_apply]
      _ = w0Bar y z := by rw [← add_assoc, F_add_self, zero_add]

private theorem cycle_decompose_explicit
    {n : ℕ} [NeZero n] (_hn : 2 ≤ n)
    (B C W : K4Cube n) (hcl : k4Closure B C W) :
    (B, C, W) =
      curlXY (explicitXY B C W) +
      curlXZ (explicitXZ B C W) +
      curlYZ (explicitYZ B C W) +
      (explicitCycleData B C W).ax •
        ((fun _ y z => if y = 0 ∧ z = 0 then 1 else 0), 0, 0) +
      (explicitCycleData B C W).ay •
        (0, (fun x _ z => if x = 0 ∧ z = 0 then 1 else 0), 0) +
      (explicitCycleData B C W).az •
        (0, 0, (fun x y _ => if x = 0 ∧ y = 0 then 1 else 0)) := by
  classical
  let cBar : I n → I n → F := fun y z => ∑ x : I n, C x y z
  let wBar : I n → I n → F := fun y z => ∑ x : I n, W x y z
  let ay : F := ∑ z : I n, cBar 0 z
  let az : F := ∑ y : I n, wBar y 0
  let c0 : K4Cube n := fun x y z =>
    C x y z + ay * if x = 0 ∧ z = 0 then 1 else 0
  let w0 : K4Cube n := fun x y z =>
    W x y z + az * if x = 0 ∧ y = 0 then 1 else 0
  let c0Bar : I n → I n → F := fun y z => ∑ x : I n, c0 x y z
  let w0Bar : I n → I n → F := fun y z => ∑ x : I n, w0 x y z
  let psi : I n → I n → F := fun y z =>
    explicitCyclicPrefix (fun r => w0Bar r 0) y +
      explicitCyclicPrefix (fun s => c0Bar y s) z
  let phiYZ : K4Cube n := fun x y z => if x = 0 then psi y z else 0
  let c1 : K4Cube n := fun x y z =>
    c0 x y z + cyclicDiffZ phiYZ x y z
  let w1 : K4Cube n := fun x y z =>
    w0 x y z + cyclicDiffY phiYZ x y z
  let phiXY0 : K4Cube n := fun x y z =>
    explicitCyclicPrefix (fun t => c1 t y z) x
  let phiXZ0 : K4Cube n := fun x y z =>
    explicitCyclicPrefix (fun t => w1 t y z) x
  let b2 : K4Cube n := fun x y z =>
    B x y z + cyclicDiffY phiXY0 x y z +
      cyclicDiffZ phiXZ0 x y z
  let g : I n → I n → F := fun y z => b2 0 y z
  let ax : F := ∑ y : I n, ∑ z : I n, g y z
  let delta : I n → I n → F := fun y z =>
    if y = 0 ∧ z = 0 then 1 else 0
  let g0 : I n → I n → F := fun y z => g y z + ax * delta y z
  let row : I n → F := fun y => ∑ z : I n, g0 y z
  let u0 : I n → F := fun y => explicitCyclicPrefix row y
  let u : I n → I n → F := fun y z => if z = 0 then u0 y else 0
  let g1 : I n → I n → F := fun y z =>
    g0 y z + u y z + u (y + 1) z
  let v : I n → I n → F := fun y z =>
    explicitCyclicPrefix (g1 y) z
  have ht := transverse_sums_and_closure B C W hcl
  change
    (∀ y, (∑ z : I n, c0Bar y z) = 0) ∧
      (∀ z, (∑ y : I n, w0Bar y z) = 0) ∧
      (∀ y z,
        c0Bar y z + c0Bar (y + 1) z +
          (w0Bar y z + w0Bar y (z + 1)) = 0) at ht
  rcases ht with ⟨hc0Sum, hw0Sum, htwo⟩
  have hp := correlated_potential_diffs B C W hcl
  change
    (∀ y z, psi y z + psi y (z + 1) = c0Bar y z) ∧
      (∀ y z, psi y z + psi (y + 1) z = w0Bar y z) at hp
  rcases hp with ⟨hpsiZ, hpsiY⟩
  have hphiSum : ∀ y z, (∑ x : I n, phiYZ x y z) = psi y z := by
    intro y z
    dsimp [phiYZ]
    rw [Finset.sum_eq_single (0 : I n)]
    · simp
    · intro x _ hx
      simp [hx]
    · simp
  have hc1Sum : ∀ y z, (∑ x : I n, c1 x y z) = 0 := by
    intro y z
    simp only [c1, Finset.sum_add_distrib, cyclicDiffZ]
    rw [hphiSum, hphiSum, hpsiZ]
    exact F_add_self _
  have hw1Sum : ∀ y z, (∑ x : I n, w1 x y z) = 0 := by
    intro y z
    simp only [w1, Finset.sum_add_distrib, cyclicDiffY]
    rw [hphiSum, hphiSum, hpsiY]
    exact F_add_self _
  have hphiXY : cyclicDiffX phiXY0 = c1 := by
    funext x y z
    let q : ZeroSumProfile n :=
      ⟨fun t => c1 t y z, LinearMap.mem_ker.mpr (hc1Sum y z)⟩
    exact congrFun (cycDiff_explicitCyclicPrimitive q) x
  have hphiXZ : cyclicDiffX phiXZ0 = w1 := by
    funext x y z
    let q : ZeroSumProfile n :=
      ⟨fun t => w1 t y z, LinearMap.mem_ker.mpr (hw1Sum y z)⟩
    exact congrFun (cycDiff_explicitCyclicPrimitive q) x
  have hc0Diff : cyclicDiffY c0 = cyclicDiffY C := by
    funext x y z
    simp only [cyclicDiffY, c0]
    ring_nf
    simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
  have hw0Diff : cyclicDiffZ w0 = cyclicDiffZ W := by
    funext x y z
    simp only [cyclicDiffZ, w0]
    ring_nf
    simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
  have hc1Diff :
      cyclicDiffY c1 =
        cyclicDiffY c0 + cyclicDiffY (cyclicDiffZ phiYZ) := by
    funext x y z
    simp only [c1, cyclicDiffY, cyclicDiffZ, Pi.add_apply]
    abel
  have hw1Diff :
      cyclicDiffZ w1 =
        cyclicDiffZ w0 + cyclicDiffZ (cyclicDiffY phiYZ) := by
    funext x y z
    simp only [w1, cyclicDiffY, cyclicDiffZ, Pi.add_apply]
    abel
  have hb2Diff : cyclicDiffX b2 = 0 := by
    funext x y z
    have hxy := congrFun (congrFun (congrFun
      (cyclicDiffX_cyclicDiffY_commute phiXY0) x) y) z
    have hxz := congrFun (congrFun (congrFun
      (cyclicDiffX_cyclicDiffZ_commute phiXZ0) x) y) z
    have hyz := congrFun (congrFun (congrFun
      (cyclicDiffY_cyclicDiffZ_commute phiYZ) x) y) z
    have hclp := hcl x y z
    have hxy' := congrFun (congrFun (congrFun hphiXY x) y) z
    have hxz' := congrFun (congrFun (congrFun hphiXZ x) y) z
    have hc0' := congrFun (congrFun (congrFun hc0Diff x) y) z
    have hw0' := congrFun (congrFun (congrFun hw0Diff x) y) z
    calc
      cyclicDiffX b2 x y z =
          cyclicDiffX B x y z +
            cyclicDiffX (cyclicDiffY phiXY0) x y z +
            cyclicDiffX (cyclicDiffZ phiXZ0) x y z := by
        simp only [b2, cyclicDiffX, cyclicDiffY, cyclicDiffZ]
        abel
      _ = cyclicDiffX B x y z +
            cyclicDiffY (cyclicDiffX phiXY0) x y z +
            cyclicDiffZ (cyclicDiffX phiXZ0) x y z := by rw [hxy, hxz]
      _ = cyclicDiffX B x y z +
            cyclicDiffY c1 x y z + cyclicDiffZ w1 x y z := by
        rw [hphiXY, hphiXZ]
      _ = (cyclicDiffX B x y z + cyclicDiffY C x y z +
              cyclicDiffZ W x y z) +
            (cyclicDiffY (cyclicDiffZ phiYZ) x y z +
              cyclicDiffY (cyclicDiffZ phiYZ) x y z) := by
        rw [show cyclicDiffY c1 x y z =
              cyclicDiffY c0 x y z +
                cyclicDiffY (cyclicDiffZ phiYZ) x y z by
              exact congrFun (congrFun (congrFun hc1Diff x) y) z,
            show cyclicDiffZ w1 x y z =
              cyclicDiffZ w0 x y z +
                cyclicDiffZ (cyclicDiffY phiYZ) x y z by
              exact congrFun (congrFun (congrFun hw1Diff x) y) z,
            hc0', hw0', ← hyz]
        abel
      _ = 0 := by rw [hclp, F_add_self, zero_add]
  have hb2Const : ∀ x y z, b2 x y z = g y z := by
    intro x y z
    have hstep : ∀ t, b2 (t + 1) y z = b2 t y z := by
      intro t
      have hd := congrFun (congrFun (congrFun hb2Diff t) y) z
      simp only [cyclicDiffX, Pi.zero_apply] at hd
      exact (F_eq_of_add_eq_zero hd).symm
    exact zmod_step_const (fun t => b2 t y z) hstep x
  have hg0Total : (∑ y : I n, ∑ z : I n, g0 y z) = 0 := by
    simp only [g0, Finset.sum_add_distrib]
    have hdelta :
        (∑ y : I n, ∑ z : I n, delta y z) = 1 := by
      dsimp [delta]
      rw [Finset.sum_eq_single (0 : I n)]
      · simp
      · intro y _ hy
        simp [hy]
      · simp
    simp_rw [← Finset.mul_sum]
    rw [hdelta, mul_one]
    exact F_add_self ax
  have hrowTotal : (∑ y : I n, row y) = 0 := by
    simpa [row] using hg0Total
  have hu0Diff : ∀ y, u0 y + u0 (y + 1) = row y := by
    let q : ZeroSumProfile n :=
      ⟨row, LinearMap.mem_ker.mpr hrowTotal⟩
    intro y
    exact congrFun (cycDiff_explicitCyclicPrimitive q) y
  have hg1Sum : ∀ y, (∑ z : I n, g1 y z) = 0 := by
    intro y
    simp only [g1, Finset.sum_add_distrib]
    have huSum : ∀ t, (∑ z : I n, u t z) = u0 t := by
      intro t
      dsimp [u]
      rw [Finset.sum_eq_single (0 : I n)]
      · simp
      · intro z _ hz
        simp [hz]
      · simp
    rw [huSum, huSum]
    change row y + u0 y + u0 (y + 1) = 0
    calc
      row y + u0 y + u0 (y + 1) =
          row y + (u0 y + u0 (y + 1)) := by abel
      _ = row y + row y := by rw [hu0Diff]
      _ = 0 := F_add_self _
  have hvDiff : ∀ y z, v y z + v y (z + 1) = g1 y z := by
    intro y
    let q : ZeroSumProfile n :=
      ⟨g1 y, LinearMap.mem_ker.mpr (hg1Sum y)⟩
    intro z
    exact congrFun (cycDiff_explicitCyclicPrimitive q) z
  have hgDecomp : ∀ y z,
      g y z =
        (u y z + u (y + 1) z) +
          (v y z + v y (z + 1)) + ax * delta y z := by
    intro y z
    rw [hvDiff]
    dsimp [g1, g0]
    ring_nf
    simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
    simp
  have hdata :
      explicitCycleData B C W =
        { xy := fun x y z => phiXY0 x y z + u y z
          xz := fun x y z => phiXZ0 x y z + v y z
          yz := phiYZ
          ax := ax
          ay := ay
          az := az } := by
    rfl
  rw [show explicitXY B C W = fun x y z => phiXY0 x y z + u y z by
        rw [explicitXY, hdata],
      show explicitXZ B C W = fun x y z => phiXZ0 x y z + v y z by
        rw [explicitXZ, hdata],
      show explicitYZ B C W = phiYZ by rw [explicitYZ, hdata],
      hdata]
  apply Prod.ext
  · funext x y z
    have htarget :
        B x y z =
        (phiXY0 x y z + u y z +
          (phiXY0 x (y + 1) z + u (y + 1) z)) +
        (phiXZ0 x y z + v y z +
          (phiXZ0 x y (z + 1) + v y (z + 1))) +
        ax * (if y = 0 ∧ z = 0 then 1 else 0) := by
      have hb : B x y z + cyclicDiffY phiXY0 x y z +
          cyclicDiffZ phiXZ0 x y z = g y z := by
        simpa [b2] using hb2Const x y z
      calc
        B x y z =
            (cyclicDiffY phiXY0 x y z +
              cyclicDiffZ phiXZ0 x y z) + g y z := by
          calc
            B x y z = B x y z + 0 := by rw [add_zero]
            _ = B x y z +
                ((cyclicDiffY phiXY0 x y z +
                    cyclicDiffZ phiXZ0 x y z) +
                  (cyclicDiffY phiXY0 x y z +
                    cyclicDiffZ phiXZ0 x y z)) := by rw [F_add_self]
            _ = (B x y z + cyclicDiffY phiXY0 x y z +
                  cyclicDiffZ phiXZ0 x y z) +
                (cyclicDiffY phiXY0 x y z +
                  cyclicDiffZ phiXZ0 x y z) := by abel
            _ = _ := by rw [hb]; abel
        _ = _ := by
          rw [hgDecomp]
          simp only [cyclicDiffY, cyclicDiffZ, delta]
          abel
    simpa [curlXY, curlXZ, curlYZ, cyclicDiffY, cyclicDiffZ] using htarget
  · apply Prod.ext
    · funext x y z
      have htarget :
          C x y z =
          (phiXY0 x y z + u y z +
            (phiXY0 (x + 1) y z + u y z)) +
          (phiYZ x y z + phiYZ x y (z + 1)) +
          ay * (if x = 0 ∧ z = 0 then 1 else 0) := by
        have hpXY := congrFun (congrFun (congrFun hphiXY x) y) z
        dsimp [c1, c0] at hpXY
        symm
        calc
          _ = cyclicDiffX phiXY0 x y z +
                cyclicDiffZ phiYZ x y z +
                ay * (if x = 0 ∧ z = 0 then 1 else 0) := by
            simp only [cyclicDiffX, cyclicDiffZ]
            ring_nf
            simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
          _ = C x y z := by
            rw [hpXY]
            ring_nf
            simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
      simpa [curlXY, curlXZ, curlYZ, cyclicDiffX, cyclicDiffZ] using htarget
    · funext x y z
      have htarget :
          W x y z =
          (phiXZ0 x y z + v y z +
            (phiXZ0 (x + 1) y z + v y z)) +
          (phiYZ x y z + phiYZ x (y + 1) z) +
          az * (if x = 0 ∧ y = 0 then 1 else 0) := by
        have hpXZ := congrFun (congrFun (congrFun hphiXZ x) y) z
        dsimp [w1, w0] at hpXZ
        symm
        calc
          _ = cyclicDiffX phiXZ0 x y z +
                cyclicDiffY phiYZ x y z +
                az * (if x = 0 ∧ y = 0 then 1 else 0) := by
            simp only [cyclicDiffX, cyclicDiffY]
            ring_nf
            simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
          _ = W x y z := by
            rw [hpXZ]
            ring_nf
            simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
      simpa [curlXY, curlXZ, curlYZ, cyclicDiffX, cyclicDiffY] using htarget

set_option maxHeartbeats 800000 in
-- Normalizing the three curl families and their cross-pairings needs this budget.
private theorem cycleQ_zero_on_generators
    {n : ℕ} [NeZero n] (_hn : 2 ≤ n) :
    (∀ phi : K4Cube n, cycleQ
      (cyclicDiffY phi) (cyclicDiffX phi) 0 = 0) ∧
    (∀ phi : K4Cube n, cycleQ
      (cyclicDiffZ phi) 0 (cyclicDiffX phi) = 0) ∧
    (∀ phi : K4Cube n, cycleQ
      0 (cyclicDiffZ phi) (cyclicDiffY phi) = 0) ∧
    (∀ p q : K4Cube n,
      cubePair (cyclicDiffY p + cyclicDiffX p)
          (cyclicDiffX (cyclicDiffZ q)) +
        cubePair (cyclicDiffZ q + cyclicDiffX q)
          (cyclicDiffX (cyclicDiffY p)) +
        cubePair (cyclicDiffX p)
          (cubeTyInvTzSum (cyclicDiffX q)) = 0) ∧
    (∀ p r : K4Cube n,
      cubePair (cyclicDiffZ r + cyclicDiffY r)
          (cyclicDiffX (cyclicDiffY p)) +
        cubePair (cyclicDiffX p)
          (cubeTyInvTzSum (cyclicDiffY r)) = 0) ∧
    (∀ q r : K4Cube n,
      cubePair (cyclicDiffZ r + cyclicDiffY r)
          (cyclicDiffX (cyclicDiffZ q)) +
        cubePair (cyclicDiffZ r)
          (cubeTyInvTzSum (cyclicDiffX q)) = 0) ∧
    cycleQ (fun _ y z => if y = 0 ∧ z = 0 then 1 else 0 : K4Cube n) 0 0 = 0 ∧
    cycleQ 0 (fun x _ z => if x = 0 ∧ z = 0 then 1 else 0 : K4Cube n) 0 = 0 ∧
    cycleQ 0 0 (fun x y _ => if x = 0 ∧ y = 0 then 1 else 0 : K4Cube n) = 0 := by
  classical
  let T := fun (a b c : I n) (f : K4Cube n) =>
    (fun x y z => f (x + a) (y + b) (z + c) : K4Cube n)
  have pair_add_left (f g h : K4Cube n) :
      cubePair (f + g) h = cubePair f h + cubePair g h := by
    unfold cubePair
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have pair_add_right (f g h : K4Cube n) :
      cubePair f (g + h) = cubePair f g + cubePair f h := by
    unfold cubePair
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have pair_zero_left (f : K4Cube n) : cubePair 0 f = 0 := by
    simp [cubePair]
  have pair_zero_right (f : K4Cube n) : cubePair f 0 = 0 := by
    simp [cubePair]
  have pair_symm (f g : K4Cube n) : cubePair f g = cubePair g f := by
    unfold cubePair
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  have pair_simul (a b c : I n) (f g : K4Cube n) :
      cubePair (T a b c f) (T a b c g) = cubePair f g := by
    unfold cubePair
    have hx : ∀ y z,
        (∑ x : I n,
          T a b c f x y z * T a b c g x y z) =
        ∑ x : I n, f x (y + b) (z + c) * g x (y + b) (z + c) := by
      intro y z
      simpa [T] using
        sum_shift (n := n) a
          (fun x => f x (y + b) (z + c) * g x (y + b) (z + c))
    simp_rw [hx]
    have hz : ∀ y,
        (∑ z : I n, ∑ x : I n,
          f x (y + b) (z + c) * g x (y + b) (z + c)) =
        ∑ z : I n, ∑ x : I n, f x (y + b) z * g x (y + b) z := by
      intro y
      simpa using
        sum_shift (n := n) c
          (fun z => ∑ x : I n, f x (y + b) z * g x (y + b) z)
    simp_rw [hz]
    simpa using
      sum_shift (n := n) b
        (fun y => ∑ z : I n, ∑ x : I n, f x y z * g x y z)
  have pair_normalize (a b c a' b' c' : I n) (f g : K4Cube n) :
      cubePair (T a b c f) (T a' b' c' g) =
        cubePair f (T (a' - a) (b' - b) (c' - c) g) := by
    have h := pair_simul (-a) (-b) (-c)
      (T a b c f) (T a' b' c' g)
    simpa [T, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h.symm
  have rectangle_self_cancel
      (a b c a' b' c' : I n) (phi : K4Cube n) :
      cubePair (T a b c phi + T a' b' c' phi)
        (phi + T a b c phi + T a' b' c' phi +
          T (a + a') (b + b') (c + c') phi) = 0 := by
    let A := T a b c phi
    let B := T a' b' c' phi
    let AB := T (a + a') (b + b') (c + c') phi
    have hAA : cubePair A A = cubePair phi phi := pair_simul _ _ _ _ _
    have hBB : cubePair B B = cubePair phi phi := pair_simul _ _ _ _ _
    have hAB : cubePair A B = cubePair B A := pair_symm _ _
    have hAp : cubePair A phi = cubePair phi A := pair_symm _ _
    have hBp : cubePair B phi = cubePair phi B := pair_symm _ _
    have hAAB : cubePair A AB = cubePair phi B := by
      dsimp [A, AB, B]
      rw [pair_normalize]
      congr 2 <;> abel
    have hBAB : cubePair B AB = cubePair phi A := by
      dsimp [A, AB, B]
      rw [pair_normalize]
      congr 2 <;> abel
    dsimp [A, B, AB] at *
    simp only [pair_add_left, pair_add_right]
    rw [hAA, hBB, hAB, hAp, hBp, hAAB, hBAB]
    ring_nf
    simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
  have hXY : ∀ phi : K4Cube n,
      cycleQ (cyclicDiffY phi) (cyclicDiffX phi) 0 = 0 := by
    intro phi
    have hB : cyclicDiffY phi = phi + T 0 1 0 phi := by
      funext x y z
      simp [cyclicDiffY, T]
    have hC : cyclicDiffX phi = phi + T 1 0 0 phi := by
      funext x y z
      simp [cyclicDiffX, T]
    rw [hB, hC]
    have hS :
        (phi + T 0 1 0 phi) + (phi + T 1 0 0 phi) + 0 =
          T 0 1 0 phi + T 1 0 0 phi := by
      funext x y z
      simp only [Pi.add_apply, Pi.zero_apply]
      ring_nf
      simp only [show (2 : F) = 0 by decide, mul_zero, zero_add]
    have hD :
        cyclicDiffX (phi + T 0 1 0 phi) =
          phi + T 0 1 0 phi + T 1 0 0 phi + T 1 1 0 phi := by
      funext x y z
      simp only [cyclicDiffX, Pi.add_apply, T]
      abel
    have hzero : cubeTyInvTzSum (0 : K4Cube n) = 0 := by
      funext x y z
      simp [cubeTyInvTzSum]
    rw [cycleQ, hS, hD, hzero, pair_zero_right]
    simp only [add_zero]
    simpa [T] using rectangle_self_cancel 0 1 0 1 0 0 phi
  have hXZ : ∀ phi : K4Cube n,
      cycleQ (cyclicDiffZ phi) 0 (cyclicDiffX phi) = 0 := by
    intro phi
    have hB : cyclicDiffZ phi = phi + T 0 0 1 phi := by
      funext x y z
      simp [cyclicDiffZ, T]
    have hW : cyclicDiffX phi = phi + T 1 0 0 phi := by
      funext x y z
      simp [cyclicDiffX, T]
    rw [hB, hW]
    have hS :
        (phi + T 0 0 1 phi) + 0 + (phi + T 1 0 0 phi) =
          T 0 0 1 phi + T 1 0 0 phi := by
      funext x y z
      simp only [Pi.add_apply, Pi.zero_apply]
      ring_nf
      simp only [show (2 : F) = 0 by decide, mul_zero, zero_add]
    have hD :
        cyclicDiffX (phi + T 0 0 1 phi) =
          phi + T 0 0 1 phi + T 1 0 0 phi + T 1 0 1 phi := by
      funext x y z
      simp only [cyclicDiffX, Pi.add_apply, T]
      abel
    rw [cycleQ, hS, hD, pair_zero_left]
    simp only [add_zero]
    simpa using rectangle_self_cancel 0 0 1 1 0 0 phi
  have pair_auto_neg (a b c : I n) (f : K4Cube n) :
      cubePair f (T a b c f) = cubePair f (T (-a) (-b) (-c) f) := by
    calc
      cubePair f (T a b c f) = cubePair (T a b c f) f := pair_symm _ _
      _ = cubePair f (T (0 - a) (0 - b) (0 - c) f) := by
        simpa [T] using pair_normalize a b c 0 0 0 f f
      _ = _ := by simp
  have plaquette_self_cancel (phi : K4Cube n) :
      cubePair (phi + T 0 0 1 phi)
        (phi + T 0 1 0 phi + T 0 (-1) 1 phi + T 0 0 1 phi) = 0 := by
    let Y := T 0 1 0 phi
    let Z := T 0 0 1 phi
    let M := T 0 (-1) 1 phi
    have hZZ : cubePair Z Z = cubePair phi phi := pair_simul _ _ _ _ _
    have hZp : cubePair Z phi = cubePair phi Z := pair_symm _ _
    have hZM : cubePair Z M = cubePair phi (T 0 (-1) 0 phi) := by
      dsimp [Z, M]
      rw [pair_normalize]
      congr 2 <;> norm_num
    have hpYneg : cubePair phi (T 0 (-1) 0 phi) = cubePair phi Y := by
      dsimp [Y]
      simpa using (pair_auto_neg 0 1 0 phi).symm
    have hZY : cubePair Z Y = cubePair phi (T 0 1 (-1) phi) := by
      dsimp [Z, Y]
      rw [pair_normalize]
      congr 2 <;> norm_num
    have hpMneg :
        cubePair phi (T 0 1 (-1) phi) = cubePair phi M := by
      dsimp [M]
      simpa using (pair_auto_neg 0 (-1) 1 phi).symm
    dsimp [Y, Z, M] at *
    simp only [pair_add_left, pair_add_right]
    rw [hZZ, hZp, hZM, hpYneg, hZY, hpMneg]
    ring_nf
    simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
  have hYZ : ∀ phi : K4Cube n,
      cycleQ 0 (cyclicDiffZ phi) (cyclicDiffY phi) = 0 := by
    intro phi
    have hC : cyclicDiffZ phi = phi + T 0 0 1 phi := by
      funext x y z
      simp [cyclicDiffZ, T]
    have hW : cyclicDiffY phi = phi + T 0 1 0 phi := by
      funext x y z
      simp [cyclicDiffY, T]
    rw [hC, hW]
    have hK :
        cubeTyInvTzSum (phi + T 0 1 0 phi) =
          phi + T 0 1 0 phi + T 0 (-1) 1 phi + T 0 0 1 phi := by
      funext x y z
      simp only [cubeTyInvTzSum, Pi.add_apply, T]
      have hy : y - 1 + 1 = y := by abel
      rw [hy]
      abel
    have hzero : cyclicDiffX (0 : K4Cube n) = 0 := by
      funext x y z
      simp [cyclicDiffX]
    rw [cycleQ, hzero, hK, pair_zero_right, zero_add]
    exact plaquette_self_cancel phi
  have hCrossXYXZ : ∀ p q : K4Cube n,
      cubePair (cyclicDiffY p + cyclicDiffX p)
          (cyclicDiffX (cyclicDiffZ q)) +
        cubePair (cyclicDiffZ q + cyclicDiffX q)
          (cyclicDiffX (cyclicDiffY p)) +
        cubePair (cyclicDiffX p)
          (cubeTyInvTzSum (cyclicDiffX q)) = 0 := by
    intro p q
    have canonQP (a b c : I n) :
        cubePair q (T a b c p) =
          cubePair p (T (-a) (-b) (-c) q) := by
      calc
        cubePair q (T a b c p) = cubePair (T a b c p) q :=
          pair_symm _ _
        _ = cubePair p (T (0 - a) (0 - b) (0 - c) q) := by
          simpa [T] using pair_normalize a b c 0 0 0 p q
        _ = _ := by simp
    have hSp :
        cyclicDiffY p + cyclicDiffX p = T 0 1 0 p + T 1 0 0 p := by
      funext x y z
      simp only [cyclicDiffX, cyclicDiffY, Pi.add_apply, T]
      ring_nf
      simp only [show (2 : F) = 0 by decide, mul_zero, zero_add]
    have hSq :
        cyclicDiffZ q + cyclicDiffX q = T 0 0 1 q + T 1 0 0 q := by
      funext x y z
      simp only [cyclicDiffX, cyclicDiffZ, Pi.add_apply, T]
      ring_nf
      simp only [show (2 : F) = 0 by decide, mul_zero, zero_add]
    have hdxz :
        cyclicDiffX (cyclicDiffZ q) =
          q + T 0 0 1 q + T 1 0 0 q + T 1 0 1 q := by
      funext x y z
      simp only [cyclicDiffX, cyclicDiffZ, T, Pi.add_apply]
      abel
    have hdxy :
        cyclicDiffX (cyclicDiffY p) =
          p + T 0 1 0 p + T 1 0 0 p + T 1 1 0 p := by
      funext x y z
      simp only [cyclicDiffX, cyclicDiffY, T, Pi.add_apply]
      abel
    have hxp : cyclicDiffX p = p + T 1 0 0 p := by
      funext x y z
      simp [cyclicDiffX, T]
    have hkxq :
        cubeTyInvTzSum (cyclicDiffX q) =
          q + T 1 0 0 q + T 0 (-1) 1 q + T 1 (-1) 1 q := by
      funext x y z
      simp only [cubeTyInvTzSum, cyclicDiffX, T, Pi.add_apply]
      abel
    have hPshiftQ (a b c : I n) :
        cubePair (T a b c p) q =
          cubePair p (T (-a) (-b) (-c) q) := by
      simpa [T] using pair_normalize a b c 0 0 0 p q
    have hQshiftP (a b c : I n) :
        cubePair (T a b c q) p = cubePair p (T a b c q) :=
      pair_symm _ _
    have hT0 : T 0 0 0 q = q := by
      funext x y z
      simp [T]
    rw [hSp, hSq, hdxz, hdxy, hxp, hkxq]
    simp only [pair_add_left, pair_add_right]
    simp only [pair_normalize]
    simp only [canonQP]
    simp only [hPshiftQ, hQshiftP]
    norm_num
    rw [hT0]
    ring_nf
    simp only [show (2 : F) = 0 by decide, show (4 : F) = 0 by decide,
      mul_zero, add_zero]
  have hCrossXYYZ : ∀ p r : K4Cube n,
      cubePair (cyclicDiffZ r + cyclicDiffY r)
          (cyclicDiffX (cyclicDiffY p)) +
        cubePair (cyclicDiffX p)
          (cubeTyInvTzSum (cyclicDiffY r)) = 0 := by
    intro p r
    have canonRP (a b c : I n) :
        cubePair r (T a b c p) =
          cubePair p (T (-a) (-b) (-c) r) := by
      calc
        cubePair r (T a b c p) = cubePair (T a b c p) r :=
          pair_symm _ _
        _ = cubePair p (T (0 - a) (0 - b) (0 - c) r) := by
          simpa [T] using pair_normalize a b c 0 0 0 p r
        _ = _ := by simp
    have hSr :
        cyclicDiffZ r + cyclicDiffY r = T 0 0 1 r + T 0 1 0 r := by
      funext x y z
      simp only [cyclicDiffY, cyclicDiffZ, Pi.add_apply, T]
      ring_nf
      simp only [show (2 : F) = 0 by decide, mul_zero, zero_add]
    have hdxy :
        cyclicDiffX (cyclicDiffY p) =
          p + T 0 1 0 p + T 1 0 0 p + T 1 1 0 p := by
      funext x y z
      simp only [cyclicDiffX, cyclicDiffY, T, Pi.add_apply]
      abel
    have hxp : cyclicDiffX p = p + T 1 0 0 p := by
      funext x y z
      simp [cyclicDiffX, T]
    have hkyr :
        cubeTyInvTzSum (cyclicDiffY r) =
          r + T 0 1 0 r + T 0 (-1) 1 r + T 0 0 1 r := by
      funext x y z
      simp only [cubeTyInvTzSum, cyclicDiffY, T, Pi.add_apply]
      have hy : y - 1 + 1 = y := by abel
      rw [hy]
      abel
    have hPshiftR (a b c : I n) :
        cubePair (T a b c p) r =
          cubePair p (T (-a) (-b) (-c) r) := by
      simpa [T] using pair_normalize a b c 0 0 0 p r
    have hRshiftP (a b c : I n) :
        cubePair (T a b c r) p = cubePair p (T a b c r) :=
      pair_symm _ _
    have hT0 : T 0 0 0 r = r := by
      funext x y z
      simp [T]
    rw [hSr, hdxy, hxp, hkyr]
    simp only [pair_add_left, pair_add_right]
    simp only [pair_normalize]
    simp only [canonRP, hPshiftR, hRshiftP]
    norm_num
    rw [hT0]
    ring_nf
    simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
  have hCrossXZYZ : ∀ q r : K4Cube n,
      cubePair (cyclicDiffZ r + cyclicDiffY r)
          (cyclicDiffX (cyclicDiffZ q)) +
        cubePair (cyclicDiffZ r)
          (cubeTyInvTzSum (cyclicDiffX q)) = 0 := by
    intro q r
    have canonRQ (a b c : I n) :
        cubePair r (T a b c q) =
          cubePair q (T (-a) (-b) (-c) r) := by
      calc
        cubePair r (T a b c q) = cubePair (T a b c q) r :=
          pair_symm _ _
        _ = cubePair q (T (0 - a) (0 - b) (0 - c) r) := by
          simpa [T] using pair_normalize a b c 0 0 0 q r
        _ = _ := by simp
    have hSr :
        cyclicDiffZ r + cyclicDiffY r = T 0 0 1 r + T 0 1 0 r := by
      funext x y z
      simp only [cyclicDiffY, cyclicDiffZ, Pi.add_apply, T]
      ring_nf
      simp only [show (2 : F) = 0 by decide, mul_zero, zero_add]
    have hdxz :
        cyclicDiffX (cyclicDiffZ q) =
          q + T 0 0 1 q + T 1 0 0 q + T 1 0 1 q := by
      funext x y z
      simp only [cyclicDiffX, cyclicDiffZ, T, Pi.add_apply]
      abel
    have hzr : cyclicDiffZ r = r + T 0 0 1 r := by
      funext x y z
      simp [cyclicDiffZ, T]
    have hkxq :
        cubeTyInvTzSum (cyclicDiffX q) =
          q + T 1 0 0 q + T 0 (-1) 1 q + T 1 (-1) 1 q := by
      funext x y z
      simp only [cubeTyInvTzSum, cyclicDiffX, T, Pi.add_apply]
      abel
    have hQshiftR (a b c : I n) :
        cubePair (T a b c q) r =
          cubePair q (T (-a) (-b) (-c) r) := by
      simpa [T] using pair_normalize a b c 0 0 0 q r
    have hRshiftQ (a b c : I n) :
        cubePair (T a b c r) q = cubePair q (T a b c r) :=
      pair_symm _ _
    have hT0 : T 0 0 0 r = r := by
      funext x y z
      simp [T]
    rw [hSr, hdxz, hzr, hkxq]
    simp only [pair_add_left, pair_add_right]
    simp only [pair_normalize]
    simp only [canonRQ, hRshiftQ]
    norm_num
    rw [hT0]
    rw [pair_symm r q]
    abel_nf
    simp only [two_smul, F_add_self, zero_add]
  let hx : K4Cube n :=
    fun _ y z => if y = 0 ∧ z = 0 then 1 else 0
  let hy : K4Cube n :=
    fun x _ z => if x = 0 ∧ z = 0 then 1 else 0
  let hz : K4Cube n :=
    fun x y _ => if x = 0 ∧ y = 0 then 1 else 0
  have hdx_hx : cyclicDiffX hx = 0 := by
    funext x y z
    dsimp [hx, cyclicDiffX]
    exact F_add_self _
  have hdx_zero : cyclicDiffX (0 : K4Cube n) = 0 := by
    funext x y z
    simp [cyclicDiffX]
  have hQx : cycleQ hx 0 0 = 0 := by
    rw [cycleQ, hdx_hx, pair_zero_right]
    simp [cubePair, cubeTyInvTzSum]
  have hQy : cycleQ 0 hy 0 = 0 := by
    rw [cycleQ, hdx_zero, pair_zero_right]
    simp [cubePair, cubeTyInvTzSum]
  have hQz : cycleQ 0 0 hz = 0 := by
    rw [cycleQ, hdx_zero, pair_zero_right]
    simp [cubePair]
  exact ⟨hXY, hXZ, hYZ, hCrossXYXZ, hCrossXYYZ, hCrossXZYZ,
    hQx, hQy, hQz⟩

private theorem cycleQ_harmonic_polar_zero
    {n : ℕ} [NeZero n] (_hn : 2 ≤ n)
    (B C W : K4Cube n) (hcl : k4Closure B C W) :
    let hx : K4Cube n :=
      fun _ y z => if y = 0 ∧ z = 0 then 1 else 0
    let hy : K4Cube n :=
      fun x _ z => if x = 0 ∧ z = 0 then 1 else 0
    let hz : K4Cube n :=
      fun x y _ => if x = 0 ∧ y = 0 then 1 else 0
    cubePair hx (cyclicDiffX B) = 0 ∧
      (cubePair hy (cyclicDiffX B) +
        cubePair hy (cubeTyInvTzSum W) = 0) ∧
      (cubePair hz (cyclicDiffX B) +
        cubePair C (cubeTyInvTzSum hz) = 0) := by
  classical
  let hx : K4Cube n :=
    fun _ y z => if y = 0 ∧ z = 0 then 1 else 0
  let hy : K4Cube n :=
    fun x _ z => if x = 0 ∧ z = 0 then 1 else 0
  let hz : K4Cube n :=
    fun x y _ => if x = 0 ∧ y = 0 then 1 else 0
  have hsumDX (y z : I n) :
      (∑ x : I n, cyclicDiffX B x y z) = 0 := by
    simp only [cyclicDiffX, Finset.sum_add_distrib]
    rw [sum_shift (n := n) (1 : I n) (fun x => B x y z)]
    exact F_add_self _
  have hsumDY (x z : I n) :
      (∑ y : I n, cyclicDiffY C x y z) = 0 := by
    simp only [cyclicDiffY, Finset.sum_add_distrib]
    rw [sum_shift (n := n) (1 : I n) (fun y => C x y z)]
    exact F_add_self _
  have hsumDZ (x y : I n) :
      (∑ z : I n, cyclicDiffZ W x y z) = 0 := by
    simp only [cyclicDiffZ, Finset.sum_add_distrib]
    rw [sum_shift (n := n) (1 : I n) (fun z => W x y z)]
    exact F_add_self _
  have hclY :
      (∑ y : I n, cyclicDiffX B 0 y 0) +
        (∑ y : I n, cyclicDiffZ W 0 y 0) = 0 := by
    calc
      _ = (∑ y : I n, (
          cyclicDiffX B 0 y 0 + cyclicDiffY C 0 y 0 +
            cyclicDiffZ W 0 y 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumDY]
        simp
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        exact hcl 0 y 0
  have hclZ :
      (∑ z : I n, cyclicDiffX B 0 0 z) +
        (∑ z : I n, cyclicDiffY C 0 0 z) = 0 := by
    calc
      _ = (∑ z : I n, (
          cyclicDiffX B 0 0 z + cyclicDiffY C 0 0 z +
            cyclicDiffZ W 0 0 z)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumDZ]
        simp
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro z _
        exact hcl 0 0 z
  have pair_hx (f : K4Cube n) :
      cubePair hx f = ∑ x : I n, f x 0 0 := by
    unfold cubePair
    rw [Fintype.sum_eq_single 0]
    · rw [Fintype.sum_eq_single 0]
      · simp [hx]
      · intro z hz
        simp [hx, hz]
    · intro y hy0
      simp [hx, hy0]
  have pair_hy (f : K4Cube n) :
      cubePair hy f = ∑ y : I n, f 0 y 0 := by
    unfold cubePair
    apply Finset.sum_congr rfl
    intro y _
    rw [Fintype.sum_eq_single 0]
    · rw [Fintype.sum_eq_single 0]
      · simp [hy]
      · intro x hx0
        simp [hy, hx0]
    · intro z hz0
      simp [hy, hz0]
  have hX : cubePair hx (cyclicDiffX B) = 0 := by
    rw [pair_hx]
    exact hsumDX 0 0
  have hY :
      cubePair hy (cyclicDiffX B) +
        cubePair hy (cubeTyInvTzSum W) = 0 := by
    rw [pair_hy, pair_hy]
    have hshift :
        (∑ y : I n, W 0 (y - 1) 1) = ∑ y : I n, W 0 y 1 := by
      simpa [sub_eq_add_neg] using
        sum_shift (n := n) (-1 : I n) (fun y => W 0 y 1)
    simp only [cubeTyInvTzSum, Finset.sum_add_distrib]
    norm_num
    rw [hshift]
    simpa [cyclicDiffZ, Finset.sum_add_distrib] using hclY
  have hZ :
      cubePair hz (cyclicDiffX B) +
        cubePair C (cubeTyInvTzSum hz) = 0 := by
    have pair_symm (f g : K4Cube n) :
        cubePair f g = cubePair g f := by
      unfold cubePair
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x _
      exact mul_comm _ _
    have pair_hz_right (a : I n) (f : K4Cube n) :
        cubePair f
          (fun x y _ => if x = 0 ∧ y = a then 1 else 0 : K4Cube n) =
          ∑ z : I n, f 0 a z := by
      unfold cubePair
      rw [Fintype.sum_eq_single a]
      · apply Finset.sum_congr rfl
        intro z _
        rw [Fintype.sum_eq_single 0]
        · simp
        · intro x hx0
          simp [hx0]
      · intro y hya
        simp [hya]
    have pair_hz_left (f : K4Cube n) :
        cubePair hz f = ∑ z : I n, f 0 0 z := by
      calc
        cubePair hz f = cubePair f hz := pair_symm _ _
        _ = _ := by simpa [hz] using pair_hz_right (0 : I n) f
    let hz1 : K4Cube n :=
      fun x y _ => if x = 0 ∧ y = 1 then 1 else 0
    have hK : cubeTyInvTzSum hz = hz + hz1 := by
      funext x y z
      simp [cubeTyInvTzSum, hz, hz1, sub_eq_zero]
    have pair_add_right (f g h : K4Cube n) :
        cubePair f (g + h) = cubePair f g + cubePair f h := by
      unfold cubePair
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [pair_hz_left, hK, pair_add_right]
    rw [show cubePair C hz = ∑ z : I n, C 0 0 z by
      simpa [hz] using pair_hz_right (0 : I n) C]
    rw [show cubePair C hz1 = ∑ z : I n, C 0 1 z by
      simpa [hz1] using pair_hz_right (1 : I n) C]
    simpa [cyclicDiffY, Finset.sum_add_distrib] using hclZ
  exact ⟨hX, hY, hZ⟩

set_option maxHeartbeats 800000 in
-- Reassembling the explicit curl and harmonic decomposition needs this budget.
theorem cycleQ_zero_of_closure
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (B C W : K4Cube n) (hcl : k4Closure B C W) :
    cycleQ B C W = 0 := by
  classical
  have pair_add_left (f g h : K4Cube n) :
      cubePair (f + g) h = cubePair f h + cubePair g h := by
    unfold cubePair
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have pair_add_right (f g h : K4Cube n) :
      cubePair f (g + h) = cubePair f g + cubePair f h := by
    unfold cubePair
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have pair_zero_left (f : K4Cube n) : cubePair 0 f = 0 := by
    simp [cubePair]
  have pair_zero_right (f : K4Cube n) : cubePair f 0 = 0 := by
    simp [cubePair]
  have hQadd (B C W b c w : K4Cube n) :
      cycleQ (B + b) (C + c) (W + w) =
        cycleQ B C W + cycleQ b c w +
          (cubePair (B + C + W) (cyclicDiffX b) +
            cubePair (b + c + w) (cyclicDiffX B) +
            cubePair C (cubeTyInvTzSum w) +
            cubePair c (cubeTyInvTzSum W)) := by
    have hdx : cyclicDiffX (B + b) =
        cyclicDiffX B + cyclicDiffX b := by
      funext x y z
      simp only [cyclicDiffX, Pi.add_apply]
      abel
    have hK : cubeTyInvTzSum (W + w) =
        cubeTyInvTzSum W + cubeTyInvTzSum w := by
      funext x y z
      simp only [cubeTyInvTzSum, Pi.add_apply]
      abel
    have hS : (B + b) + (C + c) + (W + w) =
        (B + C + W) + (b + c + w) := by
      funext x y z
      simp only [Pi.add_apply]
      abel
    rw [cycleQ, hdx, hK, hS]
    simp only [pair_add_left]
    unfold cycleQ
    simp only [pair_add_left, pair_add_right]
    ring
  obtain ⟨hQxy, hQxz, hQyz, hXYXZ, hXYYZ, hXZYZ,
      hQx, hQy, hQz⟩ := cycleQ_zero_on_generators hn
  let p := explicitXY B C W
  let q := explicitXZ B C W
  let r := explicitYZ B C W
  let Bc : K4Cube n := cyclicDiffY p + cyclicDiffZ q
  let Cc : K4Cube n := cyclicDiffX p + cyclicDiffZ r
  let Wc : K4Cube n := cyclicDiffX q + cyclicDiffY r
  have hQUV :
      cycleQ (cyclicDiffY p + cyclicDiffZ q)
        (cyclicDiffX p) (cyclicDiffX q) = 0 := by
    rw [← add_zero (cyclicDiffX p), ← zero_add (cyclicDiffX q)]
    rw [hQadd (cyclicDiffY p) (cyclicDiffX p) 0
      (cyclicDiffZ q) 0 (cyclicDiffX q)]
    rw [hQxy p, hQxz q]
    simp only [zero_add, add_zero, pair_zero_left]
    exact hXYXZ p q
  have hdx_add (f g : K4Cube n) :
      cyclicDiffX (f + g) = cyclicDiffX f + cyclicDiffX g := by
    funext x y z
    simp only [cyclicDiffX, Pi.add_apply]
    abel
  have hdx_zero : cyclicDiffX (0 : K4Cube n) = 0 := by
    funext x y z
    simp [cyclicDiffX]
  have hQCurl : cycleQ Bc Cc Wc = 0 := by
    rw [show Bc = (cyclicDiffY p + cyclicDiffZ q) + 0 by
      simp [Bc]]
    rw [show Cc = cyclicDiffX p + cyclicDiffZ r by rfl]
    rw [show Wc = cyclicDiffX q + cyclicDiffY r by rfl]
    rw [hQadd (cyclicDiffY p + cyclicDiffZ q) (cyclicDiffX p)
      (cyclicDiffX q) 0 (cyclicDiffZ r) (cyclicDiffY r)]
    rw [hQUV, hQyz r]
    simp only [zero_add, add_zero, pair_zero_right,
      pair_add_left, pair_add_right, hdx_add, hdx_zero]
    have h₁ := hXYYZ p r
    have h₂ := hXZYZ q r
    simp only [pair_add_left] at h₁ h₂
    linear_combination h₁ + h₂
  have hclCurl : k4Closure Bc Cc Wc := by
    intro x y z
    dsimp [Bc, Cc, Wc, p, q, r]
    simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ, Pi.add_apply]
    ring_nf
    simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
  let hx : K4Cube n :=
    fun _ y z => if y = 0 ∧ z = 0 then 1 else 0
  let hy : K4Cube n :=
    fun x _ z => if x = 0 ∧ z = 0 then 1 else 0
  let hz : K4Cube n :=
    fun x y _ => if x = 0 ∧ y = 0 then 1 else 0
  have hdy_add (f g : K4Cube n) :
      cyclicDiffY (f + g) = cyclicDiffY f + cyclicDiffY g := by
    funext x y z
    simp only [cyclicDiffY, Pi.add_apply]
    abel
  have hdz_add (f g : K4Cube n) :
      cyclicDiffZ (f + g) = cyclicDiffZ f + cyclicDiffZ g := by
    funext x y z
    simp only [cyclicDiffZ, Pi.add_apply]
    abel
  have hcl_add (B C W b c w : K4Cube n)
      (h₁ : k4Closure B C W) (h₂ : k4Closure b c w) :
      k4Closure (B + b) (C + c) (W + w) := by
    intro x y z
    rw [hdx_add, hdy_add, hdz_add]
    simp only [Pi.add_apply]
    have h₁' := h₁ x y z
    have h₂' := h₂ x y z
    linear_combination h₁' + h₂'
  have hclHx : k4Closure hx 0 0 := by
    intro x y z
    simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ, hx, Pi.zero_apply,
      zero_add]
    simpa only [add_zero] using F_add_self
      (if y = 0 ∧ z = 0 then (1 : F) else 0)
  have hclHy : k4Closure 0 hy 0 := by
    intro x y z
    simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ, hy, Pi.zero_apply,
      zero_add]
    simpa only [add_zero] using F_add_self
      (if x = 0 ∧ z = 0 then (1 : F) else 0)
  have hclHz : k4Closure 0 0 hz := by
    intro x y z
    simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ, hz, Pi.zero_apply,
      zero_add]
    exact F_add_self _
  have hdx_hx : cyclicDiffX hx = 0 := by
    funext x y z
    simp only [cyclicDiffX, hx, Pi.zero_apply]
    exact F_add_self _
  have hKzero : cubeTyInvTzSum (0 : K4Cube n) = 0 := by
    funext x y z
    simp [cubeTyInvTzSum]
  have hQx' : cycleQ hx 0 0 = 0 := by simpa [hx] using hQx
  have hQy' : cycleQ 0 hy 0 = 0 := by simpa [hy] using hQy
  have hQz' : cycleQ 0 0 hz = 0 := by simpa [hz] using hQz
  have hAddHx (X Y Z : K4Cube n)
      (hXcl : k4Closure X Y Z) (hXq : cycleQ X Y Z = 0) :
      cycleQ (X + hx) Y Z = 0 := by
    obtain ⟨hpx, _, _⟩ :=
      cycleQ_harmonic_polar_zero hn X Y Z hXcl
    rw [show Y = Y + 0 by simp, show Z = Z + 0 by simp]
    rw [hQadd X Y Z hx 0 0, hXq]
    rw [hQx', hdx_hx, hKzero]
    simpa only [zero_add, add_zero, pair_zero_left, pair_zero_right] using hpx
  have hAddHy (X Y Z : K4Cube n)
      (hXcl : k4Closure X Y Z) (hXq : cycleQ X Y Z = 0) :
      cycleQ X (Y + hy) Z = 0 := by
    obtain ⟨_, hpy, _⟩ :=
      cycleQ_harmonic_polar_zero hn X Y Z hXcl
    rw [show X = X + 0 by simp, show Z = Z + 0 by simp]
    rw [hQadd X Y Z 0 hy 0, hXq]
    rw [hQy', hdx_zero, hKzero]
    simpa only [zero_add, add_zero, pair_zero_left, pair_zero_right] using hpy
  have hAddHz (X Y Z : K4Cube n)
      (hXcl : k4Closure X Y Z) (hXq : cycleQ X Y Z = 0) :
      cycleQ X Y (Z + hz) = 0 := by
    obtain ⟨_, _, hpz⟩ :=
      cycleQ_harmonic_polar_zero hn X Y Z hXcl
    rw [show X = X + 0 by simp, show Y = Y + 0 by simp]
    rw [hQadd X Y Z 0 0 hz, hXq]
    rw [hQz', hdx_zero]
    simpa only [zero_add, add_zero, pair_zero_left, pair_zero_right] using hpz
  have hAddHxScalar (a : F) (X Y Z : K4Cube n)
      (hXcl : k4Closure X Y Z) (hXq : cycleQ X Y Z = 0) :
      cycleQ (X + a • hx) Y Z = 0 := by
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simpa using hXq
    · simpa using hAddHx X Y Z hXcl hXq
  have hClHxScalar (a : F) (X Y Z : K4Cube n)
      (hXcl : k4Closure X Y Z) :
      k4Closure (X + a • hx) Y Z := by
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simpa using hXcl
    · simpa using hcl_add X Y Z hx 0 0 hXcl hclHx
  have hAddHyScalar (a : F) (X Y Z : K4Cube n)
      (hXcl : k4Closure X Y Z) (hXq : cycleQ X Y Z = 0) :
      cycleQ X (Y + a • hy) Z = 0 := by
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simpa using hXq
    · simpa using hAddHy X Y Z hXcl hXq
  have hClHyScalar (a : F) (X Y Z : K4Cube n)
      (hXcl : k4Closure X Y Z) :
      k4Closure X (Y + a • hy) Z := by
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simpa using hXcl
    · simpa using hcl_add X Y Z 0 hy 0 hXcl hclHy
  have hAddHzScalar (a : F) (X Y Z : K4Cube n)
      (hXcl : k4Closure X Y Z) (hXq : cycleQ X Y Z = 0) :
      cycleQ X Y (Z + a • hz) = 0 := by
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simpa using hXq
    · simpa using hAddHz X Y Z hXcl hXq
  let d := explicitCycleData B C W
  have hQ1 : cycleQ (Bc + d.ax • hx) Cc Wc = 0 :=
    hAddHxScalar d.ax Bc Cc Wc hclCurl hQCurl
  have hcl1 : k4Closure (Bc + d.ax • hx) Cc Wc :=
    hClHxScalar d.ax Bc Cc Wc hclCurl
  have hQ2 :
      cycleQ (Bc + d.ax • hx) (Cc + d.ay • hy) Wc = 0 :=
    hAddHyScalar d.ay (Bc + d.ax • hx) Cc Wc hcl1 hQ1
  have hcl2 :
      k4Closure (Bc + d.ax • hx) (Cc + d.ay • hy) Wc :=
    hClHyScalar d.ay (Bc + d.ax • hx) Cc Wc hcl1
  have hQ3 :
      cycleQ (Bc + d.ax • hx) (Cc + d.ay • hy)
        (Wc + d.az • hz) = 0 :=
    hAddHzScalar d.az (Bc + d.ax • hx) (Cc + d.ay • hy) Wc hcl2 hQ2
  have hdec := cycle_decompose_explicit hn B C W hcl
  have hB := congrArg (fun t : K4Cycle n => t.1) hdec
  have hC := congrArg (fun t : K4Cycle n => t.2.1) hdec
  have hW := congrArg (fun t : K4Cycle n => t.2.2) hdec
  have hB' : B = Bc + d.ax • hx := by
    simpa [curlXY, curlXZ, curlYZ, Bc, p, q, r, d, hx] using hB
  have hC' : C = Cc + d.ay • hy := by
    simpa [curlXY, curlXZ, curlYZ, Cc, p, q, r, d, hy] using hC
  have hW' : W = Wc + d.az • hz := by
    simpa [curlXY, curlXZ, curlYZ, Wc, p, q, r, d, hz] using hW
  rw [hB', hC', hW']
  exact hQ3

theorem k4Singleton_defect_zero
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (R B C W Z : K4Cube n)
    (hroot : k4SingletonRootRelation B W Z)
    (hdualB : k4SingletonDualBRelation R C W)
    (hdualZ : k4SingletonDualZRelation C Z) :
    k4SingletonDefect R C W = 0 := by
  rw [defect_eq_cycleQ hn R B C W Z hroot hdualB hdualZ]
  exact cycleQ_zero_of_closure hn B C W
    (relations_imply_closure hn B C W Z hroot hdualZ)

end

end Core4loop.CompleteGraph.ScalarCycle
