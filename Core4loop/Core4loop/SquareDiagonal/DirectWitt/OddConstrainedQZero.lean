import Core4loop.SquareDiagonal.DirectWitt.OddScalarRadicalSign

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

open Core4loop.SquareDiagonal.EvenP

noncomputable section

attribute [local instance] Fintype.ofFinite

private theorem cubeDiffI_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffI f i j k = f i j k + f (i + 1) j k :=
  rfl

private theorem cubeDiffK_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffK f i j k = f i j k + f i j (k + 1) := by
  change f i j k + f (i + 0) (j + 0) (k + 1) = _
  simp

private theorem cubeDiffJInv_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffJInv f i j k = f i j k + f i (j - 1) k := by
  change f i j k + f (i + 0) (j + (-1)) (k + 0) = _
  simp [sub_eq_add_neg]

private theorem cubeDiffP_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffP f i j k =
      f i j k + f (i + 1) (j - 1) k := by
  change f i j k + f (i + 1) (j + (-1)) (k + 0) = _
  simp [sub_eq_add_neg]

private theorem cubeDiffR_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffR f i j k =
      f i j k + f i (j - 1) (k + 1) := by
  change f i j k + f (i + 0) (j + (-1)) (k + 1) = _
  simp [sub_eq_add_neg]

private theorem cubeDiffJStar_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffJStar f i j k = f i j k + f i (j + 1) k := by
  change f i j k + f (i + 0) (j + 1) (k + 0) = _
  simp

private theorem cubeDot_eq_iterated_sum
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot X Y =
      ∑ i : I n, ∑ j : I n, ∑ k : I n,
        X i j k * Y i j k := by
  simp only [cubeDot]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]

private theorem add_eq_zero_eq
    (a b : F) (h : a + b = 0) : a = b := by
  calc
    a = a + (b + b) := by rw [F_add_self, add_zero]
    _ = (a + b) + b := by abel
    _ = b := by rw [h, zero_add]

private theorem SSST_cross
    {n : Nat} [NeZero n] (A B : CyclicCube n)
    (hsrc : cubeDiffJInv A + cubeDiffP B = 0)
    (i j k : I n) :
    cubeDiffJStar (A + B) i j k = cubeDiffI B i j k := by
  have h :=
    congrFun (congrFun (congrFun hsrc i) (j + 1)) k
  simp only [Pi.add_apply, cubeDiffJInv_apply, cubeDiffP_apply,
    cubeDiffJStar_apply, cubeDiffI_apply, Pi.zero_apply] at h ⊢
  have hj : j + 1 - 1 = j := by abel
  rw [hj] at h
  apply add_eq_zero_eq
  calc
    ((A i j k + B i j k) + (A i (j + 1) k + B i (j + 1) k)) +
          (B i j k + B (i + 1) j k) =
        (A i (j + 1) k + A i j k +
          (B i (j + 1) k + B (i + 1) j k)) +
          (B i j k + B i j k) := by
            abel
    _ = 0 := by
      rw [h, F_add_self, zero_add]

private noncomputable def SSST_matrix
    {n : Nat} [NeZero n] (A B : CyclicCube n)
    (hsrc : cubeDiffJInv A + cubeDiffP B = 0)
    (k : I n) : MatrixZeroSum n :=
  ⟨fun j i => cubeDiffI B i j k, by
    constructor
    · apply LinearMap.mem_ker.mpr
      funext j
      change (∑ i : I n, cubeDiffI B i j k) = 0
      simp only [cubeDiffI_apply]
      rw [Finset.sum_add_distrib]
      rw [sum_shift (n := n) (1 : I n) (fun i => B i j k)]
      exact F_add_self _
    · apply LinearMap.mem_ker.mpr
      funext i
      change (∑ j : I n, cubeDiffI B i j k) = 0
      simp_rw [← SSST_cross A B hsrc i]
      simp only [cubeDiffJStar_apply]
      rw [Finset.sum_add_distrib]
      rw [sum_shift (n := n) (1 : I n) (fun j => (A + B) i j k)]
      exact F_add_self _⟩

private noncomputable def oddNormalize
    {n : Nat} [NeZero n] (hn : Odd n) (u : Profile n) :
    ZeroSumProfile n :=
  ⟨fun s => u s + ∑ t : I n, u t, by
    apply LinearMap.mem_ker.mpr
    change (∑ s : I n, (u s + ∑ t : I n, u t)) = 0
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    rw [show Fintype.card (I n) = n by simp [I, ZMod.card]]
    rw [nsmul_eq_mul, natCast_odd_eq_one_F hn, one_mul, F_add_self]⟩

private theorem SSST_inverseS
    {n : Nat} [NeZero n] (hn : Odd n)
    (A B : CyclicCube n)
    (hsrc : cubeDiffJInv A + cubeDiffP B = 0)
    (k j i : I n) :
    (oddMatrixInverseS hn (SSST_matrix A B hsrc k)).1 j i =
      B i j k + ∑ t : I n, B t j k := by
  let u : ZeroSumProfile n :=
    oddNormalize hn (fun t => B t j k)
  have hdiff :
      oddCyclicDiffRestrict (n := n) u =
        ⟨fun t => (SSST_matrix A B hsrc k).1 j t,
          matrix_row_zero (SSST_matrix A B hsrc k) j⟩ := by
    apply Subtype.ext
    funext t
    change
      (B t j k + ∑ r : I n, B r j k) +
          (B (t + 1) j k + ∑ r : I n, B r j k) =
        cubeDiffI B t j k
    rw [cubeDiffI_apply]
    calc
      (B t j k + ∑ r : I n, B r j k) +
          (B (t + 1) j k + ∑ r : I n, B r j k) =
        (B t j k + B (t + 1) j k) +
          ((∑ r : I n, B r j k) + ∑ r : I n, B r j k) := by
            abel
      _ = B t j k + B (t + 1) j k := by
        rw [F_add_self, add_zero]
  rw [oddMatrixInverseS_apply]
  rw [← hdiff, oddCyclicInverse_oddCyclicDiffRestrict]
  rfl

private theorem SSST_inverseJ
    {n : Nat} [NeZero n] (hn : Odd n)
    (A B : CyclicCube n)
    (hsrc : cubeDiffJInv A + cubeDiffP B = 0)
    (k j i : I n) :
    (oddMatrixInverseJ hn (SSST_matrix A B hsrc k)).1 j i =
      (A + B) i j k + ∑ t : I n, (A + B) i t k := by
  let u : ZeroSumProfile n :=
    oddNormalize hn (fun t => (A + B) i t k)
  have hdiff :
      oddCyclicDiffRestrict (n := n) u =
        ⟨fun t => (SSST_matrix A B hsrc k).1 t i,
          matrix_col_zero (SSST_matrix A B hsrc k) i⟩ := by
    apply Subtype.ext
    funext t
    change
      ((A + B) i t k + ∑ r : I n, (A + B) i r k) +
          ((A + B) i (t + 1) k + ∑ r : I n, (A + B) i r k) =
        cubeDiffI B i t k
    rw [← SSST_cross A B hsrc]
    rw [cubeDiffJStar_apply]
    calc
      ((A + B) i t k + ∑ r : I n, (A + B) i r k) +
          ((A + B) i (t + 1) k + ∑ r : I n, (A + B) i r k) =
        ((A + B) i t k + (A + B) i (t + 1) k) +
          ((∑ r : I n, (A + B) i r k) +
            ∑ r : I n, (A + B) i r k) := by
              abel
      _ = (A + B) i t k + (A + B) i (t + 1) k := by
        rw [F_add_self, add_zero]
  rw [oddMatrixInverseJ_apply]
  rw [← hdiff, oddCyclicInverse_oddCyclicDiffRestrict]
  rfl

private theorem SSST_pair_zero
    {n : Nat} [NeZero n] (hn : Odd n)
    (A B : CyclicCube n)
    (hsrc : cubeDiffJInv A + cubeDiffP B = 0) :
    cubeDot A (cubeDiffI B) = 0 := by
  rw [cubeDot_eq_iterated_sum]
  conv_lhs =>
    enter [2, i]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.sum_comm]
  have hq := oddOrbitQuadratic_eq_zero hn (SSST_matrix A B hsrc k)
  rw [← hq]
  simp only [oddOrbitQuadratic, oddMatrixDot,
    SSST_inverseS, SSST_inverseJ]
  rw [show
    (∑ j : I n, ∑ i : I n,
      (SSST_matrix A B hsrc k).1 j i *
        (B i j k + ∑ t : I n, B t j k)) =
      ∑ j : I n, ∑ i : I n,
        (SSST_matrix A B hsrc k).1 j i * B i j k by
      apply Finset.sum_congr rfl
      intro j _
      rw [show
        (∑ i : I n,
          (SSST_matrix A B hsrc k).1 j i *
            (B i j k + ∑ t : I n, B t j k)) =
          (∑ i : I n,
            (SSST_matrix A B hsrc k).1 j i * B i j k) +
          (∑ i : I n,
            (SSST_matrix A B hsrc k).1 j i) *
              (∑ t : I n, B t j k) by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, Finset.sum_mul]]
      rw [matrix_row_zero, zero_mul, add_zero]]
  rw [show
    (∑ j : I n, ∑ i : I n,
      (SSST_matrix A B hsrc k).1 j i *
        ((A + B) i j k + ∑ t : I n, (A + B) i t k)) =
      ∑ i : I n, ∑ j : I n,
        (SSST_matrix A B hsrc k).1 j i * (A + B) i j k by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [show
        (∑ j : I n,
          (SSST_matrix A B hsrc k).1 j i *
            ((A + B) i j k + ∑ t : I n, (A + B) i t k)) =
          (∑ j : I n,
            (SSST_matrix A B hsrc k).1 j i * (A + B) i j k) +
          (∑ j : I n,
            (SSST_matrix A B hsrc k).1 j i) *
              (∑ t : I n, (A + B) i t k) by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, Finset.sum_mul]]
      rw [matrix_col_zero, zero_mul, add_zero]]
  rw [Finset.sum_comm (f := fun i j =>
    (SSST_matrix A B hsrc k).1 j i * (A + B) i j k)]
  simp only [SSST_matrix, cubeDiffI_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

private theorem cubeDot_add_right
    {n : Nat} [NeZero n] (X Y Z : CyclicCube n) :
    cubeDot X (Y + Z) = cubeDot X Y + cubeDot X Z := by
  simp only [cubeDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem cubeDot_sum_left
    {n : Nat} [NeZero n] {T : Type*} [Fintype T]
    (X : T → CyclicCube n) (Y : CyclicCube n) :
    cubeDot (∑ t, X t) Y = ∑ t, cubeDot (X t) Y := by
  simp only [cubeDot, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem diamondOddPointedPhaseSSST_eq_zero
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn) :
    diamondOddPointedPhaseSSST x.1 = 0 := by
  let A : DiamondOddAxisTail n d → CyclicCube n :=
    fun wt =>
      x.1.1 diamondOddChannelS diamondOddChannelS
        (diamondOddChannelT wt)
  let B : DiamondOddAxisTail n d → CyclicCube n :=
    fun wt =>
      x.1.2.1 diamondOddChannelS diamondOddChannelS
        (diamondOddChannelT wt)
  have hsrc (wt : DiamondOddAxisTail n d) :
      cubeDiffJInv (A wt) + cubeDiffP (B wt) = 0 := by
    have hcoord :=
      congrFun
        (congrFun
          (congrFun (LinearMap.mem_ker.mp x.2) diamondOddChannelS)
          diamondOddChannelS)
        (diamondOddChannelT wt)
    rw [diamondOddPointedSourceMap_apply_SSST hn x.1 wt] at hcoord
    exact hcoord
  have hsum :
      cubeDiffJInv (∑ wt, A wt) +
          cubeDiffP (∑ wt, B wt) = 0 := by
    rw [map_sum, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun wt _ => hsrc wt)
  change
    (∑ wt : DiamondOddAxisTail n d,
      cubeDot (A wt)
        (cubeDiffI (diamondOddAxisTailJ (CyclicCube n) B wt))) = 0
  simp_rw [diamondOddAxisTailJ_apply, map_add, cubeDot_add_right]
  rw [Finset.sum_add_distrib]
  have hpoint :
      (∑ wt : DiamondOddAxisTail n d,
        cubeDot (A wt) (cubeDiffI (B wt))) = 0 :=
    Finset.sum_eq_zero
      (fun wt _ => SSST_pair_zero hn (A wt) (B wt) (hsrc wt))
  rw [hpoint, zero_add]
  rw [← cubeDot_sum_left]
  exact SSST_pair_zero hn (∑ wt, A wt) (∑ wt, B wt) hsum

private noncomputable def swapIK
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun i j k => f k j i
  invFun f := fun i j k => f k j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem swapIK_cubeDiffK
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffK f) = cubeDiffI (swapIK f) := by
  funext i j k
  rw [cubeDiffI_apply]
  change cubeDiffK f k j i = f k j i + f k j (i + 1)
  rw [cubeDiffK_apply]

private theorem swapIK_cubeDiffR
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffR f) = cubeDiffP (swapIK f) := by
  funext i j k
  rw [cubeDiffP_apply]
  change cubeDiffR f k j i =
    f k j i + f k (j - 1) (i + 1)
  rw [cubeDiffR_apply]

private theorem swapIK_cubeDiffJInv
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffJInv f) =
      cubeDiffJInv (swapIK f) := by
  funext i j k
  rw [cubeDiffJInv_apply]
  change cubeDiffJInv f k j i = f k j i + f k (j - 1) i
  rw [cubeDiffJInv_apply]

private def indexSwapIK {n : Nat} :
    (I n × I n × I n) ≃ (I n × I n × I n) where
  toFun q := (q.2.2, (q.2.1, q.1))
  invFun q := (q.2.2, (q.2.1, q.1))
  left_inv q := by
    rcases q with ⟨i, ⟨j, k⟩⟩
    rfl
  right_inv q := by
    rcases q with ⟨i, ⟨j, k⟩⟩
    rfl

private theorem cubeDot_swap_both
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot (swapIK X) (swapIK Y) = cubeDot X Y := by
  rw [cubeDot, cubeDot]
  apply Fintype.sum_equiv indexSwapIK
  intro q
  rfl

private theorem STSS_pair_zero
    {n : Nat} [NeZero n] (hn : Odd n)
    (A W : CyclicCube n)
    (hsrc : cubeDiffJInv A + cubeDiffR W = 0) :
    cubeDot A (cubeDiffK W) = 0 := by
  have hsrc' :
      cubeDiffJInv (swapIK A) +
          cubeDiffP (swapIK W) = 0 := by
    rw [← swapIK_cubeDiffJInv, ← swapIK_cubeDiffR,
      ← map_add, hsrc, map_zero]
  have hz :=
    SSST_pair_zero hn (swapIK A) (swapIK W) hsrc'
  rw [← swapIK_cubeDiffK, cubeDot_swap_both] at hz
  exact hz

theorem diamondOddPointedPhaseSTSS_eq_zero
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn) :
    diamondOddPointedPhaseSTSS x.1 = 0 := by
  let A : DiamondOddAxisTail n b → CyclicCube n :=
    fun yt =>
      x.1.1 (diamondOddChannelT yt) diamondOddChannelS
        diamondOddChannelS
  let W : DiamondOddAxisTail n b → CyclicCube n :=
    fun yt =>
      x.1.2.2 diamondOddChannelS (diamondOddChannelT yt)
        diamondOddChannelS
  have hsrc (yt : DiamondOddAxisTail n b) :
      cubeDiffJInv (A yt) + cubeDiffR (W yt) = 0 := by
    have hcoord :=
      congrFun
        (congrFun
          (congrFun (LinearMap.mem_ker.mp x.2) diamondOddChannelS)
          (diamondOddChannelT yt))
        diamondOddChannelS
    rw [diamondOddPointedSourceMap_apply_STSS hn x.1 yt] at hcoord
    exact hcoord
  have hsum :
      cubeDiffJInv (∑ yt, A yt) +
          cubeDiffR (∑ yt, W yt) = 0 := by
    rw [map_sum, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun yt _ => hsrc yt)
  change
    (∑ yt : DiamondOddAxisTail n b,
      cubeDot (A yt)
        (cubeDiffK (diamondOddAxisTailJ (CyclicCube n) W yt))) = 0
  simp_rw [diamondOddAxisTailJ_apply, map_add, cubeDot_add_right]
  rw [Finset.sum_add_distrib]
  have hpoint :
      (∑ yt : DiamondOddAxisTail n b,
        cubeDot (A yt) (cubeDiffK (W yt))) = 0 :=
    Finset.sum_eq_zero
      (fun yt _ => STSS_pair_zero hn (A yt) (W yt) (hsrc yt))
  rw [hpoint, zero_add]
  rw [← cubeDot_sum_left]
  exact STSS_pair_zero hn (∑ yt, A yt) (∑ yt, W yt) hsum

end

end Core4loop.SquareDiagonal.DirectWitt
