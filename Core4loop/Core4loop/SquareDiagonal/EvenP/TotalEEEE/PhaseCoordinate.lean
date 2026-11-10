import Core4loop.SquareDiagonal.EvenP.TotalEEEE.RightReachable
import Core4loop.SquareDiagonal.EvenP.TotalEEOE.PhaseCoordinate

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 2000000
set_option maxSynthPendingDepth 2048

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEEEEPhase

/-! ## The common literal three-axis gauge -/

private theorem cubeDot_comm
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot X Y = cubeDot Y X := by
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  ring

@[simp] private theorem cubeDot_zero_left
    {n : Nat} [NeZero n] (X : CyclicCube n) :
    cubeDot (0 : CyclicCube n) X = 0 := by
  unfold cubeDot
  simp

private theorem prod_add_components
    {U V : Type*} [Add U] [Add V] (x y : U × V) :
    x + y = (x.1 + y.1, x.2 + y.2) := by
  cases x
  cases y
  rfl

theorem cubeIJKShift_pairing_same
    {n : Nat} [NeZero n]
    (u v w : I n) (X Y : CyclicCube n) :
    cubeDot
        (TotalEEEERightInternal.cubeIJKShiftEquiv u v w X)
        (TotalEEEERightInternal.cubeIJKShiftEquiv u v w Y) =
      cubeDot X Y := by
  classical
  unfold cubeDot
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.addRight (-u))
      (Equiv.prodCongr (Equiv.addRight (-v))
        (Equiv.addRight (-w)))
  apply Fintype.sum_equiv e
  intro q
  simp [e, TotalEEEERightInternal.cubeIJKShiftEquiv,
    sub_eq_add_neg]

theorem cubeIJKShift_cubeDiffI
    {n : Nat} [NeZero n]
    (u v w : I n) (X : CyclicCube n) :
    TotalEEEERightInternal.cubeIJKShiftEquiv u v w (cubeDiffI X) =
      cubeDiffI
        (TotalEEEERightInternal.cubeIJKShiftEquiv u v w X) := by
  funext i j k
  simp only [TotalEEEERightInternal.cubeIJKShiftEquiv_apply,
    EEOEInternal.cubeDiffI_apply]
  congr 2
  ring

theorem cubeIJKShift_cubeDiffK
    {n : Nat} [NeZero n]
    (u v w : I n) (X : CyclicCube n) :
    TotalEEEERightInternal.cubeIJKShiftEquiv u v w (cubeDiffK X) =
      cubeDiffK
        (TotalEEEERightInternal.cubeIJKShiftEquiv u v w X) := by
  funext i j k
  simp only [TotalEEEERightInternal.cubeIJKShiftEquiv_apply,
    EEOEInternal.cubeDiffK_apply]
  congr 2
  abel

theorem cubeIJKShift_leftRoot
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (l : DiamondEvenPLeft n b c d)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d) :
    TotalEEEERightInternal.cubeIJKShiftEquiv
        (vecSum yt) (vecSum zt) (vecSum wt)
        (diamondARootCubeEquiv hb hc hd
          (diamondEvenPLeftRoot l) yt zt wt) =
      cubeDiffI
          ((TotalEEEEInternal.literalGaugeEquiv
            hb hc hd l.1).1 zt wt) +
        cubeDiffK
          ((TotalEEEEInternal.literalGaugeEquiv
            hb hc hd l.1).2 yt zt) := by
  funext i j k
  simp only [TotalEEEERightInternal.cubeIJKShiftEquiv_apply,
    Pi.add_apply]
  change
    diamondEvenPLeftRoot l
        ((diamondVecHeadTailEquiv hb).symm
          (i - vecSum yt, yt))
        ((diamondVecHeadTailEquiv hc).symm
          (j - vecSum zt, zt))
        ((diamondVecHeadTailEquiv hd).symm
          (k - vecSum wt, wt)) =
      _
  rw [diamondCubeReindex_leftRoot hb hc hd l yt zt wt
    (i - vecSum yt) (j - vecSum zt) (k - vecSum wt)]
  change
    cubeDiffI
        (diamondBRootCubeEquiv hc hd l.1.1 zt wt)
        ((i - vecSum yt) + vecSum yt)
        (j - vecSum zt) (k - vecSum wt) +
      cubeDiffK
        (diamondWRootCubeEquiv hb hc l.1.2 yt zt)
        (i - vecSum yt) (j - vecSum zt)
        ((k - vecSum wt) + vecSum wt) =
    cubeDiffI
        (TotalEOEEInternal.cubeJKShiftEquiv
          (vecSum zt) (vecSum wt)
          (diamondBRootCubeEquiv hc hd l.1.1 zt wt))
        i j k +
      cubeDiffK
        (TotalEEEEInternal.cubeIJShiftEquiv
          (vecSum yt) (vecSum zt)
          (diamondWRootCubeEquiv hb hc l.1.2 yt zt))
        i j k
  simp only [sub_add_cancel,
    EEOEInternal.cubeDiffI_apply,
    EEOEInternal.cubeDiffK_apply,
    TotalEOEEInternal.cubeJKShiftEquiv_apply,
    TotalEEEEInternal.cubeIJShiftEquiv]
  congr 1

theorem totalEEEELiteralPhaseGauged
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (l : DiamondEvenPLeft n b c d)
    (A : DiamondEvenPReachableA n b c d) :
    diamondEvenPCross l A =
      ∑ yt : PVec n b, ∑ zt : PVec n c, ∑ wt : PVec n d,
        cubeDot
          (cubeDiffI
              ((TotalEEEEInternal.literalGaugeEquiv
                hb hc hd l.1).1 zt wt) +
            cubeDiffK
              ((TotalEEEEInternal.literalGaugeEquiv
                hb hc hd l.1).2 yt zt))
          (TotalEEEERightInternal.aLiteralGaugeEquiv
            hb hc hd A.1 yt zt wt) := by
  change coeffApplyA (diamondEvenPLeftRoot l) A.1 = _
  rw [diamondCubeReindex_rootPairing hb hc hd]
  apply Finset.sum_congr rfl
  intro yt _
  apply Finset.sum_congr rfl
  intro zt _
  apply Finset.sum_congr rfl
  intro wt _
  let u := vecSum yt
  let v := vecSum zt
  let w := vecSum wt
  let AR :=
    diamondARootCubeEquiv hb hc hd A.1 yt zt wt
  let LR :=
    diamondARootCubeEquiv hb hc hd
      (diamondEvenPLeftRoot l) yt zt wt
  calc
    cubeDot AR LR =
        cubeDot
          (TotalEEEERightInternal.cubeIJKShiftEquiv u v w AR)
          (TotalEEEERightInternal.cubeIJKShiftEquiv u v w LR) :=
      (cubeIJKShift_pairing_same u v w AR LR).symm
    _ =
        cubeDot
          (TotalEEEERightInternal.aLiteralGaugeEquiv
            hb hc hd A.1 yt zt wt)
          (cubeDiffI
              ((TotalEEEEInternal.literalGaugeEquiv
                hb hc hd l.1).1 zt wt) +
            cubeDiffK
              ((TotalEEEEInternal.literalGaugeEquiv
                hb hc hd l.1).2 yt zt)) := by
      rw [show
          TotalEEEERightInternal.cubeIJKShiftEquiv u v w AR =
            TotalEEEERightInternal.aLiteralGaugeEquiv
              hb hc hd A.1 yt zt wt from rfl]
      rw [show
          TotalEEEERightInternal.cubeIJKShiftEquiv u v w LR =
            cubeDiffI
                ((TotalEEEEInternal.literalGaugeEquiv
                  hb hc hd l.1).1 zt wt) +
              cubeDiffK
                ((TotalEEEEInternal.literalGaugeEquiv
                  hb hc hd l.1).2 yt zt) from
        cubeIJKShift_leftRoot hb hc hd l yt zt wt]
    _ = _ := cubeDot_comm _ _

/-! ## Complete-`Z` bilinear splitting and the D/E head shear -/

noncomputable abbrev RawZLeft
    (n b d : Nat) [NeZero n] :=
  (PVec n d → CyclicCube n) ×
    (PVec n b → CyclicCube n)

noncomputable abbrev RawZRight
    (n b d : Nat) [NeZero n] :=
  PVec n b → PVec n d → CyclicCube n

def rawZLocalPhase
    {n b d : Nat} [NeZero n]
    (u : RawZLeft n b d) (v : RawZRight n b d) : F :=
  T37PhaseD.dT37GaugedPhase u.1 u.2 v

noncomputable def literalOuterZLeftFamily
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (l : DiamondEvenPLeft n b c d) :
    PVec n c → RawZLeft n b d :=
  fun zt =>
    ((TotalEEEEInternal.literalGaugeEquiv hb hc hd l.1).1 zt,
      fun yt =>
        (TotalEEEEInternal.literalGaugeEquiv hb hc hd l.1).2 yt zt)

noncomputable def literalOuterZRightFamily
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : DiamondEvenPReachableA n b c d) :
    PVec n c → RawZRight n b d :=
  fun zt yt wt =>
    TotalEEEERightInternal.aLiteralGaugeEquiv
      hb hc hd A.1 yt zt wt

private theorem srcCoord_prod_fst
    {n k : Nat} [NeZero n]
    (hn : Even n) (hk2 : 2 ≤ k)
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (f : PVec n k → U × V) :
    let x :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := k) (U × V) hn hk2 f
    let y :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := k) U hn hk2 (fun s => (f s).1)
    (x.1.1.1 = y.1.1 ∧ x.1.2.1 = y.1.2) ∧
      ∀ t : DiamondEvenAxisTailIndex n k,
        (x.2.1 t).1 = y.2.1 t := by
  simp only [diamondEvenAxisSrcCoordEquiv,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K,
    pointedSrcEvenValueEquiv_apply_tail]
  constructor
  · constructor <;> simp only [Prod.fst_sum]
  · intro t
    simp only [Prod.fst_add, Prod.fst_sum]

private theorem srcCoord_prod_snd
    {n k : Nat} [NeZero n]
    (hn : Even n) (hk2 : 2 ≤ k)
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (f : PVec n k → U × V) :
    let x :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := k) (U × V) hn hk2 f
    let y :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := k) V hn hk2 (fun s => (f s).2)
    (x.1.1.2 = y.1.1 ∧ x.1.2.2 = y.1.2) ∧
      ∀ t : DiamondEvenAxisTailIndex n k,
        (x.2.1 t).2 = y.2.1 t := by
  simp only [diamondEvenAxisSrcCoordEquiv,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K,
    pointedSrcEvenValueEquiv_apply_tail]
  constructor
  · constructor <;> simp only [Prod.snd_sum]
  · intro t
    simp only [Prod.snd_add, Prod.snd_sum]

private theorem pointedSrcEvenValueEquiv_map_sigma
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S))
    (e : U →ₗ[F] V) (f : S → U) :
    e ((pointedSrcEvenValueEquiv S U s0 heven f).1.1) =
      (pointedSrcEvenValueEquiv S V s0 heven
        (fun s => e (f s))).1.1 := by
  simp only [pointedSrcEvenValueEquiv_apply_sigma, map_sum]

private theorem pointedSrcEvenValueEquiv_map_K
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S))
    (e : U →ₗ[F] V) (f : S → U) :
    e ((pointedSrcEvenValueEquiv S U s0 heven f).1.2) =
      (pointedSrcEvenValueEquiv S V s0 heven
        (fun s => e (f s))).1.2 := by
  simp only [pointedSrcEvenValueEquiv_apply_K, map_sum]

private theorem pointedSrcEvenValueEquiv_map_tail
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S))
    (e : U →ₗ[F] V) (f : S → U)
    (t : PointedTail S s0) :
    e ((pointedSrcEvenValueEquiv S U s0 heven f).2.1 t) =
      (pointedSrcEvenValueEquiv S V s0 heven
        (fun s => e (f s))).2.1 t := by
  simp only [pointedSrcEvenValueEquiv_apply_tail, map_add, map_sum]

private noncomputable def nestedSrcRead
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

private theorem bNestedCoords_eq_nestedSrcRead
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (B : BFun4 n 1 c d) :
    TotalEEEEInternal.bNestedCoords hn hc2 hd2 B =
      nestedSrcRead
        (PVec n c) (PVec n d) (CyclicCube n)
        (zeroVec : PVec n c) (zeroVec : PVec n d)
        (even_card_PVec hn hc2) (even_card_PVec hn hd2)
        (TotalEOEEInternal.bGaugedRootFamilyEquiv
          (by omega : 0 < c) (by omega : 0 < d) B) := by
  rfl

private theorem wNestedCoords_eq_nestedSrcRead
    {n b c : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (W : WFun4 n 1 b c) :
    TotalEEEEInternal.wNestedCoords hn hb2 hc2 W =
      nestedSrcRead
        (PVec n b) (PVec n c) (CyclicCube n)
        (zeroVec : PVec n b) (zeroVec : PVec n c)
        (even_card_PVec hn hb2) (even_card_PVec hn hc2)
        (TotalEEEEInternal.wGaugedYZFamilyEquiv
          (by omega : 0 < b) (by omega : 0 < c) W) := by
  rfl

private theorem totalEEEELeftAmbientCoords_ZTail_apply
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 b c)
    (zt : DiamondEvenAxisTailIndex n c) :
    (TotalEEEEInternal.totalEEEELeftAmbientCoords
      hn hb2 hc2 hd2 x).2.2.2.1.1 zt =
      (((TotalEEEEInternal.bNestedCoords hn hc2 hd2 x.1).2.2.1.1 zt),
        ((TotalEEEEInternal.wNestedCoords hn hb2 hc2 x.2).2.1.1 zt)) := by
  rfl

private noncomputable def rawOuterZLeftCoords
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (_hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (_hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d) :
    PointedEvenValueCoords
      (PVec n c) (RawZLeft n b d) (zeroVec : PVec n c) :=
  diamondEvenAxisSrcCoordEquiv
    (n := n) (k := c) (RawZLeft n b d) hn hc2
    (literalOuterZLeftFamily
      (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d) l)

private noncomputable def rawInnerBCoords
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (u : RawZLeft n b d) :
    PointedEvenValueCoords
      (PVec n d) (CyclicCube n) (zeroVec : PVec n d) :=
  diamondEvenAxisSrcCoordEquiv
    (n := n) (k := d) (CyclicCube n) hn hd2 u.1

private noncomputable def rawInnerWCoords
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b)
    (u : RawZLeft n b d) :
    PointedEvenValueCoords
      (PVec n b) (CyclicCube n) (zeroVec : PVec n b) :=
  diamondEvenAxisSrcCoordEquiv
    (n := n) (k := b) (CyclicCube n) hn hb2 u.2

private theorem rawInnerBCoords_add
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (u v : RawZLeft n b d) :
    rawInnerBCoords hn hd2 (u + v) =
      rawInnerBCoords hn hd2 u + rawInnerBCoords hn hd2 v := by
  simpa only [rawInnerBCoords, Prod.fst_add] using
    (diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2).map_add u.1 v.1

private theorem rawInnerWCoords_add
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b)
    (u v : RawZLeft n b d) :
    rawInnerWCoords hn hb2 (u + v) =
      rawInnerWCoords hn hb2 u + rawInnerWCoords hn hb2 v := by
  simpa only [rawInnerWCoords, Prod.snd_add] using
    (diamondEvenAxisSrcCoordEquiv
      (n := n) (k := b) (CyclicCube n) hn hb2).map_add u.2 v.2

private noncomputable def frozenLeftCoords
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d) :
    TotalEEEELeftSourceTarget n b c d :=
  diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 l

private theorem frozenLeft_scalar_eq_rawOuter
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d) :
    let x := rawOuterZLeftCoords hn hb2 hc2 hd2 l
    let q := frozenLeftCoords hn hb2 hc2 hd2 l
    q.1.1 =
      (((rawInnerBCoords hn hd2 x.1.1).1,
          (rawInnerBCoords hn hd2 x.1.2).1),
        (((rawInnerWCoords hn hb2 x.1.1).1.1,
            (rawInnerWCoords hn hb2 x.1.2).1.1),
          ((rawInnerWCoords hn hb2 x.1.1).1.2,
            (rawInnerWCoords hn hb2 x.1.2).1.2))) := by
  dsimp only
  change
    (TotalEEEEInternal.totalEEEELeftAmbientCoords
      hn hb2 hc2 hd2 l.1).1 = _
  rw [TotalEEEEInternal.totalEEEELeftAmbientCoords_scalar]
  apply Prod.ext
  · rw [bNestedCoords_eq_nestedSrcRead]
    simp [nestedSrcRead, rawInnerBCoords, rawOuterZLeftCoords,
      diamondEvenAxisSrcCoordEquiv, literalOuterZLeftFamily,
      TotalEEEEInternal.literalGaugeEquiv,
      LinearEquiv.prodCongr_apply, Prod.fst_sum, Prod.snd_sum,
      pointedSrcEvenValueEquiv_apply_sigma,
      pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply]
  · rw [wNestedCoords_eq_nestedSrcRead]
    simp [nestedSrcRead, rawInnerWCoords, rawOuterZLeftCoords,
      diamondEvenAxisSrcCoordEquiv, literalOuterZLeftFamily,
      TotalEEEEInternal.literalGaugeEquiv,
      LinearEquiv.prodCongr_apply, Prod.fst_sum, Prod.snd_sum,
      pointedSrcEvenValueEquiv_apply_sigma,
      pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply]
    constructor <;> apply Prod.ext <;>
      simp only [pointedSrcEvenValueEquiv_apply_sigma,
        pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply] <;>
      exact Finset.sum_comm

private theorem frozenLeft_Y_eq_rawOuter
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (yt : DiamondEvenAxisTailIndex n b) :
    let x := rawOuterZLeftCoords hn hb2 hc2 hd2 l
    let q := frozenLeftCoords hn hb2 hc2 hd2 l
    (((q.2.1.1 yt).1.1), (q.2.1.1 yt).2) =
      ((rawInnerWCoords hn hb2 x.1.1).2.1 yt,
        (rawInnerWCoords hn hb2 x.1.2).2.1 yt) := by
  dsimp only
  change
    (((TotalEEEEInternal.totalEEEELeftAmbientCoords
        hn hb2 hc2 hd2 l.1).2.1.1 yt).1,
      ((TotalEEEEInternal.totalEEEELeftAmbientCoords
        hn hb2 hc2 hd2 l.1).2.1.1 yt).2) = _
  rw [TotalEEEEInternal.totalEEEELeftAmbientCoords_YTail,
    wNestedCoords_eq_nestedSrcRead]
  simp [nestedSrcRead, rawInnerWCoords, rawOuterZLeftCoords,
    diamondEvenAxisSrcCoordEquiv, literalOuterZLeftFamily,
    TotalEEEEInternal.literalGaugeEquiv,
    LinearEquiv.prodCongr_apply, Prod.fst_sum, Prod.snd_sum,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K,
    pointedSrcEvenValueEquiv_apply_tail,
    Finset.sum_apply]
  constructor <;> rw [Finset.sum_add_distrib] <;>
    congr 1 <;> exact Finset.sum_comm

private theorem frozenLeft_W_eq_rawOuter
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (wt : DiamondEvenAxisTailIndex n d) :
    let x := rawOuterZLeftCoords hn hb2 hc2 hd2 l
    let q := frozenLeftCoords hn hb2 hc2 hd2 l
    (((q.2.2.1.1 wt).1.1), (q.2.2.1.1 wt).2) =
      ((rawInnerBCoords hn hd2 x.1.1).2.1 wt,
        (rawInnerBCoords hn hd2 x.1.2).2.1 wt) := by
  dsimp only
  change
    (((TotalEEEEInternal.totalEEEELeftAmbientCoords
        hn hb2 hc2 hd2 l.1).2.2.1.1 wt).1,
      ((TotalEEEEInternal.totalEEEELeftAmbientCoords
        hn hb2 hc2 hd2 l.1).2.2.1.1 wt).2) = _
  rw [TotalEEEEInternal.totalEEEELeftAmbientCoords_WTail,
    bNestedCoords_eq_nestedSrcRead]
  simp [nestedSrcRead, rawInnerBCoords, rawOuterZLeftCoords,
    diamondEvenAxisSrcCoordEquiv, literalOuterZLeftFamily,
    TotalEEEEInternal.literalGaugeEquiv,
    LinearEquiv.prodCongr_apply, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_apply]

private theorem frozenLeft_Z_eq_rawOuter
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (zt : DiamondEvenAxisTailIndex n c) :
    let x := rawOuterZLeftCoords hn hb2 hc2 hd2 l
    let q := frozenLeftCoords hn hb2 hc2 hd2 l
    q.2.2.2.1.1 zt =
      ((rawInnerBCoords hn hd2 (x.2.1 zt)).1,
        (rawInnerWCoords hn hb2 (x.2.1 zt)).1) := by
  dsimp only
  change
    (TotalEEEEInternal.totalEEEELeftAmbientCoords
      hn hb2 hc2 hd2 l.1).2.2.2.1.1 zt = _
  rw [totalEEEELeftAmbientCoords_ZTail_apply,
    bNestedCoords_eq_nestedSrcRead,
    wNestedCoords_eq_nestedSrcRead]
  simp [nestedSrcRead, rawInnerBCoords, rawInnerWCoords,
    rawOuterZLeftCoords, diamondEvenAxisSrcCoordEquiv,
    literalOuterZLeftFamily, TotalEEEEInternal.literalGaugeEquiv,
    LinearEquiv.prodCongr_apply, Prod.fst_sum, Prod.snd_sum,
    TotalEOEEInternal.TailCoordHelpers.tailZeroCongr,
    TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K,
    pointedSrcEvenValueEquiv_apply_tail,
    Finset.sum_apply]
  apply Prod.ext
  · simp only [pointedSrcEvenValueEquiv_apply_sigma,
      Pi.add_apply, Finset.sum_add_distrib, Finset.sum_apply]
    congr 1
    exact Finset.sum_comm
  · simp only [pointedSrcEvenValueEquiv_apply_K,
      Pi.add_apply, Finset.sum_add_distrib, Finset.sum_apply]
    congr 1
    exact Finset.sum_comm

private theorem frozenLeft_YZ_eq_rawOuter
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (yt : DiamondEvenAxisTailIndex n b)
    (zt : DiamondEvenAxisTailIndex n c) :
    let x := rawOuterZLeftCoords hn hb2 hc2 hd2 l
    let q := frozenLeftCoords hn hb2 hc2 hd2 l
    ((q.2.2.2.2.1.1 yt).1 zt) =
      (rawInnerWCoords hn hb2 (x.2.1 zt)).2.1 yt := by
  dsimp only
  change
    ((TotalEEEEInternal.totalEEEELeftAmbientCoords
      hn hb2 hc2 hd2 l.1).2.2.2.2.1.1 yt).1 zt = _
  rw [TotalEEEEInternal.totalEEEELeftAmbientCoords_YZTail,
    wNestedCoords_eq_nestedSrcRead]
  simp [nestedSrcRead, rawInnerWCoords, rawOuterZLeftCoords,
    diamondEvenAxisSrcCoordEquiv, literalOuterZLeftFamily,
    TotalEEEEInternal.literalGaugeEquiv,
    LinearEquiv.prodCongr_apply, Prod.fst_sum, Prod.snd_sum,
    TotalEOEEInternal.TailCoordHelpers.tailZeroCongr,
    TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K,
    pointedSrcEvenValueEquiv_apply_tail,
    Finset.sum_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  abel

private theorem frozenLeft_WZ_eq_rawOuter
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (zt : DiamondEvenAxisTailIndex n c)
    (wt : DiamondEvenAxisTailIndex n d) :
    let x := rawOuterZLeftCoords hn hb2 hc2 hd2 l
    let q := frozenLeftCoords hn hb2 hc2 hd2 l
    ((q.2.2.2.2.2.1.1 zt).1 wt) =
      (rawInnerBCoords hn hd2 (x.2.1 zt)).2.1 wt := by
  dsimp only
  change
    (((TotalEEEEInternal.totalEEEELeftAmbientCoords
      hn hb2 hc2 hd2 l.1).2.2.2.2.2).1 zt).1 wt = _
  rw [TotalEEEEInternal.totalEEEELeftAmbientCoords_WZTail,
    bNestedCoords_eq_nestedSrcRead]
  simp [nestedSrcRead, rawInnerBCoords, rawOuterZLeftCoords,
    diamondEvenAxisSrcCoordEquiv, literalOuterZLeftFamily,
    TotalEEEEInternal.literalGaugeEquiv,
    LinearEquiv.prodCongr_apply, Prod.fst_sum, Prod.snd_sum,
    TotalEOEEInternal.TailCoordHelpers.tailZeroCongr,
    TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K,
    pointedSrcEvenValueEquiv_apply_tail,
    Finset.sum_apply]

private theorem frozenLeft_Y_first_eq_rawOuter
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (yt : DiamondEvenAxisTailIndex n b) :
    (((frozenLeftCoords hn hb2 hc2 hd2 l).2.1.1 yt).1.1) =
      (rawInnerWCoords hn hb2
        (rawOuterZLeftCoords hn hb2 hc2 hd2 l).1.1).2.1 yt :=
  congrArg Prod.fst
    (frozenLeft_Y_eq_rawOuter hn hb2 hc2 hd2 l yt)

private theorem frozenLeft_Y_second_eq_rawOuter
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (yt : DiamondEvenAxisTailIndex n b) :
    ((frozenLeftCoords hn hb2 hc2 hd2 l).2.1.1 yt).2 =
      (rawInnerWCoords hn hb2
        (rawOuterZLeftCoords hn hb2 hc2 hd2 l).1.2).2.1 yt :=
  congrArg Prod.snd
    (frozenLeft_Y_eq_rawOuter hn hb2 hc2 hd2 l yt)

private theorem frozenLeft_W_first_eq_rawOuter
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (wt : DiamondEvenAxisTailIndex n d) :
    (((frozenLeftCoords hn hb2 hc2 hd2 l).2.2.1.1 wt).1.1) =
      (rawInnerBCoords hn hd2
        (rawOuterZLeftCoords hn hb2 hc2 hd2 l).1.1).2.1 wt :=
  congrArg Prod.fst
    (frozenLeft_W_eq_rawOuter hn hb2 hc2 hd2 l wt)

private theorem frozenLeft_W_second_eq_rawOuter
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (wt : DiamondEvenAxisTailIndex n d) :
    ((frozenLeftCoords hn hb2 hc2 hd2 l).2.2.1.1 wt).2 =
      (rawInnerBCoords hn hd2
        (rawOuterZLeftCoords hn hb2 hc2 hd2 l).1.2).2.1 wt :=
  congrArg Prod.snd
    (frozenLeft_W_eq_rawOuter hn hb2 hc2 hd2 l wt)

noncomputable def rawZLocalCross
    {n b d : Nat} [NeZero n] :
    RawZLeft n b d →ₗ[F] Module.Dual F (RawZRight n b d) :=
  LinearMap.mk₂ F rawZLocalPhase
    (by
      intro u u' v
      simp only [rawZLocalPhase, T37PhaseD.dT37GaugedPhase,
        Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add,
        EEOEInternal.cubeDot_add_left, Finset.sum_add_distrib]
      abel)
    (by
      intro r u v
      simp only [rawZLocalPhase, T37PhaseD.dT37GaugedPhase,
        Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro yt _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro wt _
      rw [← smul_add]
      exact EEOEInternal.cubeDot_smul_left _ _ _)
    (by
      intro u v v'
      simp only [rawZLocalPhase, T37PhaseD.dT37GaugedPhase,
        Pi.add_apply, EEOEInternal.cubeDot_add_right,
        Finset.sum_add_distrib])
    (by
      intro r u v
      simp only [rawZLocalPhase, T37PhaseD.dT37GaugedPhase,
        Pi.smul_apply, EEOEInternal.cubeDot_smul_right]
      simp_rw [Finset.smul_sum])

@[simp] theorem rawZLocalCross_apply
    {n b d : Nat} [NeZero n]
    (u : RawZLeft n b d) (v : RawZRight n b d) :
    rawZLocalCross u v = rawZLocalPhase u v :=
  rfl

theorem rawOuterZPairing
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c)
    (f : PVec n c → RawZLeft n b d)
    (g : PVec n c → RawZRight n b d) :
    let x :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c) (RawZLeft n b d) hn hc2 f
    let y :=
      diamondEvenAxisDualCoordEquiv
        (n := n) (k := c) (RawZRight n b d) hn hc2 g
    (∑ zt : PVec n c, rawZLocalPhase (f zt) (g zt)) =
      rawZLocalPhase x.1.1 y.1.1 +
        rawZLocalPhase x.1.2 y.1.2 +
        ∑ zt : DiamondEvenAxisTailIndex n c,
          rawZLocalPhase (x.2.1 zt) (y.2.1 zt) := by
  dsimp only
  simpa only [rawZLocalCross_apply] using
    pointedEvenValue_pairing
      (zeroVec : PVec n c)
      (even_card_PVec hn hc2)
      (rawZLocalCross (n := n) (b := b) (d := d)) f g

theorem rawZLocalPhase_headShear
    {n b d : Nat} [NeZero n]
    (x₀ x₁ : RawZLeft n b d)
    (y₀ y₁ : RawZRight n b d) :
    rawZLocalPhase x₀ y₀ + rawZLocalPhase x₁ y₁ =
      rawZLocalPhase (x₀ + x₁) y₁ +
        rawZLocalPhase x₀ (Add.add y₀ y₁) := by
  have hleft :
      rawZLocalPhase (x₀ + x₁) y₁ =
        rawZLocalPhase x₀ y₁ + rawZLocalPhase x₁ y₁ := by
    change
      rawZLocalCross (x₀ + x₁) y₁ =
        rawZLocalCross x₀ y₁ + rawZLocalCross x₁ y₁
    rw [map_add]
    rfl
  have hright :
      rawZLocalPhase x₀ (Add.add y₀ y₁) =
        rawZLocalPhase x₀ y₀ + rawZLocalPhase x₀ y₁ := by
    change
      rawZLocalCross x₀ (Add.add y₀ y₁) =
        rawZLocalCross x₀ y₀ + rawZLocalCross x₀ y₁
    exact map_add (rawZLocalCross x₀) y₀ y₁
  rw [hleft, hright]
  abel_nf
  simp only [two_smul, F_add_self, add_zero]

theorem rawOuterZPairingSheared
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c)
    (f : PVec n c → RawZLeft n b d)
    (g : PVec n c → RawZRight n b d) :
    let x :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c) (RawZLeft n b d) hn hc2 f
    let y :=
      (TotalEOEEInternal.pointedHeadShear
        (zeroVec : PVec n c))
        (diamondEvenAxisDualCoordEquiv
          (n := n) (k := c) (RawZRight n b d) hn hc2 g)
    (∑ zt : PVec n c, rawZLocalPhase (f zt) (g zt)) =
      rawZLocalPhase (x.1.1 + x.1.2) y.1.1 +
        rawZLocalPhase x.1.1 y.1.2 +
        ∑ zt : DiamondEvenAxisTailIndex n c,
          rawZLocalPhase (x.2.1 zt) (y.2.1 zt) := by
  dsimp only
  rw [rawOuterZPairing hn hc2 f g]
  rw [rawZLocalPhase_headShear]
  rfl

def t37AmbientLedgerPhase
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (u : RawZLeft n b d)
    (q : T37RightP1.T37RightAmbientTarget n b d) : F :=
  EEOEInternal.ambientPhase
      (diamondEEOECoeffMap
        (((diamondEvenAxisSrcCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2 u.1).1,
          (diamondEvenAxisSrcCoordEquiv
            (n := n) (k := b) (CyclicCube n) hn hb2 u.2).1)))
      q.1 +
    (∑ yt : DiamondEvenAxisTailIndex n b,
      cubeDot
        (cubeDiffK
          ((diamondEvenAxisSrcCoordEquiv
            (n := n) (k := b) (CyclicCube n) hn hb2 u.2).2.1 yt))
        (q.2.1.1 yt).1) +
    ∑ wt : DiamondEvenAxisTailIndex n d,
      cubeDot
        (cubeDiffI
          ((diamondEvenAxisSrcCoordEquiv
            (n := n) (k := d) (CyclicCube n) hn hd2 u.1).2.1 wt))
        (q.2.2.1.1 wt).1

private theorem t37AmbientLedgerPhase_eq_rawInner
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (u : RawZLeft n b d)
    (q : T37RightP1.T37RightAmbientTarget n b d) :
    t37AmbientLedgerPhase hn hb2 hd2 u q =
      EEOEInternal.ambientPhase
          (diamondEEOECoeffMap
            ((rawInnerBCoords hn hd2 u).1,
              (rawInnerWCoords hn hb2 u).1))
          q.1 +
        (∑ yt : DiamondEvenAxisTailIndex n b,
          cubeDot
            (cubeDiffK ((rawInnerWCoords hn hb2 u).2.1 yt))
            (q.2.1.1 yt).1) +
        ∑ wt : DiamondEvenAxisTailIndex n d,
          cubeDot
            (cubeDiffI ((rawInnerBCoords hn hd2 u).2.1 wt))
            (q.2.2.1.1 wt).1 :=
  rfl

theorem rawZLocalPhase_eq_t37AmbientLedgerPhase
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (u : RawZLeft n b d)
    (v : RawZRight n b d) :
    rawZLocalPhase u v =
      t37AmbientLedgerPhase hn hb2 hd2 u
        (T37RightP1.t37GaugedRightCoordinateEquiv
          hn hb2 hd2 v) := by
  exact
    T37PhaseD.dT37GaugedPhase_coordinate_ledger
      hn hb2 hd2 u.1 u.2 v

def rawOuterLedgerPhase
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (A : DiamondEvenPReachableA n b c d) : F :=
  let x :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (RawZLeft n b d) hn hc2
      (literalOuterZLeftFamily
        (by omega : 0 < b) (by omega : 0 < c)
        (by omega : 0 < d) l)
  let q :=
    TotalEEEERightInternal.rawRightCoordinateEquiv
      hn hb2 hc2 hd2 A.1
  t37AmbientLedgerPhase hn hb2 hd2 (x.1.1 + x.1.2) q.1.1 +
    t37AmbientLedgerPhase hn hb2 hd2 x.1.1 q.1.2 +
    ∑ zt : DiamondEvenAxisTailIndex n c,
      t37AmbientLedgerPhase hn hb2 hd2 (x.2.1 zt) (q.2.1 zt)

private theorem rawRightCoordinateEquiv_E
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n b c d) :
    let y :=
      (TotalEOEEInternal.pointedHeadShear
          (zeroVec : PVec n c))
        (diamondEvenAxisDualCoordEquiv
          (n := n) (k := c)
          (PVec n b → PVec n d → CyclicCube n) hn hc2
          (TotalEEEERightInternal.aZOuterGaugeEquiv
            (n := n) (b := b) (c := c) (d := d)
            (by omega : 0 < b) (by omega : 0 < c)
            (by omega : 0 < d) A))
    (TotalEEEERightInternal.rawRightCoordinateEquiv
      hn hb2 hc2 hd2 A).1.2 =
      T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2 y.1.2 :=
  rfl

private theorem rawRightCoordinateEquiv_ZTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n b c d)
    (zt : DiamondEvenAxisTailIndex n c) :
    let y :=
      (TotalEOEEInternal.pointedHeadShear
          (zeroVec : PVec n c))
        (diamondEvenAxisDualCoordEquiv
          (n := n) (k := c)
          (PVec n b → PVec n d → CyclicCube n) hn hc2
          (TotalEEEERightInternal.aZOuterGaugeEquiv
            (n := n) (b := b) (c := c) (d := d)
            (by omega : 0 < b) (by omega : 0 < c)
            (by omega : 0 < d) A))
    ((TotalEEEERightInternal.rawRightCoordinateEquiv
      hn hb2 hc2 hd2 A).2.1 zt) =
      T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2
        (y.2.1 zt) :=
  rfl

private theorem reachableEEEEEquiv_eq_pack_raw
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n b c d) :
    let raw :=
      TotalEEEERightInternal.rawRightCoordinateEquiv
        hn hb2 hc2 hd2 A.1
    let D :
        TotalEEEERightInternal.t37RightLedgerSubmodule n b d :=
      ⟨raw.1.1,
        (TotalEEEERightInternal.literal_reachable_iff_raw_D_ledger
          hn hb2 hc2 hd2 A.1).mp A.2⟩
    let packedD :=
      TotalEEEERightInternal.t37LedgerAmbientToReachableTargetEquiv
        hn hb2 hd2 D
    let packedZTail :=
      TotalEEEERightInternal.tailT37ReassocEquiv
        (n := n) (b := b) (c := c) (d := d) raw.2
    diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A =
      TotalEEEERightInternal.constrainedZTotalFreeEquiv
        (n := n) (b := b) (c := c) (d := d)
        ((packedD, raw.1.2), packedZTail) :=
  rfl

private theorem constrainedZTotalFreeEquiv_fields
    {n b c d : Nat} [NeZero n]
    (q : TotalEEEERightInternal.ConstrainedZTotalFreeInput n b c d) :
    TotalEEEERightInternal.constrainedZTotalFreeEquiv
        (n := n) (b := b) (c := c) (d := d) q =
      (TotalEEEERightInternal.scalarConstrainedFreeEquiv
          (q.1.1.1, q.1.2.1),
        (TotalEEEERightInternal.yConstrainedFreeEquiv
            (q.1.1.2.1, q.1.2.2.1),
          (TotalEEEERightInternal.wConstrainedFreeEquiv
              (q.1.1.2.2.1, q.1.2.2.2.1),
            (q.2.1,
              (q.2.2.1,
                (q.2.2.2.1,
                  (TotalEEEERightInternal.ywConstrainedFreeEquiv
                      (q.1.1.2.2.2, q.1.2.2.2.2),
                    q.2.2.2.2))))))) :=
  rfl

theorem totalEEEELiteralPhase_eq_rawOuterLedger
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (A : DiamondEvenPReachableA n b c d) :
    diamondEvenPCross l A =
      rawOuterLedgerPhase hn hb2 hc2 hd2 l A := by
  rw [totalEEEELiteralPhaseGauged
    (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d)]
  rw [Finset.sum_comm]
  change
    (∑ zt : PVec n c,
      rawZLocalPhase
        (literalOuterZLeftFamily
          (by omega : 0 < b) (by omega : 0 < c)
          (by omega : 0 < d) l zt)
        (literalOuterZRightFamily
          (by omega : 0 < b) (by omega : 0 < c)
          (by omega : 0 < d) A zt)) = _
  rw [rawOuterZPairingSheared hn hc2]
  rw [rawZLocalPhase_eq_t37AmbientLedgerPhase hn hb2 hd2,
    rawZLocalPhase_eq_t37AmbientLedgerPhase hn hb2 hd2]
  simp_rw [rawZLocalPhase_eq_t37AmbientLedgerPhase hn hb2 hd2]
  rfl

/-! ## The frozen six-active/two-zero coordinate phase -/

def totalEEEEYBasePhase
    {n : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEYLeftBase n)
    (q : TotalEEEERightInternal.YRightBase n) : F :=
  cubeDot (cubeDiffK (x.1.1 + x.2)) q.1.1.1 +
    cubeDot (cubeDiffK x.1.1) q.2.1

theorem totalEEEEYBasePhase_reduced
    {n : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEYLeftBase n)
    (q : TotalEEEERightInternal.YRightBase n) :
    totalEEEEYBasePhase x q =
      cubeDot (cubeDiffK x.2) q.1.1.1 +
        cubeDot (cubeDiffK x.1.1) q.2.1 := by
  rw [totalEEEEYBasePhase, map_add,
    EEOEInternal.cubeDot_add_left,
    T37PhaseD.dT37RBlock_JKernel_phase_zero x.1 q.1.1]
  simp only [zero_add]

def totalEEEEWBasePhase
    {n : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEWLeftBase n)
    (q : TotalEEEERightInternal.WRightBase n) : F :=
  cubeDot (cubeDiffI (x.1.1 + x.2)) q.1.1.1 +
    cubeDot (cubeDiffI x.1.1) q.1.2

theorem totalEEEEWBasePhase_reduced
    {n : Nat} [NeZero n]
    (x : TotalEEEEInternal.TotalEEEEWLeftBase n)
    (q : TotalEEEERightInternal.WRightBase n) :
    totalEEEEWBasePhase x q =
      cubeDot (cubeDiffI x.2) q.1.1.1 +
        cubeDot (cubeDiffI x.1.1) q.1.2 := by
  rw [totalEEEEWBasePhase, map_add,
    EEOEInternal.cubeDot_add_left,
    T37PhaseD.dT37PBlock_JKernel_phase_zero x.1 q.1.1]
  simp only [zero_add]

private def scalarAmbientPhase
    {n : Nat} [NeZero n]
    (l : DiamondEEEELeftAmbient n)
    (q : DiamondEEEERightAmbient n) : F :=
  let r := diamondEEEECoeffMap l
  cubeDot r.1.1.1 q.1.1.1 +
    cubeDot r.1.1.2 q.1.1.2 +
    cubeDot r.1.2.1 q.1.2.1 +
    cubeDot r.1.2.2 q.1.2.2 +
    cubeDot r.2.1.1 q.2.1.1 +
    cubeDot r.2.1.2 q.2.1.2 +
    cubeDot r.2.2.1 q.2.2.1 +
    cubeDot r.2.2.2 q.2.2.2

private theorem diamondEEEECross_eq_scalarAmbientPhase
    {n : Nat} [NeZero n]
    (l : DiamondEEEELeftSource n)
    (q : DiamondEEEERightSource n) :
    diamondEEEECross l q = scalarAmbientPhase l.1 q.1 :=
  rfl

private def scalarDLeft
    {n : Nat} [NeZero n]
    (l : DiamondEEEELeftAmbient n) :
    DiamondEEOELeftAmbient n :=
  ((l.1.1.1 + l.1.2.1, l.1.1.2 + l.1.2.2),
    (l.2.1.1 + l.2.1.2, l.2.2.1 + l.2.2.2))

private def scalarELeft
    {n : Nat} [NeZero n]
    (l : DiamondEEEELeftAmbient n) :
    DiamondEEOELeftAmbient n :=
  ((l.1.1.1, l.1.1.2), (l.2.1.1, l.2.2.1))

private def scalarInterleaveValue
    {n : Nat} [NeZero n]
    (qD qE : DiamondEEOERightAmbient n) :
    DiamondEEEERightAmbient n :=
  (((qD.1.1, qD.1.2), (qE.1.1, qE.1.2)),
    ((qD.2.1, qD.2.2), (qE.2.1, qE.2.2)))

private theorem scalarInterleaveEquiv_eq_value
    {n : Nat} [NeZero n]
    (qD qE : DiamondEEOERightAmbient n) :
    TotalEEEERightInternal.scalarInterleaveEquiv (qD, qE) =
      scalarInterleaveValue qD qE :=
  rfl

private theorem scalarHeads_merge
    {n : Nat} [NeZero n]
    (l : DiamondEEEELeftAmbient n)
    (qD qE : DiamondEEOERightAmbient n) :
    EEOEInternal.ambientPhase
          (diamondEEOECoeffMap (scalarDLeft l)) qD +
        EEOEInternal.ambientPhase
          (diamondEEOECoeffMap (scalarELeft l)) qE =
      scalarAmbientPhase l
        (scalarInterleaveValue qD qE) := by
  simp only [EEOEInternal.ambientPhase, diamondEEOECoeffMap,
    scalarDLeft, scalarELeft, scalarAmbientPhase,
    scalarInterleaveValue, diamondEEEECoeffMap,
    LinearMap.coe_mk, AddHom.coe_mk, map_add,
    EEOEInternal.cubeDot_add_left, cubeDot_zero_left, add_zero]
  abel

private theorem diamondTailAllEvenZCross_eq_ambientPhase
    {n : Nat} [NeZero n]
    (l : DiamondEEOELeftAmbient n)
    (q : DiamondEEOERightAmbient n) :
    diamondTailAllEvenZCross l q =
      EEOEInternal.ambientPhase (diamondEEOECoeffMap l) q :=
  rfl

private theorem packedT37_scalar_value
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (q : TotalEEEERightInternal.t37RightLedgerSubmodule n b d) :
    ((TotalEEEERightInternal.t37LedgerAmbientToReachableTargetEquiv
      hn hb2 hd2 q).1).1 = q.1.1 :=
  by
    change
      (T37RightP1.t37RightAmbientEquiv hn hb2 hd2
        ((T37RightP1.t37RightAmbientEquiv
          hn hb2 hd2).symm q.1)).1 = q.1.1
    exact congrArg Prod.fst
      ((T37RightP1.t37RightAmbientEquiv
        hn hb2 hd2).apply_symm_apply q.1)

private theorem packedT37_Y_value
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (q : TotalEEEERightInternal.t37RightLedgerSubmodule n b d)
    (yt : DiamondEvenAxisTailIndex n b) :
    ((((TotalEEEERightInternal.t37LedgerAmbientToReachableTargetEquiv
        hn hb2 hd2 q).2.1.1 yt).1.1),
      (((TotalEEEERightInternal.t37LedgerAmbientToReachableTargetEquiv
        hn hb2 hd2 q).2.1.1 yt).2.1)) =
      q.1.2.1.1 yt :=
  by
    change
      (T37RightP1.t37RightAmbientEquiv hn hb2 hd2
          ((T37RightP1.t37RightAmbientEquiv
            hn hb2 hd2).symm q.1)).2.1.1 yt =
        q.1.2.1.1 yt
    exact congrArg (fun z => z.2.1.1 yt)
      ((T37RightP1.t37RightAmbientEquiv
        hn hb2 hd2).apply_symm_apply q.1)

private theorem packedT37_W_value
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (q : TotalEEEERightInternal.t37RightLedgerSubmodule n b d)
    (wt : DiamondEvenAxisTailIndex n d) :
    ((((TotalEEEERightInternal.t37LedgerAmbientToReachableTargetEquiv
        hn hb2 hd2 q).2.2.1.1 wt).1.1),
      (((TotalEEEERightInternal.t37LedgerAmbientToReachableTargetEquiv
        hn hb2 hd2 q).2.2.1.1 wt).2.1)) =
      q.1.2.2.1.1 wt :=
  by
    change
      (T37RightP1.t37RightAmbientEquiv hn hb2 hd2
          ((T37RightP1.t37RightAmbientEquiv
            hn hb2 hd2).symm q.1)).2.2.1.1 wt =
        q.1.2.2.1.1 wt
    exact congrArg (fun z => z.2.2.1.1 wt)
      ((T37RightP1.t37RightAmbientEquiv
        hn hb2 hd2).apply_symm_apply q.1)

private theorem packedT37_Y_first_value
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (q : TotalEEEERightInternal.t37RightLedgerSubmodule n b d)
    (yt : DiamondEvenAxisTailIndex n b) :
    (((TotalEEEERightInternal.t37LedgerAmbientToReachableTargetEquiv
      hn hb2 hd2 q).2.1.1 yt).1.1) =
      (q.1.2.1.1 yt).1 :=
  congrArg Prod.fst (packedT37_Y_value hn hb2 hd2 q yt)

private theorem packedT37_W_first_value
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (q : TotalEEEERightInternal.t37RightLedgerSubmodule n b d)
    (wt : DiamondEvenAxisTailIndex n d) :
    (((TotalEEEERightInternal.t37LedgerAmbientToReachableTargetEquiv
      hn hb2 hd2 q).2.2.1.1 wt).1.1) =
      (q.1.2.2.1.1 wt).1 :=
  congrArg Prod.fst (packedT37_W_value hn hb2 hd2 q wt)

private theorem packedZTail_Z_value
    {n b c d : Nat} [NeZero n]
    (q : DiamondEvenAxisValueTailZero n c
      (T37RightP1.T37RightAmbientTarget n b d))
    (zt : DiamondEvenAxisTailIndex n c) :
    ((TotalEEEERightInternal.tailT37ReassocEquiv
      (n := n) (b := b) (c := c) (d := d) q).1.1 zt) =
      (q.1 zt).1 :=
  rfl

private theorem packedZTail_YZ_value
    {n b c d : Nat} [NeZero n]
    (q : DiamondEvenAxisValueTailZero n c
      (T37RightP1.T37RightAmbientTarget n b d))
    (yt : DiamondEvenAxisTailIndex n b)
    (zt : DiamondEvenAxisTailIndex n c) :
    (((TotalEEEERightInternal.tailT37ReassocEquiv
      (n := n) (b := b) (c := c) (d := d) q).2.1.1 yt).1 zt) =
      (q.1 zt).2.1.1 yt :=
  rfl

private theorem packedZTail_WZ_value
    {n b c d : Nat} [NeZero n]
    (q : DiamondEvenAxisValueTailZero n c
      (T37RightP1.T37RightAmbientTarget n b d))
    (zt : DiamondEvenAxisTailIndex n c)
    (wt : DiamondEvenAxisTailIndex n d) :
    (((TotalEEEERightInternal.tailT37ReassocEquiv
      (n := n) (b := b) (c := c) (d := d) q).2.2.1.1 zt).1 wt) =
      (q.1 zt).2.2.1.1 wt :=
  rfl

private theorem scalarConstrainedFreeEquiv_value
    {n b d : Nat} [NeZero n]
    (qD : T37RightP1.T37RightReachableTarget n b d)
    (qE : T37RightP1.T37RightAmbientTarget n b d) :
    (TotalEEEERightInternal.scalarConstrainedFreeEquiv
      (qD.1, qE.1)).1 =
      scalarInterleaveValue qD.1.1 qE.1 :=
  rfl

private theorem yConstrainedFreeEquiv_value
    {n b d : Nat} [NeZero n]
    (qD : T37RightP1.T37RightReachableTarget n b d)
    (qE : T37RightP1.T37RightAmbientTarget n b d)
    (yt : DiamondEvenAxisTailIndex n b) :
    (TotalEEEERightInternal.yConstrainedFreeEquiv
      (qD.2.1, qE.2.1)).1 yt =
      (qD.2.1.1 yt, qE.2.1.1 yt) :=
  rfl

private theorem wConstrainedFreeEquiv_value
    {n b d : Nat} [NeZero n]
    (qD : T37RightP1.T37RightReachableTarget n b d)
    (qE : T37RightP1.T37RightAmbientTarget n b d)
    (wt : DiamondEvenAxisTailIndex n d) :
    (TotalEEEERightInternal.wConstrainedFreeEquiv
      (qD.2.2.1, qE.2.2.1)).1 wt =
      (((qD.2.2.1.1 wt).1, (qE.2.2.1.1 wt).1),
        ((qD.2.2.1.1 wt).2, (qE.2.2.1.1 wt).2)) :=
  rfl

def totalEEEEYZBasePhase
    {n : Nat} [NeZero n]
    (x : CyclicCube n)
    (q : CyclicCube n × CyclicCube n) : F :=
  cubeDot (cubeDiffK x) q.1

def totalEEEEWZBasePhase
    {n : Nat} [NeZero n]
    (x : CyclicCube n)
    (q : CyclicCube n × CyclicCube n) : F :=
  cubeDot (cubeDiffI x) q.1

/-- The `YW` source coordinate is bottom-valued.  Its right carrier is
intentionally retained and may be nonzero. -/
def totalEEEEYWBasePhase
    {n : Nat} [NeZero n]
    (_x : (⊥ : Submodule F (CyclicCube n)))
    (_q : TotalEEEERightInternal.YWRightBase n) : F :=
  0

/-- The innermost `YWZ` source coordinate is bottom-valued.  Its right cube
is intentionally retained and may be nonzero. -/
def totalEEEEYWZBasePhase
    {n : Nat} [NeZero n]
    (_x : (⊥ : Submodule F (CyclicCube n)))
    (_q : CyclicCube n) : F :=
  0

/-- The exact frozen association is
`scalar × (Y × (W × (Z × (YZ × (WZ × (YW × YWZ))))))`.
The first six summands are the literal nonzero sectors.  The final two
summands expose phase-zero on the actual bottom left coordinates without
altering either reachable right carrier. -/
def totalEEEECoordinatePhase
    {n b c d : Nat} [NeZero n]
    (l : TotalEEEELeftSourceTarget n b c d)
    (q : TotalEEEERightReachableTarget n b c d) : F :=
  diamondEEEECross l.1 q.1 +
    (∑ yt : DiamondEvenAxisTailIndex n b,
      totalEEEEYBasePhase
        (l.2.1.1 yt) (q.2.1.1 yt)) +
    (∑ wt : DiamondEvenAxisTailIndex n d,
      totalEEEEWBasePhase
        (l.2.2.1.1 wt) (q.2.2.1.1 wt)) +
    (∑ zt : DiamondEvenAxisTailIndex n c,
      diamondTailAllEvenZCross
        (l.2.2.2.1.1 zt) (q.2.2.2.1.1 zt)) +
    (∑ yt : DiamondEvenAxisTailIndex n b,
      ∑ zt : DiamondEvenAxisTailIndex n c,
        totalEEEEYZBasePhase
          ((l.2.2.2.2.1.1 yt).1 zt)
          ((q.2.2.2.2.1.1 yt).1 zt)) +
    (∑ zt : DiamondEvenAxisTailIndex n c,
      ∑ wt : DiamondEvenAxisTailIndex n d,
        totalEEEEWZBasePhase
          ((l.2.2.2.2.2.1.1 zt).1 wt)
          ((q.2.2.2.2.2.1.1 zt).1 wt)) +
    (∑ yt : DiamondEvenAxisTailIndex n b,
      ∑ wt : DiamondEvenAxisTailIndex n d,
        totalEEEEYWBasePhase
          ((l.2.2.2.2.2.2.1.1 yt).1 wt)
          ((q.2.2.2.2.2.2.1.1 yt).1 wt)) +
    ∑ yt : DiamondEvenAxisTailIndex n b,
      ∑ zt : DiamondEvenAxisTailIndex n c,
        ∑ wt : DiamondEvenAxisTailIndex n d,
          totalEEEEYWZBasePhase
            (((l.2.2.2.2.2.2.2.1 yt).1 zt).1 wt)
            (((q.2.2.2.2.2.2.2.1 yt).1 zt).1 wt)

set_option pp.universes false in
set_option pp.all false in
theorem totalEEEELiteralPhaseCoordinateSplit
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (A : DiamondEvenPReachableA n b c d) :
    diamondEvenPCross l A =
      totalEEEECoordinatePhase
        (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 l)
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) := by
  rw [totalEEEELiteralPhase_eq_rawOuterLedger
    hn hb2 hc2 hd2 l A]
  rw [reachableEEEEEquiv_eq_pack_raw
    hn hb2 hc2 hd2 A]
  rw [constrainedZTotalFreeEquiv_fields]
  simp only [rawOuterLedgerPhase, totalEEEECoordinatePhase,
    totalEEEEYWBasePhase, totalEEEEYWZBasePhase,
    Finset.sum_const_zero, add_zero]
  rw [diamondEEEECross_eq_scalarAmbientPhase]
  rw [scalarConstrainedFreeEquiv_value]
  rw [packedT37_scalar_value]
  simp_rw [yConstrainedFreeEquiv_value]
  simp_rw [wConstrainedFreeEquiv_value]
  simp only [totalEEEEYBasePhase, totalEEEEWBasePhase,
    totalEEEEYZBasePhase, totalEEEEWZBasePhase]
  simp_rw [packedT37_Y_first_value]
  simp_rw [packedT37_W_first_value]
  simp_rw [packedZTail_Z_value]
  simp_rw [packedZTail_YZ_value]
  simp_rw [packedZTail_WZ_value]
  have hleft :
      diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 l =
        frozenLeftCoords hn hb2 hc2 hd2 l :=
    rfl
  rw [hleft]
  rw [frozenLeft_scalar_eq_rawOuter]
  simp_rw [frozenLeft_Y_first_eq_rawOuter,
    frozenLeft_Y_second_eq_rawOuter]
  simp_rw [frozenLeft_W_first_eq_rawOuter,
    frozenLeft_W_second_eq_rawOuter]
  simp_rw [frozenLeft_Z_eq_rawOuter]
  simp_rw [frozenLeft_YZ_eq_rawOuter]
  simp_rw [frozenLeft_WZ_eq_rawOuter]
  simp_rw [t37AmbientLedgerPhase_eq_rawInner]
  simp_rw [rawInnerBCoords_add, rawInnerWCoords_add]
  simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
    Pi.add_apply]
  have houter :
      diamondEvenAxisSrcCoordEquiv
          (n := n) (k := c) (RawZLeft n b d) hn hc2
          (literalOuterZLeftFamily
            (by omega : 0 < b) (by omega : 0 < c)
            (by omega : 0 < d) l) =
        rawOuterZLeftCoords hn hb2 hc2 hd2 l :=
    rfl
  rw [houter]
  rw [← scalarHeads_merge]
  simp only [scalarDLeft, scalarELeft, prod_add_components]
  simp_rw [diamondTailAllEvenZCross_eq_ambientPhase]
  simp only [Finset.sum_add_distrib]
  have hYZ :
      (∑ zt : DiamondEvenAxisTailIndex n c,
        ∑ yt : DiamondEvenAxisTailIndex n b,
          cubeDot
            (cubeDiffK
              ((rawInnerWCoords hn hb2
                ((rawOuterZLeftCoords
                  hn hb2 hc2 hd2 l).2.1 zt)).2.1 yt))
            ((((TotalEEEERightInternal.rawRightCoordinateEquiv
              hn hb2 hc2 hd2 A.1).2.1 zt).2.1.1 yt).1)) =
        ∑ yt : DiamondEvenAxisTailIndex n b,
          ∑ zt : DiamondEvenAxisTailIndex n c,
            cubeDot
              (cubeDiffK
                ((rawInnerWCoords hn hb2
                  ((rawOuterZLeftCoords
                    hn hb2 hc2 hd2 l).2.1 zt)).2.1 yt))
              ((((TotalEEEERightInternal.rawRightCoordinateEquiv
                hn hb2 hc2 hd2 A.1).2.1 zt).2.1.1 yt).1) :=
    Finset.sum_comm
  rw [hYZ]
  ac_rfl

end TotalEEEEPhase

end

end Core4loop.SquareDiagonal.EvenP
