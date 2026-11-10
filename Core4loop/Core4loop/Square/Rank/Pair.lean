import Core4loop.Square.Rank.PairSetup

open scoped BigOperators

namespace Core4loop

noncomputable def BFiber {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (p : PVec n a) (sy sz : I n) (w : WVec n d) : F :=
  ∑ z : ZVec n c, if vecSum z = sz then B p sy z w else 0

lemma BRootFiberSum_KBMap {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (B : BFun4 n a c d) (sy sz : I n) (w : WVec n d) :
    BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
        (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B) sy sz w =
      ∑ p : PVec n a,
        (BFiber (n := n) (a := a) (c := c) (d := d) B p sy sz w
          + BFiber (n := n) (a := a) (c := c) (d := d) B p (sy + 1) sz w) := by
  classical
  unfold BRootFiberSum BFiber
  change
    (∑ z : ZVec n c,
        if vecSum z = sz then
          ∑ p : PVec n a, dyB B p (vecSumRep (n := n) (k := b) hb sy) z w
        else 0) =
      ∑ p : PVec n a,
        ((∑ z : ZVec n c, if vecSum z = sz then B p sy z w else 0)
          + ∑ z : ZVec n c, if vecSum z = sz then B p (sy + 1) z w else 0)
  unfold dyB betaB gammaB
  rw [vecSum_vecSumRep (n := n) (k := b) hb sy]
  calc
    (∑ z : ZVec n c,
        if vecSum z = sz then ∑ p : PVec n a, (B p sy z w + B p (sy + 1) z w) else 0)
        =
        ∑ z : ZVec n c, ∑ p : PVec n a,
          if vecSum z = sz then B p sy z w + B p (sy + 1) z w else 0 := by
          refine Finset.sum_congr rfl ?_
          intro z _
          by_cases hz : vecSum z = sz <;> simp [hz]
    _ =
        ∑ p : PVec n a, ∑ z : ZVec n c,
          if vecSum z = sz then B p sy z w + B p (sy + 1) z w else 0 := by
          rw [Finset.sum_comm]
    _ =
        ∑ p : PVec n a,
          ((∑ z : ZVec n c, if vecSum z = sz then B p sy z w else 0)
            + ∑ z : ZVec n c, if vecSum z = sz then B p (sy + 1) z w else 0) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro z _
          by_cases hz : vecSum z = sz <;> simp [hz]

lemma BCompatPSum_squareCompat_B {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (B : BFun4 n a c d) (sy sz : I n) (w : WVec n d) :
    BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
        (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) B)
        sy sz w =
      ∑ p : PVec n a,
        (BFiber (n := n) (a := a) (c := c) (d := d) B p sy sz w
          + BFiber (n := n) (a := a) (c := c) (d := d) B p (sy + 1) (sz - 1) w) := by
  classical
  unfold BCompatPSum BFiber
  change
    (∑ p : PVec n a,
        squareCompatFun B 0 p (vecSumRep (n := n) (k := b) hb sy) sz w) =
      ∑ p : PVec n a,
        ((∑ z : ZVec n c, if vecSum z = sz then B p sy z w else 0)
          + ∑ z : ZVec n c, if vecSum z = sz - 1 then B p (sy + 1) z w else 0)
  unfold squareCompatFun betaB gammaB xiW zetaW
  rw [vecSum_vecSumRep (n := n) (k := b) hb sy]
  refine Finset.sum_congr rfl ?_
  intro p _
  simp only [Pi.zero_apply, add_zero]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro z _
  have hiff : vecSum z + 1 = sz ↔ vecSum z = sz - 1 := by
    constructor
    · intro h
      rw [← h]
      abel
    · intro h
      rw [h]
      abel
  exact if_congr hiff rfl rfl

theorem BPairRawCurl_SquareBMapAmbient
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) (B : BFun4 n a c d) :
    BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B) = 0 := by
  classical
  funext w sy sz
  unfold BPairRawCurl
  change
    BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
          (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B) sy sz w
      + BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
          (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B)
          (sy + 1) (sz - 1) w
      + BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
          (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) B)
          sy sz w
      + BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
          (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) B)
          (sy + 1) sz w =
    0
  rw [BRootFiberSum_KBMap (n := n) (a := a) (b := b) (c := c) (d := d) hb B sy sz w]
  rw [BRootFiberSum_KBMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hb B (sy + 1) (sz - 1) w]
  rw [BCompatPSum_squareCompat_B
    (n := n) (a := a) (b := b) (c := c) (d := d) hb B sy sz w]
  rw [BCompatPSum_squareCompat_B
    (n := n) (a := a) (b := b) (c := c) (d := d) hb B (sy + 1) sz w]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro p _
  ring_nf
  have htwo : (2 : F) = 0 := by decide
  rw [htwo]
  simp

theorem SquareBMapAmbient_mem_ker_rawCurl
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) (B : BFun4 n a c d) :
    SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B ∈
      LinearMap.ker (BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  apply LinearMap.mem_ker.mpr
  exact BPairRawCurl_SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) hb B

noncomputable def WRootFiberSum {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (R : RootTarget n b c d) (y : YVec n b) (sw sz : I n) : F :=
  ∑ z : ZVec n c,
    if vecSum z = sz then R y z (vecSumRep (n := n) (k := d) hd sw) else 0

noncomputable def WCompatPSum {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (C : CFun4 n a b d) (y : YVec n b) (sw sz : I n) : F :=
  ∑ p : PVec n a, C p y sz (vecSumRep (n := n) (k := d) hd sw)

noncomputable def WPairRawCurl {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (x : WPairAmbient n a b c d) (y : YVec n b) : MatrixProfile n :=
  fun sw sz =>
    WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd x.1.1 y sw sz
      + WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
          x.1.1 y (sw + 1) (sz - 1)
      + WCompatPSum (n := n) (a := a) (b := b) (d := d) hd x.2.1 y sw sz
      + WCompatPSum (n := n) (a := a) (b := b) (d := d) hd
          x.2.1 y (sw + 1) sz

set_option linter.flexible false in
noncomputable def WPairRawCurlMap {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    WPairAmbient n a b c d →ₗ[F] (YVec n b → MatrixProfile n) where
  toFun x := WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd x
  map_add' x y := by
    funext y0 sw sz
    unfold WPairRawCurl WRootFiberSum WCompatPSum
    simp [Finset.sum_add_distrib]
    rw [sum_if_add_F, sum_if_add_F]
    abel
  map_smul' r x := by
    funext y sw sz
    unfold WPairRawCurl WRootFiberSum WCompatPSum
    simp [smul_eq_mul]
    rw [sum_if_mul_F, sum_if_mul_F, ← Finset.mul_sum, ← Finset.mul_sum]
    ring

noncomputable def WFiber {n a b c : ℕ} [NeZero n]
    (W : WFun4 n a b c) (p : PVec n a) (y : YVec n b) (sz sw : I n) : F :=
  ∑ z : ZVec n c, if vecSum z = sz then W p y z sw else 0

lemma WRootFiberSum_KWMap {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (W : WFun4 n a b c) (y : YVec n b) (sw sz : I n) :
    WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
        (KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W) y sw sz =
      ∑ p : PVec n a,
        (WFiber (n := n) (a := a) (b := b) (c := c) W p y sz sw
          + WFiber (n := n) (a := a) (b := b) (c := c) W p y sz (sw + 1)) := by
  classical
  unfold WRootFiberSum WFiber
  change
    (∑ z : ZVec n c,
        if vecSum z = sz then
          ∑ p : PVec n a, dwW W p y z (vecSumRep (n := n) (k := d) hd sw)
        else 0) =
      ∑ p : PVec n a,
        ((∑ z : ZVec n c, if vecSum z = sz then W p y z sw else 0)
          + ∑ z : ZVec n c, if vecSum z = sz then W p y z (sw + 1) else 0)
  unfold dwW xiW zetaW
  rw [vecSum_vecSumRep (n := n) (k := d) hd sw]
  calc
    (∑ z : ZVec n c,
        if vecSum z = sz then ∑ p : PVec n a, (W p y z sw + W p y z (sw + 1)) else 0)
        =
        ∑ z : ZVec n c, ∑ p : PVec n a,
          if vecSum z = sz then W p y z sw + W p y z (sw + 1) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro z _
          by_cases hz : vecSum z = sz <;> simp [hz]
    _ =
        ∑ p : PVec n a, ∑ z : ZVec n c,
          if vecSum z = sz then W p y z sw + W p y z (sw + 1) else 0 := by
          rw [Finset.sum_comm]
    _ =
        ∑ p : PVec n a,
          ((∑ z : ZVec n c, if vecSum z = sz then W p y z sw else 0)
            + ∑ z : ZVec n c, if vecSum z = sz then W p y z (sw + 1) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro z _
          by_cases hz : vecSum z = sz <;> simp [hz]

lemma WCompatPSum_squareCompat_W {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (W : WFun4 n a b c) (y : YVec n b) (sw sz : I n) :
    WCompatPSum (n := n) (a := a) (b := b) (d := d) hd
        (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) W)
        y sw sz =
      ∑ p : PVec n a,
        (WFiber (n := n) (a := a) (b := b) (c := c) W p y sz sw
          + WFiber (n := n) (a := a) (b := b) (c := c) W p y (sz - 1) (sw + 1)) := by
  classical
  unfold WCompatPSum WFiber
  change
    (∑ p : PVec n a,
        squareCompatFun 0 W p y sz (vecSumRep (n := n) (k := d) hd sw)) =
      ∑ p : PVec n a,
        ((∑ z : ZVec n c, if vecSum z = sz then W p y z sw else 0)
          + ∑ z : ZVec n c, if vecSum z = sz - 1 then W p y z (sw + 1) else 0)
  unfold squareCompatFun betaB gammaB xiW zetaW
  rw [vecSum_vecSumRep (n := n) (k := d) hd sw]
  refine Finset.sum_congr rfl ?_
  intro p _
  simp only [Pi.zero_apply, zero_add]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro z _
  have hiff : vecSum z + 1 = sz ↔ vecSum z = sz - 1 := by
    constructor
    · intro h
      rw [← h]
      abel
    · intro h
      rw [h]
      abel
  exact if_congr hiff rfl rfl

theorem WPairRawCurl_SquareWMapAmbient
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) (W : WFun4 n a b c) :
    WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W) = 0 := by
  classical
  funext y sw sz
  unfold WPairRawCurl
  change
    WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
          (KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W) y sw sz
      + WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
          (KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W)
          y (sw + 1) (sz - 1)
      + WCompatPSum (n := n) (a := a) (b := b) (d := d) hd
          (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) W)
          y sw sz
      + WCompatPSum (n := n) (a := a) (b := b) (d := d) hd
          (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) W)
          y (sw + 1) sz =
    0
  rw [WRootFiberSum_KWMap (n := n) (a := a) (b := b) (c := c) (d := d) hd W y sw sz]
  rw [WRootFiberSum_KWMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hd W y (sw + 1) (sz - 1)]
  rw [WCompatPSum_squareCompat_W
    (n := n) (a := a) (b := b) (c := c) (d := d) hd W y sw sz]
  rw [WCompatPSum_squareCompat_W
    (n := n) (a := a) (b := b) (c := c) (d := d) hd W y (sw + 1) sz]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro p _
  ring_nf
  have htwo : (2 : F) = 0 := by decide
  rw [htwo]
  simp

theorem SquareWMapAmbient_mem_ker_rawCurl
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) (W : WFun4 n a b c) :
    SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W ∈
      LinearMap.ker (WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) := by
  apply LinearMap.mem_ker.mpr
  exact WPairRawCurl_SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) hd W

end Core4loop
