import Core4loop.Square.Rank.PairExact

open scoped BigOperators

namespace Core4loop

noncomputable def WZeroRootLTarget
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (y : YVec n b) : ZeroSumProfile n :=
  ⟨WZeroRootL (n := n) V y,
    LinearMap.mem_ker.mpr
      (W_zeroRoot_L_zero_sum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hd x V hV hroot hraw y)⟩

noncomputable def WZeroRootK
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (y : YVec n b) : Profile n :=
  Classical.choose
    (show ∃ h : Profile n,
        cycDiff (n := n) F h =
          (WZeroRootLTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hd x V hV hroot hraw y).1 by
      have hm :
          (WZeroRootLTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hd x V hV hroot hraw y).1 ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (WZeroRootLTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hd x V hV hroot hraw y).2
      exact hm)

lemma WZeroRootK_spec
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (y : YVec n b) :
    cycDiff (n := n) F
        (WZeroRootK
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hd x V hV hroot hraw y) =
      (WZeroRootLTarget
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hd x V hV hroot hraw y).1 :=
  Classical.choose_spec
    (show ∃ h : Profile n,
        cycDiff (n := n) F h =
          (WZeroRootLTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hd x V hV hroot hraw y).1 by
      have hm :
          (WZeroRootLTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hd x V hV hroot hraw y).1 ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (WZeroRootLTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hd x V hV hroot hraw y).2
      exact hm)

noncomputable def WZeroRootHcorr
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (p : PVec n a) (y : YVec n b) (sw sz : I n) : F :=
  if p = (zeroVec : PVec n a) then
    WZeroRootK
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hd x V hV hroot hraw y (sw + sz)
  else 0

noncomputable def WZeroRootG
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (p : PVec n a) (y : YVec n b) (sw sz : I n) : F :=
  WZeroRootD (n := n) V p y sw sz +
    WZeroRootHcorr
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hd x V hV hroot hraw p y sw sz

lemma WZeroRootG_diag
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (p : PVec n a) (y : YVec n b) (sw sz : I n) :
    WZeroRootG
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hd x V hV hroot hraw p y sw sz +
      WZeroRootG
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hd x V hV hroot hraw p y (sw + 1) (sz - 1) =
      (V p y).1 sw (sw + sz) := by
  classical
  unfold WZeroRootG WZeroRootHcorr
  have hcoord : sw + 1 + (sz - 1) = sw + sz := by abel
  by_cases hp : p = (zeroVec : PVec n a)
  · rw [if_pos hp, if_pos hp, hcoord]
    have hdiag := WZeroRootD_diag (n := n) V p y sw sz
    calc
      WZeroRootD (n := n) V p y sw sz +
            WZeroRootK
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw y (sw + sz) +
          (WZeroRootD (n := n) V p y (sw + 1) (sz - 1) +
            WZeroRootK
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw y (sw + sz))
          =
        (WZeroRootD (n := n) V p y sw sz +
          WZeroRootD (n := n) V p y (sw + 1) (sz - 1)) +
          (WZeroRootK
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hd x V hV hroot hraw y (sw + sz) +
            WZeroRootK
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw y (sw + sz)) := by ring
      _ = (WZeroRootD (n := n) V p y sw sz +
          WZeroRootD (n := n) V p y (sw + 1) (sz - 1)) + 0 := by
            rw [F_add_self]
      _ = (V p y).1 sw (sw + sz) := by
            simp [hdiag]
  · rw [if_neg hp, if_neg hp]
    simpa using WZeroRootD_diag (n := n) V p y sw sz

lemma WZeroRootHcorr_w_sum
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (y : YVec n b) (sw sz : I n) :
    (∑ p : PVec n a,
      (WZeroRootHcorr
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hd x V hV hroot hraw p y sw sz +
        WZeroRootHcorr
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hd x V hV hroot hraw p y (sw + 1) sz)) =
      WZeroRootL (n := n) V y (sw + sz) := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · unfold WZeroRootHcorr
    rw [if_pos rfl, if_pos rfl]
    have hcoord : sw + 1 + sz = sw + sz + 1 := by abel
    rw [hcoord]
    have hpoint := congrFun
      (WZeroRootK_spec
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hd x V hV hroot hraw y) (sw + sz)
    simpa [WZeroRootLTarget, WZeroRootL, cycDiff] using hpoint
  · intro p _ hp
    unfold WZeroRootHcorr
    rw [if_neg hp, if_neg hp]
    simp
  · simp

lemma WZeroRootG_w_sum
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (y : YVec n b) (sw sz : I n) :
    (∑ p : PVec n a,
      (WZeroRootG
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hd x V hV hroot hraw p y sw sz +
        WZeroRootG
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hd x V hV hroot hraw p y (sw + 1) sz)) = 0 := by
  classical
  have hdiag := W_zeroRoot_Dsum_diag_read
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hd x V hV hroot hraw y sw sz
  have hcorr := WZeroRootHcorr_w_sum
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hd x V hV hroot hraw y sw sz
  unfold WZeroRootG
  calc
    (∑ p : PVec n a,
      ((WZeroRootD (n := n) V p y sw sz +
            WZeroRootHcorr
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw p y sw sz) +
        (WZeroRootD (n := n) V p y (sw + 1) sz +
            WZeroRootHcorr
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw p y (sw + 1) sz)))
        =
      WZeroRootDsum (n := n) V y sw sz +
        (∑ p : PVec n a,
          (WZeroRootHcorr
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw p y sw sz +
            WZeroRootHcorr
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw p y (sw + 1) sz)) := by
            unfold WZeroRootDsum
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro p _
            ring
    _ = WZeroRootL (n := n) V y (sw + sz) +
          WZeroRootL (n := n) V y (sw + sz) := by
            rw [hdiag, hcorr]
            rfl
    _ = 0 := F_add_self _

noncomputable def WZeroRootWFun
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0) :
    WFun4 n a b c :=
  fun p y z sw =>
    if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
      WZeroRootG
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hd x V hV hroot hraw p y sw (vecSum z)
    else 0

lemma W_zeroRoot_fiber
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (p : PVec n a) (y : YVec n b) (sz sw : I n) :
    WFiber (n := n) (a := a) (b := b) (c := c)
        (WZeroRootWFun
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hc hd x V hV hroot hraw) p y sz sw =
      WZeroRootG
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hd x V hV hroot hraw p y sw sz := by
  classical
  unfold WFiber WZeroRootWFun
  rw [Finset.sum_eq_single (vecSumRep (n := n) (k := c) hc sz)]
  · rw [vecSum_vecSumRep (n := n) (k := c) hc sz]
    simp
  · intro z _ hz
    by_cases hzs : vecSum z = sz
    · have hnot : z ≠ vecSumRep (n := n) (k := c) hc (vecSum z) := by
        intro h
        apply hz
        rw [h, hzs]
      rw [if_pos hzs, if_neg hnot]
    · rw [if_neg hzs]
  · simp

lemma WZeroRootWFun_KWMap_zero
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0) :
    KWMap (n := n) (a := a) (b := b) (c := c) (d := d)
      (WZeroRootWFun
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hc hd x V hV hroot hraw) = 0 := by
  classical
  funext y z w
  unfold KWMap dwW xiW zetaW WZeroRootWFun
  by_cases hz : z = vecSumRep (n := n) (k := c) hc (vecSum z)
  · have hw := WZeroRootG_w_sum
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hd x V hV hroot hraw y (vecSum w) (vecSum z)
    calc
      (∑ p : PVec n a,
        ((if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
            WZeroRootG
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw p y (vecSum w) (vecSum z)
          else 0) +
          (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
            WZeroRootG
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw p y (vecSum w + 1) (vecSum z)
          else 0)))
          =
        ∑ p : PVec n a,
          (WZeroRootG
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw p y (vecSum w) (vecSum z) +
            WZeroRootG
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw p y (vecSum w + 1) (vecSum z)) := by
            refine Finset.sum_congr rfl ?_
            intro p _
            rw [if_pos hz, if_pos hz]
      _ = 0 := hw
  · apply Finset.sum_eq_zero
    intro p _
    change
      (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
        WZeroRootG
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hd x V hV hroot hraw p y (vecSum w) (vecSum z)
      else 0) +
        (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
          WZeroRootG
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hd x V hV hroot hraw p y (vecSum w + 1) (vecSum z)
        else 0) = 0
    rw [if_neg hz, if_neg hz]
    simp

lemma WZeroRootWFun_squareCompat
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b)
    (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0) :
    ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
      (WZeroRootWFun
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hc hd x V hV hroot hraw) =
      WDiagEmbed (n := n) (a := a) (b := b) (d := d) V := by
  classical
  let W : WFun4 n a b c :=
    WZeroRootWFun
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hc hd x V hV hroot hraw
  funext p y sz w
  change squareCompatFun 0 W p y sz w =
    (WDiagEmbed (n := n) (a := a) (b := b) (d := d) V) p y sz w
  unfold squareCompatFun betaB gammaB xiW zetaW WDiagEmbed
  simp only [Pi.zero_apply, zero_add]
  change
    (∑ z : ZVec n c, if vecSum z = sz then W p y z (vecSum w) else 0) +
        (∑ z : ZVec n c, if vecSum z + 1 = sz then W p y z (vecSum w + 1) else 0) =
      (V p y).1 (vecSum w) (vecSum w + sz)
  have hfirst :
      (∑ z : ZVec n c, if vecSum z = sz then W p y z (vecSum w) else 0) =
        WZeroRootG
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hd x V hV hroot hraw p y (vecSum w) sz := by
    simpa [W] using
      W_zeroRoot_fiber
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hc hd x V hV hroot hraw p y sz (vecSum w)
  have hsecond_fiber :
      (∑ z : ZVec n c, if vecSum z + 1 = sz then W p y z (vecSum w + 1) else 0) =
        WFiber (n := n) (a := a) (b := b) (c := c)
          W p y (sz - 1) (vecSum w + 1) := by
    unfold WFiber
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
  have hsecond :
      (∑ z : ZVec n c, if vecSum z + 1 = sz then W p y z (vecSum w + 1) else 0) =
        WZeroRootG
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hd x V hV hroot hraw p y (vecSum w + 1) (sz - 1) := by
    rw [hsecond_fiber]
    simpa [W] using
      W_zeroRoot_fiber
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hc hd x V hV hroot hraw p y (sz - 1) (vecSum w + 1)
  rw [hfirst, hsecond]
  exact WZeroRootG_diag
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hd x V hV hroot hraw p y (vecSum w) sz

theorem WPair_zeroRoot_mem_range
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (x : WPairAmbient n a b c d)
    (hroot : x.1.1 = 0)
    (hcurl :
      WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0) :
    x ∈ LinearMap.range
      (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  classical
  have hraw :=
    (WPairCurl_eq_zero_iff_raw
      (n := n) (a := a) (b := b) (c := c) (d := d) hd x).1 hcurl
  rcases x.2.2 with ⟨V, hV⟩
  let W : WFun4 n a b c :=
    WZeroRootWFun
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hc hd x V hV hroot hraw
  refine ⟨W, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    change
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W = x.1.1
    calc
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
          = 0 := by
            simpa [W] using
              WZeroRootWFun_KWMap_zero
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hc hd x V hV hroot hraw
      _ = x.1.1 := hroot.symm
  · apply Subtype.ext
    change
      (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) W) =
        x.2.1
    calc
      (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) W)
          = WDiagEmbed (n := n) (a := a) (b := b) (d := d) V := by
            simpa [W] using
              WZeroRootWFun_squareCompat
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hc hd x V hV hroot hraw
      _ = x.2.1 := hV

theorem ker_WPairCurlMap_eq_range_SquareWMapAmbient
    {n a b c d : ℕ} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    LinearMap.ker
        (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) =
      LinearMap.range
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  apply le_antisymm
  · intro x hx
    have hxroot_range :
        x.1.1 ∈ LinearMap.range
          (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      rw [range_KWMap_eq_WDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
      exact x.1.2
    rcases hxroot_range with ⟨W0, hW0⟩
    let x0 : WPairAmbient n a b c d :=
      SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W0
    have hx0root : x0.1.1 = x.1.1 := by
      change KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W0 = x.1.1
      exact hW0
    have hx0ker :
        x0 ∈ LinearMap.ker
          (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) := by
      exact SquareWMapAmbient_mem_ker_pairCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hd W0
    have hyroot : (x + x0).1.1 = 0 := by
      change x.1.1 + x0.1.1 = 0
      rw [hx0root]
      exact F_module_add_self x.1.1
    have hyker :
        x + x0 ∈ LinearMap.ker
          (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) :=
      Submodule.add_mem _ hx hx0ker
    have hyrange : x + x0 ∈
        LinearMap.range
          (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      exact WPair_zeroRoot_mem_range
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hc hd (x + x0) hyroot (LinearMap.mem_ker.mp hyker)
    have hx0range : x0 ∈
        LinearMap.range
          (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) :=
      ⟨W0, rfl⟩
    have hsumrange : x0 + (x + x0) ∈
        LinearMap.range
          (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) :=
      Submodule.add_mem _ hx0range hyrange
    have hxsum : x0 + (x + x0) = x := by
      calc
        x0 + (x + x0) = x + (x0 + x0) := by
          abel
        _ = x + 0 := by rw [F_module_add_self x0]
        _ = x := by simp
    rw [hxsum] at hsumrange
    exact hsumrange
  · exact range_SquareWMapAmbient_le_ker_WPairCurlMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd

end Core4loop
