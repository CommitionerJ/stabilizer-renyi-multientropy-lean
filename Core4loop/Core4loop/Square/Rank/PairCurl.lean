import Core4loop.Square.Rank.Pair
import Core4loop.Square.Rank.Shear
import Core4loop.Square.Rank.BPairCurlCore

open scoped BigOperators

namespace Core4loop

lemma WRootFiberSum_WDiff_col_zero {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d) (y : YVec n b) (sz : I n) :
    (∑ sw : I n,
      WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd x.1.1 y sw sz) = 0 := by
  classical
  rcases x.1.2 with ⟨U, hU⟩
  rw [← hU]
  unfold WRootFiberSum WDiffEmbed
  change
    (∑ sw : I n, ∑ z : ZVec n c,
      if vecSum z = sz then
        (U y z).1 (vecSum (vecSumRep (n := n) (k := d) hd sw))
      else 0) = 0
  calc
    (∑ sw : I n, ∑ z : ZVec n c,
        if vecSum z = sz then (U y z).1 (vecSum (vecSumRep (n := n) (k := d) hd sw))
        else 0)
        =
      ∑ sw : I n, ∑ z : ZVec n c,
        if vecSum z = sz then (U y z).1 sw else 0 := by
          refine Finset.sum_congr rfl ?_
          intro sw _
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [vecSum_vecSumRep (n := n) (k := d) hd sw]
    _ = ∑ z : ZVec n c, ∑ sw : I n,
            if vecSum z = sz then (U y z).1 sw else 0 := by
            rw [Finset.sum_comm]
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro z _
            by_cases hz : vecSum z = sz
            · have hterm :
                  (∑ sw : I n, if vecSum z = sz then (U y z).1 sw else 0) =
                    ∑ sw : I n, (U y z).1 sw := by
                refine Finset.sum_congr rfl ?_
                intro sw _
                rw [if_pos hz]
              rw [hterm]
              have hzero : sigmaMap (n := n) (U y z).1 = 0 :=
                LinearMap.mem_ker.mp (U y z).2
              change (∑ sw : I n, (U y z).1 sw) = 0 at hzero
              exact hzero
            · apply Finset.sum_eq_zero
              intro sw _
              rw [if_neg hz]

lemma WRootFiberSum_WDiff_col_shift_zero {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d) (y : YVec n b) (sz : I n) :
    (∑ sw : I n,
      WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
        x.1.1 y (sw + 1) (sz - 1)) = 0 := by
  classical
  have hshift :
      (∑ sw : I n,
        WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
          x.1.1 y (sw + 1) (sz - 1))
        =
      ∑ sw : I n,
        WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
          x.1.1 y sw (sz - 1) := by
    simpa using
      ((Equiv.addRight (1 : I n)).sum_comp (Finset.univ : Finset (I n))
        (fun sw : I n =>
          WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
            x.1.1 y sw (sz - 1)))
  rw [hshift]
  exact WRootFiberSum_WDiff_col_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hd x y (sz - 1)

lemma WCompatPSum_col_shift {n a b d : ℕ} [NeZero n]
    (hd : 0 < d) (C : CFun4 n a b d) (y : YVec n b) (sz : I n) :
    (∑ sw : I n, WCompatPSum (n := n) (a := a) (b := b) (d := d) hd
        C y (sw + 1) sz)
      =
    ∑ sw : I n, WCompatPSum (n := n) (a := a) (b := b) (d := d) hd
        C y sw sz := by
  simpa using
    ((Equiv.addRight (1 : I n)).sum_comp (Finset.univ : Finset (I n))
      (fun sw : I n =>
        WCompatPSum (n := n) (a := a) (b := b) (d := d) hd C y sw sz))

lemma WPairRawCurl_col_zero {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d) (y : YVec n b) (sz : I n) :
    (∑ sw : I n,
      WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d)
        hd x y sw sz) = 0 := by
  classical
  unfold WPairRawCurl
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [WRootFiberSum_WDiff_col_zero (n := n) (a := a) (b := b) (c := c) (d := d)
    hd x y sz]
  rw [WRootFiberSum_WDiff_col_shift_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hd x y sz]
  rw [WCompatPSum_col_shift (n := n) (a := a) (b := b) (d := d) hd x.2.1 y sz]
  simpa [add_assoc] using
    F_add_self (∑ sw : I n,
      WCompatPSum (n := n) (a := a) (b := b) (d := d) hd x.2.1 y sw sz)

lemma WRootFiberSum_diag_cancel {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d) (y : YVec n b) (t : I n) :
    (∑ sz : I n,
      WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd x.1.1 y (t - sz) sz)
      +
    (∑ sz : I n,
      WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
        x.1.1 y (t - sz + 1) (sz - 1)) = 0 := by
  classical
  let f : I n → F := fun sz =>
    WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd x.1.1 y (t - sz) sz
  have hshift :
      (∑ sz : I n,
        WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
          x.1.1 y (t - sz + 1) (sz - 1))
        = ∑ sz : I n, f sz := by
    calc
      (∑ sz : I n,
        WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
          x.1.1 y (t - sz + 1) (sz - 1))
          = ∑ sz : I n, f (sz - 1) := by
              refine Finset.sum_congr rfl ?_
              intro sz _
              unfold f
              have hcoord : t - (sz - 1) = t - sz + 1 := by abel
              rw [hcoord]
      _ = ∑ sz : I n, f sz := by
              simpa [sub_eq_add_neg] using
                ((Equiv.addRight (-(1 : I n))).sum_comp
                  (Finset.univ : Finset (I n)) f)
  rw [hshift]
  exact F_add_self _

lemma WCompatPSum_WDiag_diag_zero {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d) (y : YVec n b) (t : I n) :
    (∑ sz : I n,
      WCompatPSum (n := n) (a := a) (b := b) (d := d) hd x.2.1 y (t - sz) sz) = 0 := by
  classical
  rcases x.2.2 with ⟨V, hV⟩
  rw [← hV]
  unfold WCompatPSum WDiagEmbed
  change
    (∑ sz : I n, ∑ p : PVec n a,
      (V p y).1 (vecSum (vecSumRep (n := n) (k := d) hd (t - sz)))
        (vecSum (vecSumRep (n := n) (k := d) hd (t - sz)) + sz)) = 0
  calc
    (∑ sz : I n, ∑ p : PVec n a,
      (V p y).1 (vecSum (vecSumRep (n := n) (k := d) hd (t - sz)))
        (vecSum (vecSumRep (n := n) (k := d) hd (t - sz)) + sz))
        = ∑ sz : I n, ∑ p : PVec n a, (V p y).1 (t - sz) t := by
            refine Finset.sum_congr rfl ?_
            intro sz _
            refine Finset.sum_congr rfl ?_
            intro p _
            rw [vecSum_vecSumRep (n := n) (k := d) hd (t - sz)]
            have hcoord : t - sz + sz = t := by abel
            rw [hcoord]
    _ = ∑ p : PVec n a, ∑ sz : I n, (V p y).1 (t - sz) t := by
            rw [Finset.sum_comm]
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro p _
            have hshift :
                (∑ sz : I n, (V p y).1 (t - sz) t) =
                  ∑ sw : I n, (V p y).1 sw t := by
              simpa using
                ((zmodSubLeftEquiv (n := n) t).sum_comp
                  (fun sw : I n => (V p y).1 sw t))
            rw [hshift]
            exact lineZeroSum_sum_coord (V p y) t

lemma WCompatPSum_WDiag_diag_shift_zero {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d) (y : YVec n b) (t : I n) :
    (∑ sz : I n,
      WCompatPSum (n := n) (a := a) (b := b) (d := d) hd
        x.2.1 y (t - sz + 1) sz) = 0 := by
  classical
  rcases x.2.2 with ⟨V, hV⟩
  rw [← hV]
  unfold WCompatPSum WDiagEmbed
  change
    (∑ sz : I n, ∑ p : PVec n a,
      (V p y).1 (vecSum (vecSumRep (n := n) (k := d) hd (t - sz + 1)))
        (vecSum (vecSumRep (n := n) (k := d) hd (t - sz + 1)) + sz)) = 0
  calc
    (∑ sz : I n, ∑ p : PVec n a,
      (V p y).1 (vecSum (vecSumRep (n := n) (k := d) hd (t - sz + 1)))
        (vecSum (vecSumRep (n := n) (k := d) hd (t - sz + 1)) + sz))
        = ∑ sz : I n, ∑ p : PVec n a, (V p y).1 (t + 1 - sz) (t + 1) := by
            refine Finset.sum_congr rfl ?_
            intro sz _
            refine Finset.sum_congr rfl ?_
            intro p _
            rw [vecSum_vecSumRep (n := n) (k := d) hd (t - sz + 1)]
            have hfirst : t - sz + 1 = t + 1 - sz := by abel
            have hcoord : (t + 1 - sz) + sz = t + 1 := by abel
            rw [hfirst, hcoord]
    _ = ∑ p : PVec n a, ∑ sz : I n, (V p y).1 (t + 1 - sz) (t + 1) := by
            rw [Finset.sum_comm]
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro p _
            have hshift :
                (∑ sz : I n, (V p y).1 (t + 1 - sz) (t + 1)) =
                  ∑ sw : I n, (V p y).1 sw (t + 1) := by
              simpa using
                ((zmodSubLeftEquiv (n := n) (t + 1)).sum_comp
                  (fun sw : I n => (V p y).1 sw (t + 1)))
            rw [hshift]
            exact lineZeroSum_sum_coord (V p y) (t + 1)

lemma WPairRawCurl_diag_zero {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d) (y : YVec n b) (t : I n) :
    (∑ sz : I n,
      WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d)
        hd x y (t - sz) sz) = 0 := by
  classical
  unfold WPairRawCurl
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hroot := WRootFiberSum_diag_cancel
    (n := n) (a := a) (b := b) (c := c) (d := d) hd x y t
  rw [WCompatPSum_WDiag_diag_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hd x y t]
  rw [WCompatPSum_WDiag_diag_shift_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hd x y t]
  simpa [add_assoc] using hroot

noncomputable def WPairCurl {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d) : YVec n b → PairCurlSpace n :=
  fun y =>
    ⟨shearDiagVal (n := n)
      (WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd x y),
      shearDiagVal_mem_MatrixZeroSum
        (WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd x y)
        (WPairRawCurl_col_zero (n := n) (a := a) (b := b) (c := c) (d := d) hd x y)
        (WPairRawCurl_diag_zero (n := n) (a := a) (b := b) (c := c) (d := d) hd x y)⟩

noncomputable def WPairCurlMap {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    WPairAmbient n a b c d →ₗ[F] (YVec n b → PairCurlSpace n) where
  toFun x := WPairCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd x
  map_add' x y := by
    funext y0
    apply Subtype.ext
    funext sz t
    unfold WPairCurl shearDiagVal
    have hraw :=
      congrFun (congrFun (congrFun
        ((WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd).map_add x y)
        y0) (t - sz)) sz
    exact hraw
  map_smul' r x := by
    funext y
    apply Subtype.ext
    funext sz t
    unfold WPairCurl shearDiagVal
    have hraw :=
      congrFun (congrFun (congrFun
        ((WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd).map_smul r x)
        y) (t - sz)) sz
    exact hraw

lemma WPairCurl_eq_zero_iff_raw {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d) :
    WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0 ↔
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0 := by
  constructor
  · intro h
    funext y sw sz
    have hy := congrFun h y
    have hv := congrArg Subtype.val hy
    have hpoint := congrFun (congrFun hv sz) (sw + sz)
    change
      (WPairCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd x y).1 sz (sw + sz) =
        0 at hpoint
    unfold WPairCurl shearDiagVal at hpoint
    change
      WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d)
        hd x y (sw + sz - sz) sz = 0 at hpoint
    have hcoord : sw + sz - sz = sw := by abel
    rw [hcoord] at hpoint
    exact hpoint
  · intro h
    funext y
    apply Subtype.ext
    funext sz t
    change (WPairCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd x y).1 sz t = 0
    unfold WPairCurl shearDiagVal
    exact congrFun (congrFun (congrFun h y) (t - sz)) sz

theorem ker_WPairCurlMap_eq_ker_raw {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    LinearMap.ker (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) =
      LinearMap.ker (WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    exact (WPairCurl_eq_zero_iff_raw (n := n) (a := a) (b := b) (c := c) (d := d) hd x).1
      (LinearMap.mem_ker.mp hx)
  · intro hx
    apply LinearMap.mem_ker.mpr
    exact (WPairCurl_eq_zero_iff_raw (n := n) (a := a) (b := b) (c := c) (d := d) hd x).2
      (LinearMap.mem_ker.mp hx)

end Core4loop
