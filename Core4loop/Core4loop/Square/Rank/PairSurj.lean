import Core4loop.Square.Rank.PairCurl

open scoped BigOperators

namespace Core4loop

noncomputable def BSurjTargetProfile {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (t : I n) :
    ZeroSumProfile n :=
  ⟨fun r => (T w).1 (r + 1) t, by
    classical
    apply LinearMap.mem_ker.mpr
    change (∑ r : I n, (T w).1 (r + 1) t) = 0
    have hshift :
        (∑ r : I n, (T w).1 (r + 1) t) =
          ∑ r : I n, (T w).1 r t := by
      simpa using
        ((Equiv.addRight (1 : I n)).sum_comp (Finset.univ : Finset (I n))
          (fun r : I n => (T w).1 r t))
    rw [hshift]
    exact matrix_col_zero (T w) t⟩

noncomputable def BSurjH {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (t : I n) :
    Profile n :=
  Classical.choose
    (show ∃ h : Profile n,
        cycDiff (n := n) F h = (BSurjTargetProfile (n := n) T w t).1 by
      have hm :
          (BSurjTargetProfile (n := n) T w t).1 ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (BSurjTargetProfile (n := n) T w t).2
      exact hm)

lemma BSurjH_spec {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (t : I n) :
    cycDiff (n := n) F (BSurjH (n := n) T w t) =
      (BSurjTargetProfile (n := n) T w t).1 :=
  Classical.choose_spec
    (show ∃ h : Profile n,
        cycDiff (n := n) F h = (BSurjTargetProfile (n := n) T w t).1 by
      have hm :
          (BSurjTargetProfile (n := n) T w t).1 ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (BSurjTargetProfile (n := n) T w t).2
      exact hm)

noncomputable def BSurjA0 {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (r t : I n) : F :=
  BSurjH (n := n) T w t r

lemma BSurjA0_curl {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (r t : I n) :
    BSurjA0 (n := n) T w r t +
        BSurjA0 (n := n) T w (r - 1) t =
      (T w).1 r t := by
  have hpoint := congrFun (BSurjH_spec (n := n) T w t) (r - 1)
  have hcoord : (r - 1) + 1 = r := by abel
  simpa [BSurjA0, BSurjTargetProfile, cycDiff, hcoord, add_comm] using hpoint

noncomputable def BSurjS0 {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (r : I n) : F :=
  ∑ t : I n, BSurjA0 (n := n) T w r t

lemma BSurjS0_step {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (r : I n) :
    BSurjS0 (n := n) T w (r + 1) = BSurjS0 (n := n) T w r := by
  classical
  have hsum :
      BSurjS0 (n := n) T w (r + 1) + BSurjS0 (n := n) T w r = 0 := by
    calc
      BSurjS0 (n := n) T w (r + 1) + BSurjS0 (n := n) T w r
          =
        ∑ t : I n,
          (BSurjA0 (n := n) T w (r + 1) t +
            BSurjA0 (n := n) T w r t) := by
            unfold BSurjS0
            rw [← Finset.sum_add_distrib]
      _ = ∑ t : I n, (T w).1 (r + 1) t := by
            refine Finset.sum_congr rfl ?_
            intro t _
            simpa using BSurjA0_curl (n := n) T w (r + 1) t
      _ = 0 := matrix_row_zero (T w) (r + 1)
  calc
    BSurjS0 (n := n) T w (r + 1)
        = BSurjS0 (n := n) T w (r + 1) + 0 := by simp
    _ = BSurjS0 (n := n) T w (r + 1) +
          (BSurjS0 (n := n) T w r + BSurjS0 (n := n) T w r) := by
            rw [F_add_self]
    _ = BSurjS0 (n := n) T w r := by
            rw [← add_assoc, hsum]
            simp

lemma BSurjS0_const {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (r : I n) :
    BSurjS0 (n := n) T w r = BSurjS0 (n := n) T w 0 :=
  zmod_step_const (fun r : I n => BSurjS0 (n := n) T w r)
    (BSurjS0_step (n := n) T w) r

noncomputable def BSurjA {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (r t : I n) : F :=
  BSurjA0 (n := n) T w r t +
    if t = 0 then BSurjS0 (n := n) T w 0 else 0

lemma BSurjA_curl {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (r t : I n) :
    BSurjA (n := n) T w r t +
        BSurjA (n := n) T w (r - 1) t =
      (T w).1 r t := by
  unfold BSurjA
  by_cases ht : t = 0
  · subst ht
    have hcurl := BSurjA0_curl (n := n) T w r 0
    rw [if_pos rfl]
    change
      BSurjA0 (n := n) T w r 0 + BSurjS0 (n := n) T w 0 +
          (BSurjA0 (n := n) T w (r - 1) 0 + BSurjS0 (n := n) T w 0) =
        (T w).1 r 0
    calc
      BSurjA0 (n := n) T w r 0 + BSurjS0 (n := n) T w 0 +
          (BSurjA0 (n := n) T w (r - 1) 0 + BSurjS0 (n := n) T w 0)
          =
        (BSurjA0 (n := n) T w r 0 + BSurjA0 (n := n) T w (r - 1) 0) +
          (BSurjS0 (n := n) T w 0 + BSurjS0 (n := n) T w 0) := by ring
      _ = (BSurjA0 (n := n) T w r 0 + BSurjA0 (n := n) T w (r - 1) 0) + 0 := by
            rw [F_add_self]
      _ = (T w).1 r 0 := by
            simp [hcurl]
  · simp [ht, BSurjA0_curl (n := n) T w r t]

lemma BSurjA_row_zero {n d : ℕ} [NeZero n]
    (T : WVec n d → PairCurlSpace n) (w : WVec n d) (r : I n) :
    (∑ t : I n, BSurjA (n := n) T w r t) = 0 := by
  classical
  unfold BSurjA
  rw [Finset.sum_add_distrib]
  have hsingle :
      (∑ t : I n,
        if t = 0 then BSurjS0 (n := n) T w 0 else 0) =
        BSurjS0 (n := n) T w 0 := by
    rw [Finset.sum_eq_single (0 : I n)]
    · simp
    · intro t _ ht
      simp [ht]
    · simp
  rw [hsingle]
  change BSurjS0 (n := n) T w r + BSurjS0 (n := n) T w 0 = 0
  rw [BSurjS0_const (n := n) T w r]
  exact F_add_self _

noncomputable def BSurjU {n c d : ℕ} [NeZero n] (hc : 0 < c)
    (T : WVec n d → PairCurlSpace n) : YCoeff n c d :=
  fun z w =>
    ⟨fun sy =>
        if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
          BSurjA (n := n) T w (vecSum z) (sy + vecSum z)
        else 0,
      by
        classical
        apply LinearMap.mem_ker.mpr
        change
          (∑ sy : I n,
            (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
              BSurjA (n := n) T w (vecSum z) (sy + vecSum z)
            else 0)) = 0
        by_cases hz : z = vecSumRep (n := n) (k := c) hc (vecSum z)
        · have hif :
              (∑ sy : I n,
                (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
                  BSurjA (n := n) T w (vecSum z) (sy + vecSum z)
                else 0)) =
                ∑ sy : I n, BSurjA (n := n) T w (vecSum z) (sy + vecSum z) := by
            refine Finset.sum_congr rfl ?_
            intro sy _
            rw [if_pos hz]
          rw [hif]
          have hshift :
              (∑ sy : I n,
                BSurjA (n := n) T w (vecSum z) (sy + vecSum z)) =
                ∑ t : I n, BSurjA (n := n) T w (vecSum z) t := by
            simpa using
              ((Equiv.addRight (vecSum z)).sum_comp
                (Finset.univ : Finset (I n))
                (fun t : I n => BSurjA (n := n) T w (vecSum z) t))
          rw [hshift]
          exact BSurjA_row_zero (n := n) T w (vecSum z)
        · apply Finset.sum_eq_zero
          intro sy _
          rw [if_neg hz]⟩

noncomputable def BSurjAmbient {n a b c d : ℕ} [NeZero n] (hc : 0 < c)
    (T : WVec n d → PairCurlSpace n) : BPairAmbient n a b c d :=
  (⟨YDiffEmbed (n := n) (b := b) (c := c) (d := d) (BSurjU (n := n) hc T),
      ⟨BSurjU (n := n) hc T, rfl⟩⟩,
    0)

lemma BSurj_root_fiber {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (T : WVec n d → PairCurlSpace n)
    (w : WVec n d) (sy sz : I n) :
    BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
        (YDiffEmbed (n := n) (b := b) (c := c) (d := d)
          (BSurjU (n := n) hc T)) sy sz w =
      BSurjA (n := n) T w sz (sy + sz) := by
  classical
  unfold BRootFiberSum YDiffEmbed BSurjU
  change
    (∑ z : ZVec n c,
      if vecSum z = sz then
        (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
          BSurjA (n := n) T w (vecSum z)
            (vecSum (vecSumRep (n := n) (k := b) hb sy) + vecSum z)
        else 0)
      else 0) =
    BSurjA (n := n) T w sz (sy + sz)
  rw [Finset.sum_eq_single (vecSumRep (n := n) (k := c) hc sz)]
  · rw [vecSum_vecSumRep (n := n) (k := c) hc sz,
      vecSum_vecSumRep (n := n) (k := b) hb sy]
    simp
  · intro z _ hz
    by_cases hzs : vecSum z = sz
    · have hnot : z ≠ vecSumRep (n := n) (k := c) hc (vecSum z) := by
        intro h
        apply hz
        rw [h, hzs]
      rw [if_pos hzs, if_neg hnot]
    · simp [hzs]
  · simp

theorem BPairCurlMap_surjective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Function.Surjective
      (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  classical
  intro T
  refine ⟨BSurjAmbient (n := n) (a := a) (b := b) (c := c) (d := d) hc T, ?_⟩
  funext w
  apply Subtype.ext
  funext sz t
  change
    shearDiagVal (n := n)
      (BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb
        (BSurjAmbient (n := n) (a := a) (b := b) (c := c) (d := d) hc T) w)
        sz t =
      (T w).1 sz t
  unfold shearDiagVal BPairRawCurl BSurjAmbient
  rw [BSurj_root_fiber (n := n) (b := b) (c := c) (d := d)
    hb hc T w (t - sz) sz]
  rw [BSurj_root_fiber (n := n) (b := b) (c := c) (d := d)
    hb hc T w (t - sz + 1) (sz - 1)]
  have hcoord₁ : (t - sz) + sz = t := by abel
  have hcoord₂ : (t - sz + 1) + (sz - 1) = t := by abel
  simp [BCompatPSum, hcoord₁, hcoord₂, BSurjA_curl (n := n) T w sz t]

noncomputable def WSurjU {n b c : ℕ} [NeZero n] (hc : 0 < c)
    (T : YVec n b → PairCurlSpace n) : WCoeff n b c :=
  fun y z =>
    ⟨fun sw =>
        if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
          BSurjA (n := n) T y (vecSum z) (sw + vecSum z)
        else 0,
      by
        classical
        apply LinearMap.mem_ker.mpr
        change
          (∑ sw : I n,
            (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
              BSurjA (n := n) T y (vecSum z) (sw + vecSum z)
            else 0)) = 0
        by_cases hz : z = vecSumRep (n := n) (k := c) hc (vecSum z)
        · have hif :
              (∑ sw : I n,
                (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
                  BSurjA (n := n) T y (vecSum z) (sw + vecSum z)
                else 0)) =
                ∑ sw : I n, BSurjA (n := n) T y (vecSum z) (sw + vecSum z) := by
            refine Finset.sum_congr rfl ?_
            intro sw _
            rw [if_pos hz]
          rw [hif]
          have hshift :
              (∑ sw : I n,
                BSurjA (n := n) T y (vecSum z) (sw + vecSum z)) =
                ∑ t : I n, BSurjA (n := n) T y (vecSum z) t := by
            simpa using
              ((Equiv.addRight (vecSum z)).sum_comp
                (Finset.univ : Finset (I n))
                (fun t : I n => BSurjA (n := n) T y (vecSum z) t))
          rw [hshift]
          exact BSurjA_row_zero (n := n) T y (vecSum z)
        · apply Finset.sum_eq_zero
          intro sw _
          rw [if_neg hz]⟩

noncomputable def WSurjAmbient {n a b c d : ℕ} [NeZero n] (hc : 0 < c)
    (T : YVec n b → PairCurlSpace n) : WPairAmbient n a b c d :=
  (⟨WDiffEmbed (n := n) (b := b) (c := c) (d := d) (WSurjU (n := n) hc T),
      ⟨WSurjU (n := n) hc T, rfl⟩⟩,
    0)

lemma WSurj_root_fiber {n b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) (T : YVec n b → PairCurlSpace n)
    (y : YVec n b) (sw sz : I n) :
    WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
        (WDiffEmbed (n := n) (b := b) (c := c) (d := d)
          (WSurjU (n := n) hc T)) y sw sz =
      BSurjA (n := n) T y sz (sw + sz) := by
  classical
  unfold WRootFiberSum WDiffEmbed WSurjU
  change
    (∑ z : ZVec n c,
      if vecSum z = sz then
        (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
          BSurjA (n := n) T y (vecSum z)
            (vecSum (vecSumRep (n := n) (k := d) hd sw) + vecSum z)
        else 0)
      else 0) =
    BSurjA (n := n) T y sz (sw + sz)
  rw [Finset.sum_eq_single (vecSumRep (n := n) (k := c) hc sz)]
  · rw [vecSum_vecSumRep (n := n) (k := c) hc sz,
      vecSum_vecSumRep (n := n) (k := d) hd sw]
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

theorem WPairCurlMap_surjective
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    Function.Surjective
      (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) := by
  classical
  intro T
  refine ⟨WSurjAmbient (n := n) (a := a) (b := b) (c := c) (d := d) hc T, ?_⟩
  funext y
  apply Subtype.ext
  funext sz t
  change
    shearDiagVal (n := n)
      (WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (WSurjAmbient (n := n) (a := a) (b := b) (c := c) (d := d) hc T) y)
        sz t =
      (T y).1 sz t
  unfold shearDiagVal WPairRawCurl WSurjAmbient
  rw [WSurj_root_fiber (n := n) (b := b) (c := c) (d := d)
    hc hd T y (t - sz) sz]
  rw [WSurj_root_fiber (n := n) (b := b) (c := c) (d := d)
    hc hd T y (t - sz + 1) (sz - 1)]
  have hcoord₁ : (t - sz) + sz = t := by abel
  have hcoord₂ : (t - sz + 1) + (sz - 1) = t := by abel
  simp [WCompatPSum, hcoord₁, hcoord₂, BSurjA_curl (n := n) T y sz t]

end Core4loop
