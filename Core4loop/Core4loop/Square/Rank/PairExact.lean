import Core4loop.Square.Rank.PairCurl

open scoped BigOperators

namespace Core4loop

lemma F_eq_of_add_eq_zero {x y : F} (h : x + y = 0) : x = y := by
  calc
    x = x + 0 := by simp
    _ = x + (x + y) := by rw [h]
    _ = (x + x) + y := by ring
    _ = 0 + y := by rw [F_add_self]
    _ = y := by simp

theorem SquareBMapAmbient_mem_ker_pairCurl
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) (B : BFun4 n a c d) :
    SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B ∈
      LinearMap.ker (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  apply LinearMap.mem_ker.mpr
  exact (BPairCurl_eq_zero_iff_raw
    (n := n) (a := a) (b := b) (c := c) (d := d) hb
    (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B)).2
      (BPairRawCurl_SquareBMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d) hb B)

theorem range_SquareBMapAmbient_le_ker_BPairCurlMap
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    LinearMap.range
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
      LinearMap.ker
        (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  intro x hx
  rcases hx with ⟨B, rfl⟩
  exact SquareBMapAmbient_mem_ker_pairCurl
    (n := n) (a := a) (b := b) (c := c) (d := d) hb B

lemma B_zeroRoot_raw_compat_step
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (w : WVec n d) (sy sz : I n) :
    BCompatPSum (n := n) (a := a) (b := b) (d := d) hb x.2.1 sy sz w +
      BCompatPSum (n := n) (a := a) (b := b) (d := d) hb x.2.1 (sy + 1) sz w = 0 := by
  have hpoint := congrFun (congrFun (congrFun hraw w) sy) sz
  change
    BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb x w sy sz = 0
    at hpoint
  unfold BPairRawCurl at hpoint
  rw [hroot] at hpoint
  simpa [BRootFiberSum] using hpoint

lemma B_zeroRoot_pairCurl_compat_step
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (hroot : x.1.1 = 0)
    (hcurl :
      BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (w : WVec n d) (sy sz : I n) :
    BCompatPSum (n := n) (a := a) (b := b) (d := d) hb x.2.1 sy sz w +
      BCompatPSum (n := n) (a := a) (b := b) (d := d) hb x.2.1 (sy + 1) sz w = 0 := by
  exact B_zeroRoot_raw_compat_step
    (n := n) (a := a) (b := b) (c := c) (d := d) hb x hroot
    ((BPairCurl_eq_zero_iff_raw
      (n := n) (a := a) (b := b) (c := c) (d := d) hb x).1 hcurl)
    w sy sz

noncomputable def BDiagPrimitiveTarget {n a d : ℕ} [NeZero n]
    (V : BDiagCoeff n a d) (p : PVec n a) (w : WVec n d) (t : I n) :
    ZeroSumProfile n :=
  ⟨fun sy => (V p w).1 sy t, by
    apply LinearMap.mem_ker.mpr
    change (∑ sy : I n, (V p w).1 sy t) = 0
    exact lineZeroSum_sum_coord (V p w) t⟩

noncomputable def BDiagPrimitive {n a d : ℕ} [NeZero n]
    (V : BDiagCoeff n a d) (p : PVec n a) (w : WVec n d) (t : I n) :
    Profile n :=
  Classical.choose
    (show ∃ h : Profile n,
        cycDiff (n := n) F h =
          (BDiagPrimitiveTarget (n := n) V p w t).1 by
      have hm :
          (BDiagPrimitiveTarget (n := n) V p w t).1 ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (BDiagPrimitiveTarget (n := n) V p w t).2
      exact hm)

lemma BDiagPrimitive_spec {n a d : ℕ} [NeZero n]
    (V : BDiagCoeff n a d) (p : PVec n a) (w : WVec n d) (t : I n) :
    cycDiff (n := n) F (BDiagPrimitive (n := n) V p w t) =
      (BDiagPrimitiveTarget (n := n) V p w t).1 :=
  Classical.choose_spec
    (show ∃ h : Profile n,
        cycDiff (n := n) F h =
          (BDiagPrimitiveTarget (n := n) V p w t).1 by
      have hm :
          (BDiagPrimitiveTarget (n := n) V p w t).1 ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (BDiagPrimitiveTarget (n := n) V p w t).2
      exact hm)

noncomputable def BZeroRootD {n a d : ℕ} [NeZero n]
    (V : BDiagCoeff n a d) (p : PVec n a) (sy sz : I n) (w : WVec n d) : F :=
  BDiagPrimitive (n := n) V p w (sy + sz) sy

lemma BZeroRootD_diag {n a d : ℕ} [NeZero n]
    (V : BDiagCoeff n a d) (p : PVec n a) (sy sz : I n) (w : WVec n d) :
    BZeroRootD (n := n) V p sy sz w +
        BZeroRootD (n := n) V p (sy + 1) (sz - 1) w =
      (V p w).1 sy (sy + sz) := by
  unfold BZeroRootD
  have hcoord : sy + 1 + (sz - 1) = sy + sz := by abel
  rw [hcoord]
  have hpoint := congrFun (BDiagPrimitive_spec (n := n) V p w (sy + sz)) sy
  simpa [BDiagPrimitiveTarget, cycDiff] using hpoint

lemma BCompatPSum_BDiagEmbed_eq {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (V : BDiagCoeff n a d) (w : WVec n d) (sy sz : I n) :
    BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
        (BDiagEmbed (n := n) (a := a) (b := b) (d := d) V) sy sz w =
      ∑ p : PVec n a, (V p w).1 sy (sy + sz) := by
  unfold BCompatPSum BDiagEmbed
  change
    (∑ p : PVec n a,
      (V p w).1 (vecSum (vecSumRep (n := n) (k := b) hb sy))
        (vecSum (vecSumRep (n := n) (k := b) hb sy) + sz)) =
      ∑ p : PVec n a, (V p w).1 sy (sy + sz)
  rw [vecSum_vecSumRep (n := n) (k := b) hb sy]

lemma BCompatPSum_BDiagEmbed_D {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (V : BDiagCoeff n a d) (w : WVec n d) (sy sz : I n) :
    BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
        (BDiagEmbed (n := n) (a := a) (b := b) (d := d) V) sy sz w =
      ∑ p : PVec n a,
        (BZeroRootD (n := n) V p sy sz w +
          BZeroRootD (n := n) V p (sy + 1) (sz - 1) w) := by
  rw [BCompatPSum_BDiagEmbed_eq (n := n) (a := a) (b := b) (d := d) hb V w sy sz]
  refine Finset.sum_congr rfl ?_
  intro p _
  exact (BZeroRootD_diag (n := n) V p sy sz w).symm

noncomputable def BZeroRootDsum {n a d : ℕ} [NeZero n]
    (V : BDiagCoeff n a d) (sy sz : I n) (w : WVec n d) : F :=
  ∑ p : PVec n a,
    (BZeroRootD (n := n) V p sy sz w +
      BZeroRootD (n := n) V p (sy + 1) sz w)

lemma B_zeroRoot_Dsum_diag_step
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d) (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (w : WVec n d) (sy sz : I n) :
    BZeroRootDsum (n := n) V sy sz w =
      BZeroRootDsum (n := n) V (sy + 1) (sz - 1) w := by
  classical
  have hcompat := B_zeroRoot_raw_compat_step
    (n := n) (a := a) (b := b) (c := c) (d := d) hb x hroot hraw w sy sz
  rw [← hV] at hcompat
  rw [BCompatPSum_BDiagEmbed_D (n := n) (a := a) (b := b) (d := d) hb V w sy sz] at hcompat
  rw [BCompatPSum_BDiagEmbed_D (n := n) (a := a) (b := b) (d := d) hb V w (sy + 1) sz] at hcompat
  have hsum :
      BZeroRootDsum (n := n) V sy sz w +
        BZeroRootDsum (n := n) V (sy + 1) (sz - 1) w = 0 := by
    rw [← Finset.sum_add_distrib] at hcompat
    unfold BZeroRootDsum
    calc
      (∑ p : PVec n a,
          (BZeroRootD (n := n) V p sy sz w +
            BZeroRootD (n := n) V p (sy + 1) sz w)) +
          (∑ p : PVec n a,
            (BZeroRootD (n := n) V p (sy + 1) (sz - 1) w +
              BZeroRootD (n := n) V p (sy + 1 + 1) (sz - 1) w))
          =
        ∑ p : PVec n a,
          ((BZeroRootD (n := n) V p sy sz w +
              BZeroRootD (n := n) V p (sy + 1) sz w) +
            (BZeroRootD (n := n) V p (sy + 1) (sz - 1) w +
              BZeroRootD (n := n) V p (sy + 1 + 1) (sz - 1) w)) := by
            rw [← Finset.sum_add_distrib]
      _ =
        ∑ p : PVec n a,
          ((BZeroRootD (n := n) V p sy sz w +
              BZeroRootD (n := n) V p (sy + 1) (sz - 1) w) +
            (BZeroRootD (n := n) V p (sy + 1) sz w +
              BZeroRootD (n := n) V p (sy + 1 + 1) (sz - 1) w)) := by
            refine Finset.sum_congr rfl ?_
            intro p _
            ring
      _ = 0 := hcompat
  exact F_eq_of_add_eq_zero hsum

lemma B_zeroRoot_Dsum_diag_read
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d) (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (w : WVec n d) (sy sz : I n) :
    BZeroRootDsum (n := n) V sy sz w =
      BZeroRootDsum (n := n) V 0 (sy + sz) w := by
  let t : I n := sy + sz
  let g : I n → F := fun s => BZeroRootDsum (n := n) V s (t - s) w
  have hconst : ∀ s : I n, g (s + 1) = g s := by
    intro s
    unfold g
    have hstep := B_zeroRoot_Dsum_diag_step
      (n := n) (a := a) (b := b) (c := c) (d := d) hb x V hV hroot hraw w s (t - s)
    have hcoord : t - (s + 1) = t - s - 1 := by abel
    rw [hcoord]
    exact hstep.symm
  have hread := zmod_step_const g hconst sy
  have hleft : t - sy = sz := by
    dsimp [t]
    abel
  have hright : t - 0 = sy + sz := by
    dsimp [t]
    abel
  simpa [g, hleft, hright] using hread

lemma BZeroRootDsum_col_zero {n a d : ℕ} [NeZero n]
    (V : BDiagCoeff n a d) (w : WVec n d) (sz : I n) :
    (∑ sy : I n, BZeroRootDsum (n := n) V sy sz w) = 0 := by
  classical
  unfold BZeroRootDsum
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro p _
  rw [Finset.sum_add_distrib]
  have hshift :
      (∑ sy : I n, BZeroRootD (n := n) V p (sy + 1) sz w) =
        ∑ sy : I n, BZeroRootD (n := n) V p sy sz w := by
    simpa using
      ((Equiv.addRight (1 : I n)).sum_comp (Finset.univ : Finset (I n))
        (fun sy : I n => BZeroRootD (n := n) V p sy sz w))
  rw [hshift]
  exact F_add_self _

noncomputable def BZeroRootL {n a d : ℕ} [NeZero n]
    (V : BDiagCoeff n a d) (w : WVec n d) (t : I n) : F :=
  BZeroRootDsum (n := n) V 0 t w

lemma B_zeroRoot_L_zero_sum
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d) (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (w : WVec n d) :
    (∑ t : I n, BZeroRootL (n := n) V w t) = 0 := by
  unfold BZeroRootL
  calc
    (∑ t : I n, BZeroRootDsum (n := n) V 0 t w)
        = ∑ sy : I n, BZeroRootDsum (n := n) V sy 0 w := by
            refine Finset.sum_congr rfl ?_
            intro sy _
            have hread := B_zeroRoot_Dsum_diag_read
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw w sy 0
            simpa using hread.symm
    _ = 0 := BZeroRootDsum_col_zero (n := n) V w 0

noncomputable def BZeroRootLTarget
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (w : WVec n d) : ZeroSumProfile n :=
  ⟨BZeroRootL (n := n) V w,
    LinearMap.mem_ker.mpr
      (B_zeroRoot_L_zero_sum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb x V hV hroot hraw w)⟩

noncomputable def BZeroRootK
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (w : WVec n d) : Profile n :=
  Classical.choose
    (show ∃ h : Profile n,
        cycDiff (n := n) F h =
          (BZeroRootLTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb x V hV hroot hraw w).1 by
      have hm :
          (BZeroRootLTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb x V hV hroot hraw w).1 ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (BZeroRootLTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb x V hV hroot hraw w).2
      exact hm)

lemma BZeroRootK_spec
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (w : WVec n d) :
    cycDiff (n := n) F
        (BZeroRootK
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb x V hV hroot hraw w) =
      (BZeroRootLTarget
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb x V hV hroot hraw w).1 :=
  Classical.choose_spec
    (show ∃ h : Profile n,
        cycDiff (n := n) F h =
          (BZeroRootLTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb x V hV hroot hraw w).1 by
      have hm :
          (BZeroRootLTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb x V hV hroot hraw w).1 ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (BZeroRootLTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb x V hV hroot hraw w).2
      exact hm)

noncomputable def BZeroRootHcorr
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (p : PVec n a) (sy sz : I n) (w : WVec n d) : F :=
  if p = (zeroVec : PVec n a) then
    BZeroRootK
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb x V hV hroot hraw w (sy + sz)
  else 0

noncomputable def BZeroRootG
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (p : PVec n a) (sy sz : I n) (w : WVec n d) : F :=
  BZeroRootD (n := n) V p sy sz w +
    BZeroRootHcorr
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb x V hV hroot hraw p sy sz w

lemma BZeroRootG_diag
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (p : PVec n a) (sy sz : I n) (w : WVec n d) :
    BZeroRootG
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb x V hV hroot hraw p sy sz w +
      BZeroRootG
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb x V hV hroot hraw p (sy + 1) (sz - 1) w =
      (V p w).1 sy (sy + sz) := by
  classical
  unfold BZeroRootG BZeroRootHcorr
  have hcoord : sy + 1 + (sz - 1) = sy + sz := by abel
  by_cases hp : p = (zeroVec : PVec n a)
  · rw [if_pos hp, if_pos hp, hcoord]
    have hdiag := BZeroRootD_diag (n := n) V p sy sz w
    calc
      BZeroRootD (n := n) V p sy sz w +
            BZeroRootK
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw w (sy + sz) +
          (BZeroRootD (n := n) V p (sy + 1) (sz - 1) w +
            BZeroRootK
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw w (sy + sz))
          =
        (BZeroRootD (n := n) V p sy sz w +
          BZeroRootD (n := n) V p (sy + 1) (sz - 1) w) +
          (BZeroRootK
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb x V hV hroot hraw w (sy + sz) +
            BZeroRootK
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw w (sy + sz)) := by ring
      _ = (BZeroRootD (n := n) V p sy sz w +
          BZeroRootD (n := n) V p (sy + 1) (sz - 1) w) + 0 := by
            rw [F_add_self]
      _ = (V p w).1 sy (sy + sz) := by
            simp [hdiag]
  · rw [if_neg hp, if_neg hp]
    simpa using BZeroRootD_diag (n := n) V p sy sz w

lemma BZeroRootHcorr_y_sum
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (sy sz : I n) (w : WVec n d) :
    (∑ p : PVec n a,
      (BZeroRootHcorr
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb x V hV hroot hraw p sy sz w +
        BZeroRootHcorr
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb x V hV hroot hraw p (sy + 1) sz w)) =
      BZeroRootL (n := n) V w (sy + sz) := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · unfold BZeroRootHcorr
    rw [if_pos rfl, if_pos rfl]
    have hcoord : sy + 1 + sz = sy + sz + 1 := by abel
    rw [hcoord]
    have hpoint := congrFun
      (BZeroRootK_spec
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb x V hV hroot hraw w) (sy + sz)
    simpa [BZeroRootLTarget, BZeroRootL, cycDiff] using hpoint
  · intro p _ hp
    unfold BZeroRootHcorr
    rw [if_neg hp, if_neg hp]
    simp
  · simp

lemma BZeroRootG_y_sum
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (sy sz : I n) (w : WVec n d) :
    (∑ p : PVec n a,
      (BZeroRootG
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb x V hV hroot hraw p sy sz w +
        BZeroRootG
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb x V hV hroot hraw p (sy + 1) sz w)) = 0 := by
  classical
  have hdiag := B_zeroRoot_Dsum_diag_read
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb x V hV hroot hraw w sy sz
  have hcorr := BZeroRootHcorr_y_sum
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb x V hV hroot hraw sy sz w
  unfold BZeroRootG
  calc
    (∑ p : PVec n a,
      ((BZeroRootD (n := n) V p sy sz w +
            BZeroRootHcorr
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw p sy sz w) +
        (BZeroRootD (n := n) V p (sy + 1) sz w +
            BZeroRootHcorr
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw p (sy + 1) sz w)))
        =
      BZeroRootDsum (n := n) V sy sz w +
        (∑ p : PVec n a,
          (BZeroRootHcorr
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw p sy sz w +
            BZeroRootHcorr
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw p (sy + 1) sz w)) := by
            unfold BZeroRootDsum
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro p _
            ring
    _ = BZeroRootL (n := n) V w (sy + sz) +
          BZeroRootL (n := n) V w (sy + sz) := by
            rw [hdiag, hcorr]
            rfl
    _ = 0 := F_add_self _

noncomputable def BZeroRootBFun
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0) :
    BFun4 n a c d :=
  fun p sy z w =>
    if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
      BZeroRootG
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb x V hV hroot hraw p sy (vecSum z) w
    else 0

lemma B_zeroRoot_fiber
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (p : PVec n a) (sy sz : I n) (w : WVec n d) :
    BFiber (n := n) (a := a) (c := c) (d := d)
        (BZeroRootBFun
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc x V hV hroot hraw) p sy sz w =
      BZeroRootG
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb x V hV hroot hraw p sy sz w := by
  classical
  unfold BFiber BZeroRootBFun
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

lemma BZeroRootBFun_KBMap_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
      (BZeroRootBFun
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc x V hV hroot hraw) = 0 := by
  classical
  funext y z w
  unfold KBMap dyB betaB gammaB BZeroRootBFun
  by_cases hz : z = vecSumRep (n := n) (k := c) hc (vecSum z)
  · have hy := BZeroRootG_y_sum
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb x V hV hroot hraw (vecSum y) (vecSum z) w
    calc
      (∑ p : PVec n a,
        ((if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
            BZeroRootG
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw p (vecSum y) (vecSum z) w
          else 0) +
          (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
            BZeroRootG
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw p (vecSum y + 1) (vecSum z) w
          else 0)))
          =
        ∑ p : PVec n a,
          (BZeroRootG
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw p (vecSum y) (vecSum z) w +
            BZeroRootG
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb x V hV hroot hraw p (vecSum y + 1) (vecSum z) w) := by
            refine Finset.sum_congr rfl ?_
            intro p _
            rw [if_pos hz, if_pos hz]
      _ = 0 := hy
  · apply Finset.sum_eq_zero
    intro p _
    change
      (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
        BZeroRootG
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb x V hV hroot hraw p (vecSum y) (vecSum z) w
      else 0) +
        (if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
          BZeroRootG
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb x V hV hroot hraw p (vecSum y + 1) (vecSum z) w
        else 0) = 0
    rw [if_neg hz, if_neg hz]
    simp

lemma BZeroRootBFun_squareCompat
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (x : BPairAmbient n a b c d)
    (V : BDiagCoeff n a d)
    (hV : BDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0) :
    ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
      (BZeroRootBFun
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc x V hV hroot hraw) =
      BDiagEmbed (n := n) (a := a) (b := b) (d := d) V := by
  classical
  let B : BFun4 n a c d :=
    BZeroRootBFun
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc x V hV hroot hraw
  funext p y sz w
  change squareCompatFun B 0 p y sz w =
    (BDiagEmbed (n := n) (a := a) (b := b) (d := d) V) p y sz w
  unfold squareCompatFun betaB gammaB xiW zetaW BDiagEmbed
  simp only [Pi.zero_apply, add_zero]
  change
    (∑ z : ZVec n c, if vecSum z = sz then B p (vecSum y) z w else 0) +
        (∑ z : ZVec n c, if vecSum z + 1 = sz then B p (vecSum y + 1) z w else 0) =
      (V p w).1 (vecSum y) (vecSum y + sz)
  have hfirst :
      (∑ z : ZVec n c, if vecSum z = sz then B p (vecSum y) z w else 0) =
        BZeroRootG
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb x V hV hroot hraw p (vecSum y) sz w := by
    simpa [B] using
      B_zeroRoot_fiber
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc x V hV hroot hraw p (vecSum y) sz w
  have hsecond_fiber :
      (∑ z : ZVec n c, if vecSum z + 1 = sz then B p (vecSum y + 1) z w else 0) =
        BFiber (n := n) (a := a) (c := c) (d := d)
          B p (vecSum y + 1) (sz - 1) w := by
    unfold BFiber
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
      (∑ z : ZVec n c, if vecSum z + 1 = sz then B p (vecSum y + 1) z w else 0) =
        BZeroRootG
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb x V hV hroot hraw p (vecSum y + 1) (sz - 1) w := by
    rw [hsecond_fiber]
    simpa [B] using
      B_zeroRoot_fiber
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc x V hV hroot hraw p (vecSum y + 1) (sz - 1) w
  rw [hfirst, hsecond]
  exact BZeroRootG_diag
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb x V hV hroot hraw p (vecSum y) sz w

theorem BPair_zeroRoot_mem_range
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (x : BPairAmbient n a b c d)
    (hroot : x.1.1 = 0)
    (hcurl :
      BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0) :
    x ∈ LinearMap.range
      (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  classical
  have hraw :=
    (BPairCurl_eq_zero_iff_raw
      (n := n) (a := a) (b := b) (c := c) (d := d) hb x).1 hcurl
  rcases x.2.2 with ⟨V, hV⟩
  let B : BFun4 n a c d :=
    BZeroRootBFun
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc x V hV hroot hraw
  refine ⟨B, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    change
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B = x.1.1
    calc
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
          = 0 := by
            simpa [B] using
              BZeroRootBFun_KBMap_zero
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc x V hV hroot hraw
      _ = x.1.1 := hroot.symm
  · apply Subtype.ext
    change
      (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) B) =
        x.2.1
    calc
      (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) B)
          = BDiagEmbed (n := n) (a := a) (b := b) (d := d) V := by
            simpa [B] using
              BZeroRootBFun_squareCompat
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc x V hV hroot hraw
      _ = x.2.1 := hV

theorem ker_BPairCurlMap_eq_range_SquareBMapAmbient
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    LinearMap.ker
        (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) =
      LinearMap.range
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  apply le_antisymm
  · intro x hx
    have hxroot_range :
        x.1.1 ∈ LinearMap.range
          (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      rw [range_KBMap_eq_YDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
      exact x.1.2
    rcases hxroot_range with ⟨B0, hB0⟩
    let x0 : BPairAmbient n a b c d :=
      SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B0
    have hx0root : x0.1.1 = x.1.1 := by
      change KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B0 = x.1.1
      exact hB0
    have hx0ker :
        x0 ∈ LinearMap.ker
          (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
      exact SquareBMapAmbient_mem_ker_pairCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb B0
    have hyroot : (x + x0).1.1 = 0 := by
      change x.1.1 + x0.1.1 = 0
      rw [hx0root]
      exact F_module_add_self x.1.1
    have hyker :
        x + x0 ∈ LinearMap.ker
          (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) :=
      Submodule.add_mem _ hx hx0ker
    have hyrange : x + x0 ∈
        LinearMap.range
          (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      exact BPair_zeroRoot_mem_range
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc (x + x0) hyroot (LinearMap.mem_ker.mp hyker)
    have hx0range : x0 ∈
        LinearMap.range
          (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) :=
      ⟨B0, rfl⟩
    have hsumrange : x0 + (x + x0) ∈
        LinearMap.range
          (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) :=
      Submodule.add_mem _ hx0range hyrange
    have hxsum : x0 + (x + x0) = x := by
      calc
        x0 + (x + x0) = x + (x0 + x0) := by
          abel
        _ = x + 0 := by rw [F_module_add_self x0]
        _ = x := by simp
    rw [hxsum] at hsumrange
    exact hsumrange
  · exact range_SquareBMapAmbient_le_ker_BPairCurlMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hb

theorem SquareWMapAmbient_mem_ker_pairCurl
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) (W : WFun4 n a b c) :
    SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W ∈
      LinearMap.ker (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) := by
  apply LinearMap.mem_ker.mpr
  exact (WPairCurl_eq_zero_iff_raw
    (n := n) (a := a) (b := b) (c := c) (d := d) hd
    (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W)).2
      (WPairRawCurl_SquareWMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d) hd W)

theorem range_SquareWMapAmbient_le_ker_WPairCurlMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    LinearMap.range
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
      LinearMap.ker
        (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) := by
  intro x hx
  rcases hx with ⟨W, rfl⟩
  exact SquareWMapAmbient_mem_ker_pairCurl
    (n := n) (a := a) (b := b) (c := c) (d := d) hd W

lemma W_zeroRoot_raw_compat_step
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (y : YVec n b) (sw sz : I n) :
    WCompatPSum (n := n) (a := a) (b := b) (d := d) hd x.2.1 y sw sz +
      WCompatPSum (n := n) (a := a) (b := b) (d := d) hd x.2.1 y (sw + 1) sz = 0 := by
  have hpoint := congrFun (congrFun (congrFun hraw y) sw) sz
  change
    WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd x y sw sz = 0
    at hpoint
  unfold WPairRawCurl at hpoint
  rw [hroot] at hpoint
  simpa [WRootFiberSum] using hpoint

lemma W_zeroRoot_pairCurl_compat_step
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (hroot : x.1.1 = 0)
    (hcurl :
      WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (y : YVec n b) (sw sz : I n) :
    WCompatPSum (n := n) (a := a) (b := b) (d := d) hd x.2.1 y sw sz +
      WCompatPSum (n := n) (a := a) (b := b) (d := d) hd x.2.1 y (sw + 1) sz = 0 := by
  exact W_zeroRoot_raw_compat_step
    (n := n) (a := a) (b := b) (c := c) (d := d) hd x hroot
    ((WPairCurl_eq_zero_iff_raw
      (n := n) (a := a) (b := b) (c := c) (d := d) hd x).1 hcurl)
    y sw sz

noncomputable def WDiagPrimitiveTarget {n a b : ℕ} [NeZero n]
    (V : WDiagCoeff n a b) (p : PVec n a) (y : YVec n b) (t : I n) :
    ZeroSumProfile n :=
  ⟨fun sw => (V p y).1 sw t, by
    apply LinearMap.mem_ker.mpr
    change (∑ sw : I n, (V p y).1 sw t) = 0
    exact lineZeroSum_sum_coord (V p y) t⟩

noncomputable def WDiagPrimitive {n a b : ℕ} [NeZero n]
    (V : WDiagCoeff n a b) (p : PVec n a) (y : YVec n b) (t : I n) :
    Profile n :=
  Classical.choose
    (show ∃ h : Profile n,
        cycDiff (n := n) F h =
          (WDiagPrimitiveTarget (n := n) V p y t).1 by
      have hm :
          (WDiagPrimitiveTarget (n := n) V p y t).1 ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (WDiagPrimitiveTarget (n := n) V p y t).2
      exact hm)

lemma WDiagPrimitive_spec {n a b : ℕ} [NeZero n]
    (V : WDiagCoeff n a b) (p : PVec n a) (y : YVec n b) (t : I n) :
    cycDiff (n := n) F (WDiagPrimitive (n := n) V p y t) =
      (WDiagPrimitiveTarget (n := n) V p y t).1 :=
  Classical.choose_spec
    (show ∃ h : Profile n,
        cycDiff (n := n) F h =
          (WDiagPrimitiveTarget (n := n) V p y t).1 by
      have hm :
          (WDiagPrimitiveTarget (n := n) V p y t).1 ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact (WDiagPrimitiveTarget (n := n) V p y t).2
      exact hm)

noncomputable def WZeroRootD {n a b : ℕ} [NeZero n]
    (V : WDiagCoeff n a b) (p : PVec n a) (y : YVec n b) (sw sz : I n) : F :=
  WDiagPrimitive (n := n) V p y (sw + sz) sw

lemma WZeroRootD_diag {n a b : ℕ} [NeZero n]
    (V : WDiagCoeff n a b) (p : PVec n a) (y : YVec n b) (sw sz : I n) :
    WZeroRootD (n := n) V p y sw sz +
        WZeroRootD (n := n) V p y (sw + 1) (sz - 1) =
      (V p y).1 sw (sw + sz) := by
  unfold WZeroRootD
  have hcoord : sw + 1 + (sz - 1) = sw + sz := by abel
  rw [hcoord]
  have hpoint := congrFun (WDiagPrimitive_spec (n := n) V p y (sw + sz)) sw
  simpa [WDiagPrimitiveTarget, cycDiff] using hpoint

lemma WCompatPSum_WDiagEmbed_eq {n a b d : ℕ} [NeZero n]
    (hd : 0 < d) (V : WDiagCoeff n a b) (y : YVec n b) (sw sz : I n) :
    WCompatPSum (n := n) (a := a) (b := b) (d := d) hd
        (WDiagEmbed (n := n) (a := a) (b := b) (d := d) V) y sw sz =
      ∑ p : PVec n a, (V p y).1 sw (sw + sz) := by
  unfold WCompatPSum WDiagEmbed
  change
    (∑ p : PVec n a,
      (V p y).1 (vecSum (vecSumRep (n := n) (k := d) hd sw))
        (vecSum (vecSumRep (n := n) (k := d) hd sw) + sz)) =
      ∑ p : PVec n a, (V p y).1 sw (sw + sz)
  rw [vecSum_vecSumRep (n := n) (k := d) hd sw]

lemma WCompatPSum_WDiagEmbed_D {n a b d : ℕ} [NeZero n]
    (hd : 0 < d) (V : WDiagCoeff n a b) (y : YVec n b) (sw sz : I n) :
    WCompatPSum (n := n) (a := a) (b := b) (d := d) hd
        (WDiagEmbed (n := n) (a := a) (b := b) (d := d) V) y sw sz =
      ∑ p : PVec n a,
        (WZeroRootD (n := n) V p y sw sz +
          WZeroRootD (n := n) V p y (sw + 1) (sz - 1)) := by
  rw [WCompatPSum_WDiagEmbed_eq (n := n) (a := a) (b := b) (d := d) hd V y sw sz]
  refine Finset.sum_congr rfl ?_
  intro p _
  exact (WZeroRootD_diag (n := n) V p y sw sz).symm

noncomputable def WZeroRootDsum {n a b : ℕ} [NeZero n]
    (V : WDiagCoeff n a b) (y : YVec n b) (sw sz : I n) : F :=
  ∑ p : PVec n a,
    (WZeroRootD (n := n) V p y sw sz +
      WZeroRootD (n := n) V p y (sw + 1) sz)

lemma W_zeroRoot_Dsum_diag_step
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b) (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (y : YVec n b) (sw sz : I n) :
    WZeroRootDsum (n := n) V y sw sz =
      WZeroRootDsum (n := n) V y (sw + 1) (sz - 1) := by
  classical
  have hcompat := W_zeroRoot_raw_compat_step
    (n := n) (a := a) (b := b) (c := c) (d := d) hd x hroot hraw y sw sz
  rw [← hV] at hcompat
  rw [WCompatPSum_WDiagEmbed_D (n := n) (a := a) (b := b) (d := d) hd V y sw sz] at hcompat
  rw [WCompatPSum_WDiagEmbed_D (n := n) (a := a) (b := b) (d := d) hd V y (sw + 1) sz] at hcompat
  have hsum :
      WZeroRootDsum (n := n) V y sw sz +
        WZeroRootDsum (n := n) V y (sw + 1) (sz - 1) = 0 := by
    rw [← Finset.sum_add_distrib] at hcompat
    unfold WZeroRootDsum
    calc
      (∑ p : PVec n a,
          (WZeroRootD (n := n) V p y sw sz +
            WZeroRootD (n := n) V p y (sw + 1) sz)) +
          (∑ p : PVec n a,
            (WZeroRootD (n := n) V p y (sw + 1) (sz - 1) +
              WZeroRootD (n := n) V p y (sw + 1 + 1) (sz - 1)))
          =
        ∑ p : PVec n a,
          ((WZeroRootD (n := n) V p y sw sz +
              WZeroRootD (n := n) V p y (sw + 1) sz) +
            (WZeroRootD (n := n) V p y (sw + 1) (sz - 1) +
              WZeroRootD (n := n) V p y (sw + 1 + 1) (sz - 1))) := by
            rw [← Finset.sum_add_distrib]
      _ =
        ∑ p : PVec n a,
          ((WZeroRootD (n := n) V p y sw sz +
              WZeroRootD (n := n) V p y (sw + 1) (sz - 1)) +
            (WZeroRootD (n := n) V p y (sw + 1) sz +
              WZeroRootD (n := n) V p y (sw + 1 + 1) (sz - 1))) := by
            refine Finset.sum_congr rfl ?_
            intro p _
            ring
      _ = 0 := hcompat
  exact F_eq_of_add_eq_zero hsum

lemma W_zeroRoot_Dsum_diag_read
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b) (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (y : YVec n b) (sw sz : I n) :
    WZeroRootDsum (n := n) V y sw sz =
      WZeroRootDsum (n := n) V y 0 (sw + sz) := by
  let t : I n := sw + sz
  let g : I n → F := fun s => WZeroRootDsum (n := n) V y s (t - s)
  have hconst : ∀ s : I n, g (s + 1) = g s := by
    intro s
    unfold g
    have hstep := W_zeroRoot_Dsum_diag_step
      (n := n) (a := a) (b := b) (c := c) (d := d) hd x V hV hroot hraw y s (t - s)
    have hcoord : t - (s + 1) = t - s - 1 := by abel
    rw [hcoord]
    exact hstep.symm
  have hread := zmod_step_const g hconst sw
  have hleft : t - sw = sz := by
    dsimp [t]
    abel
  have hright : t - 0 = sw + sz := by
    dsimp [t]
    abel
  simpa [g, hleft, hright] using hread

lemma WZeroRootDsum_col_zero {n a b : ℕ} [NeZero n]
    (V : WDiagCoeff n a b) (y : YVec n b) (sz : I n) :
    (∑ sw : I n, WZeroRootDsum (n := n) V y sw sz) = 0 := by
  classical
  unfold WZeroRootDsum
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro p _
  rw [Finset.sum_add_distrib]
  have hshift :
      (∑ sw : I n, WZeroRootD (n := n) V p y (sw + 1) sz) =
        ∑ sw : I n, WZeroRootD (n := n) V p y sw sz := by
    simpa using
      ((Equiv.addRight (1 : I n)).sum_comp (Finset.univ : Finset (I n))
        (fun sw : I n => WZeroRootD (n := n) V p y sw sz))
  rw [hshift]
  exact F_add_self _

noncomputable def WZeroRootL {n a b : ℕ} [NeZero n]
    (V : WDiagCoeff n a b) (y : YVec n b) (t : I n) : F :=
  WZeroRootDsum (n := n) V y 0 t

lemma W_zeroRoot_L_zero_sum
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : WPairAmbient n a b c d)
    (V : WDiagCoeff n a b) (hV : WDiagEmbed (n := n) (a := a) (b := b) (d := d) V = x.2.1)
    (hroot : x.1.1 = 0)
    (hraw :
      WPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (y : YVec n b) :
    (∑ t : I n, WZeroRootL (n := n) V y t) = 0 := by
  unfold WZeroRootL
  calc
    (∑ t : I n, WZeroRootDsum (n := n) V y 0 t)
        = ∑ sw : I n, WZeroRootDsum (n := n) V y sw 0 := by
            refine Finset.sum_congr rfl ?_
            intro sw _
            have hread := W_zeroRoot_Dsum_diag_read
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hd x V hV hroot hraw y sw 0
            simpa using hread.symm
    _ = 0 := WZeroRootDsum_col_zero (n := n) V y 0

end Core4loop
