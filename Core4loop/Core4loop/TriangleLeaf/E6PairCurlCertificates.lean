import Core4loop.Square.Rank.BPairCurlCore
import Core4loop.RootSpaces.PullYZ

/-!
# Triangle+leaf E6 pair-curl certificates

The source spaces and linear maps in this module are logical-level 1
definitions.  The pointwise formulas, explicit sections, range equality,
injectivity, finrank, and surjectivity results are logical-level 5 structural
certificates.  This module imports and proves no logical-level 6--10 residual,
`Delta`, support, `Gamma`, or catalogue result.
-/

open scoped BigOperators

namespace Core4loop

noncomputable abbrev TriangleLeafE6PairCurlJ
    (n b c d : ℕ) [NeZero n] :=
  ↥(YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
    WDiffSpace (n := n) (b := b) (c := c) (d := d))

noncomputable def triangleLeafE6PairCurlHdiffEmbed
    {n d : ℕ} [NeZero n] :
    ZeroSumProfileM n (MatrixZeroSum n) →ₗ[F]
      (WVec n d → PairCurlSpace n) where
  toFun S := fun w => S.1 (vecSum w)
  map_add' S T := by
    funext w
    rfl
  map_smul' r S := by
    funext w
    rfl

theorem triangleLeafE6PairCurlHdiffEmbed_injective
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Function.Injective
      (triangleLeafE6PairCurlHdiffEmbed (n := n) (d := d)) := by
  intro S T h
  apply Subtype.ext
  funext sw
  have hw := congrFun h (vecSumRep (n := n) (k := d) hd sw)
  simpa [triangleLeafE6PairCurlHdiffEmbed,
    vecSum_vecSumRep (n := n) (k := d) hd sw] using hw

theorem finrank_triangleLeafE6PairCurlHdiff
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafE6PairCurlHdiffEmbed (n := n) (d := d))) =
      (n - 1) ^ 3 := by
  rw [LinearMap.finrank_range_of_inj
    (triangleLeafE6PairCurlHdiffEmbed_injective (n := n) (d := d) hd)]
  rw [finrank_ZeroSumProfileM, finrank_MatrixZeroSum]
  ring

noncomputable def triangleLeafE6BPairRootInclude
    {n a b c d : ℕ} [NeZero n] :
    TriangleLeafE6PairCurlJ n b c d →ₗ[F]
      BPairAmbient n a b c d where
  toFun j := (⟨j.1, j.2.1⟩, 0)
  map_add' j k := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  map_smul' r j := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

noncomputable def triangleLeafE6BPairRootCurl
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    TriangleLeafE6PairCurlJ n b c d →ₗ[F]
      (WVec n d → PairCurlSpace n) :=
  (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb).comp
    (triangleLeafE6BPairRootInclude
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def triangleLeafE6BDiagInclude
    {n a b c d : ℕ} [NeZero n] :
    BDiagCoeff n a d →ₗ[F] BPairAmbient n a b c d where
  toFun U :=
    (0, ⟨BDiagEmbed (n := n) (a := a) (b := b) (d := d) U, ⟨U, rfl⟩⟩)
  map_add' U V := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact (BDiagEmbed (n := n) (a := a) (b := b) (d := d)).map_add U V
  map_smul' r U := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact (BDiagEmbed (n := n) (a := a) (b := b) (d := d)).map_smul r U

noncomputable def triangleLeafE6BDiagCurl
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    BDiagCoeff n a d →ₗ[F] (WVec n d → PairCurlSpace n) :=
  (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb).comp
    (triangleLeafE6BDiagInclude
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def triangleLeafE6RootTrace
    {n c : ℕ} [NeZero n] :
    YWCoeff n c →ₗ[F] (I n → MatrixZeroSum n) where
  toFun M := fun sz =>
    ∑ z : ZVec n c, if vecSum z = sz then M z else 0
  map_add' M N := by
    funext sz
    change
      (∑ z : ZVec n c, if vecSum z = sz then (M + N) z else 0) =
        (∑ z : ZVec n c, if vecSum z = sz then M z else 0) +
          ∑ z : ZVec n c, if vecSum z = sz then N z else 0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = sz <;> simp [hz]
  map_smul' r M := by
    funext sz
    change
      (∑ z : ZVec n c, if vecSum z = sz then (r • M) z else 0) =
        r • ∑ z : ZVec n c, if vecSum z = sz then M z else 0
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = sz <;> simp [hz]

lemma triangleLeafE6BRootFiberSum_pullYW
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (M : YWCoeff n c)
    (sy sz : I n) (w : WVec n d) :
    BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
        (pullYW (n := n) (b := b) (c := c) (d := d) M) sy sz w =
      ((triangleLeafE6RootTrace (n := n) (c := c) M) sz).1 sy (vecSum w) := by
  unfold BRootFiberSum pullYW triangleLeafE6RootTrace
  change
    (∑ z : ZVec n c,
      if vecSum z = sz then
        (M z).1 (vecSum (vecSumRep (n := n) (k := b) hb sy)) (vecSum w)
      else 0) =
      ((∑ z : ZVec n c, if vecSum z = sz then M z else 0) :
        MatrixZeroSum n).1 sy (vecSum w)
  rw [vecSum_vecSumRep (n := n) (k := b) hb sy]
  change
    (∑ z : ZVec n c, if vecSum z = sz then (M z).1 sy (vecSum w) else 0) =
      ((Submodule.subtype (MatrixZeroSum n))
        (∑ z : ZVec n c, if vecSum z = sz then M z else 0)) sy (vecSum w)
  rw [map_sum]
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases hz : vecSum z = sz <;> simp [hz]

noncomputable def triangleLeafE6RootCurlProfile
    {n : ℕ} [NeZero n]
    (R : I n → MatrixZeroSum n) :
    ZeroSumProfileM n (MatrixZeroSum n) :=
  ⟨fun sw =>
      ⟨fun x t =>
          (R x).1 (t - x) sw +
            (R (x - 1)).1 (t - x + 1) sw,
        by
          constructor
          · apply LinearMap.mem_ker.mpr
            funext x
            change
              (∑ t : I n,
                  ((R x).1 (t - x) sw +
                    (R (x - 1)).1 (t - x + 1) sw)) = 0
            rw [Finset.sum_add_distrib]
            have hfirst :
                (∑ t : I n, (R x).1 (t - x) sw) =
                  ∑ y : I n, (R x).1 y sw := by
              simpa [sub_eq_add_neg] using
                ((Equiv.addRight (-x)).sum_comp
                  (Finset.univ : Finset (I n))
                  (fun y : I n => (R x).1 y sw))
            have hsecond :
                (∑ t : I n, (R (x - 1)).1 (t - x + 1) sw) =
                  ∑ y : I n, (R (x - 1)).1 y sw := by
              let e : I n ≃ I n := Equiv.addRight (-x + 1)
              simpa [sub_eq_add_neg, add_assoc] using
                (e.sum_comp (fun y : I n => (R (x - 1)).1 y sw))
            rw [hfirst, hsecond, matrix_col_zero, matrix_col_zero]
            simp
          · apply LinearMap.mem_ker.mpr
            funext t
            change
              (∑ x : I n,
                  ((R x).1 (t - x) sw +
                    (R (x - 1)).1 (t - x + 1) sw)) = 0
            rw [Finset.sum_add_distrib]
            let f : I n → F := fun x => (R x).1 (t - x) sw
            have hshift :
                (∑ x : I n, (R (x - 1)).1 (t - x + 1) sw) =
                  ∑ x : I n, f x := by
              calc
                (∑ x : I n, (R (x - 1)).1 (t - x + 1) sw)
                    = ∑ x : I n, f (x - 1) := by
                        refine Finset.sum_congr rfl ?_
                        intro x _
                        unfold f
                        rw [show t - x + 1 = t - (x - 1) by abel]
                _ = ∑ x : I n, f x := by
                        simpa [sub_eq_add_neg] using
                          ((Equiv.addRight (-(1 : I n))).sum_comp
                            (Finset.univ : Finset (I n)) f)
            change (∑ x : I n, f x) +
                (∑ x : I n, (R (x - 1)).1 (t - x + 1) sw) = 0
            rw [hshift]
            exact F_add_self _⟩,
    by
      apply LinearMap.mem_ker.mpr
      change
        sigmaMapM (n := n) (MatrixZeroSum n)
          (fun sw =>
            ⟨fun x t =>
                (R x).1 (t - x) sw +
                  (R (x - 1)).1 (t - x + 1) sw,
              _⟩) = 0
      apply Subtype.ext
      funext x t
      change
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ sw : I n,
            (⟨fun x t =>
                (R x).1 (t - x) sw +
                  (R (x - 1)).1 (t - x + 1) sw,
              _⟩ : MatrixZeroSum n))) x t = 0
      rw [map_sum]
      simp only [Finset.sum_apply]
      change
        (∑ sw : I n,
          ((R x).1 (t - x) sw +
            (R (x - 1)).1 (t - x + 1) sw)) = 0
      rw [Finset.sum_add_distrib, matrix_row_zero, matrix_row_zero]
      simp⟩

lemma triangleLeafE6BPairRootCurl_pullYW_pointwise
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (M : YWCoeff n c) (w : WVec n d) (x t : I n) :
    ((triangleLeafE6BPairRootCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb)
      ⟨pullYW (n := n) (b := b) (c := c) (d := d) M,
        range_pullYW_le_inf_YW
          (n := n) (b := b) (c := c) (d := d) ⟨M, rfl⟩⟩ w).1 x t =
      ((triangleLeafE6RootTrace (n := n) (c := c) M) x).1
          (t - x) (vecSum w) +
        ((triangleLeafE6RootTrace (n := n) (c := c) M) (x - 1)).1
          (t - x + 1) (vecSum w) := by
  change
    (BPairCurl
      (n := n) (a := a) (b := b) (c := c) (d := d) hb
      (⟨_, _⟩, 0) w).1 x t = _
  unfold BPairCurl shearDiagVal BPairRawCurl
  simp only [BCompatPSum]
  rw [triangleLeafE6BRootFiberSum_pullYW
    (n := n) (b := b) (c := c) (d := d) hb M (t - x) x w]
  rw [triangleLeafE6BRootFiberSum_pullYW
    (n := n) (b := b) (c := c) (d := d) hb M (t - x + 1) (x - 1) w]
  simp

lemma triangleLeafE6BPairRootCurl_pullYW_eq_hdiff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (M : YWCoeff n c) :
    (triangleLeafE6BPairRootCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb)
      ⟨pullYW (n := n) (b := b) (c := c) (d := d) M,
        range_pullYW_le_inf_YW
          (n := n) (b := b) (c := c) (d := d) ⟨M, rfl⟩⟩ =
      triangleLeafE6PairCurlHdiffEmbed
        (n := n) (d := d)
        (triangleLeafE6RootCurlProfile
          (triangleLeafE6RootTrace (n := n) (c := c) M)) := by
  funext w
  apply Subtype.ext
  funext x t
  exact triangleLeafE6BPairRootCurl_pullYW_pointwise
    (n := n) (a := a) (b := b) (c := c) (d := d) hb M w x t

noncomputable def triangleLeafE6RootCurlTranspose
    {n : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) :
    ZeroSumProfileM n (MatrixZeroSum n) :=
  ⟨fun x =>
      ⟨fun t sw => (S.1 sw).1 x t, by
        constructor
        · apply LinearMap.mem_ker.mpr
          funext t
          change (∑ sw : I n, (S.1 sw).1 x t) = 0
          have hsum :
              (∑ sw : I n, S.1 sw) = 0 :=
            LinearMap.mem_ker.mp S.2
          have hpoint :=
            congrFun (congrFun (congrArg Subtype.val hsum) x) t
          simpa only [Submodule.coe_sum, Finset.sum_apply, Pi.zero_apply] using hpoint
        · apply LinearMap.mem_ker.mpr
          funext sw
          exact matrix_row_zero (S.1 sw) x⟩,
    by
      apply LinearMap.mem_ker.mpr
      change
        sigmaMapM (n := n) (MatrixZeroSum n)
          (fun x =>
            ⟨fun t sw => (S.1 sw).1 x t, _⟩) = 0
      apply Subtype.ext
      funext t sw
      change
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ x : I n,
            (⟨fun t sw => (S.1 sw).1 x t, _⟩ :
              MatrixZeroSum n))) t sw = 0
      rw [map_sum]
      simp only [Finset.sum_apply]
      change (∑ x : I n, (S.1 sw).1 x t) = 0
      exact matrix_col_zero (S.1 sw) t⟩

noncomputable def triangleLeafE6RootCurlSection
    {n : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) :
    I n → MatrixZeroSum n :=
  let P :=
    cycPrimitiveM (n := n) (MatrixZeroSum n)
      (triangleLeafE6RootCurlTranspose S)
  fun x =>
    ⟨fun y sw => (P (x + 1)).1 (y + x) sw, by
      constructor
      · apply LinearMap.mem_ker.mpr
        funext y
        exact matrix_row_zero (P (x + 1)) (y + x)
      · apply LinearMap.mem_ker.mpr
        funext sw
        change (∑ y : I n, (P (x + 1)).1 (y + x) sw) = 0
        have hshift :
            (∑ y : I n, (P (x + 1)).1 (y + x) sw) =
              ∑ y : I n, (P (x + 1)).1 y sw := by
          simpa using
            ((Equiv.addRight x).sum_comp (Finset.univ : Finset (I n))
              (fun y : I n => (P (x + 1)).1 y sw))
        rw [hshift]
        exact matrix_col_zero (P (x + 1)) sw⟩

theorem triangleLeafE6RootCurlProfile_section
    {n : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) :
    triangleLeafE6RootCurlProfile
        (triangleLeafE6RootCurlSection S) = S := by
  let A := triangleLeafE6RootCurlTranspose S
  let P := cycPrimitiveM (n := n) (MatrixZeroSum n) A
  have hprimitive :=
    congrArg Subtype.val
      (cycDiff_cycPrimitiveM (n := n) (MatrixZeroSum n) A)
  change cycDiff (n := n) (MatrixZeroSum n) P = A.1 at hprimitive
  apply Subtype.ext
  funext sw
  apply Subtype.ext
  funext x t
  have hx := congrFun hprimitive x
  have hpoint :=
    congrFun (congrFun (congrArg Subtype.val hx) t) sw
  change
    (triangleLeafE6RootCurlSection S x).1 (t - x) sw +
        (triangleLeafE6RootCurlSection S (x - 1)).1 (t - x + 1) sw =
      (S.1 sw).1 x t
  change
    (P (x + 1)).1 ((t - x) + x) sw +
        (P ((x - 1) + 1)).1 ((t - x + 1) + (x - 1)) sw =
      (S.1 sw).1 x t
  have hcoord₁ : (t - x) + x = t := by abel
  have hcoord₂ : (x - 1) + 1 = x := by abel
  have hcoord₃ : (t - x + 1) + (x - 1) = t := by abel
  rw [hcoord₁, hcoord₂, hcoord₃]
  change
    (P (x + 1)).1 t sw + (P x).1 t sw =
      (S.1 sw).1 x t
  change
    (P x).1 t sw + (P (x + 1)).1 t sw =
      (S.1 sw).1 x t at hpoint
  simpa [add_comm] using hpoint

noncomputable def triangleLeafE6RootTraceSection
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (R : I n → MatrixZeroSum n) :
    YWCoeff n c :=
  fun z =>
    if z = vecSumRep (n := n) (k := c) hc (vecSum z)
    then R (vecSum z)
    else 0

theorem triangleLeafE6RootTrace_section
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (R : I n → MatrixZeroSum n) :
    triangleLeafE6RootTrace (n := n) (c := c)
        (triangleLeafE6RootTraceSection hc R) = R := by
  classical
  funext x
  unfold triangleLeafE6RootTrace triangleLeafE6RootTraceSection
  change
    (∑ z : ZVec n c,
      if vecSum z = x then
        (if z = vecSumRep (n := n) (k := c) hc (vecSum z)
          then R (vecSum z)
          else 0)
      else 0) = R x
  rw [Finset.sum_eq_single (vecSumRep (n := n) (k := c) hc x)]
  · rw [vecSum_vecSumRep (n := n) (k := c) hc x]
    simp
  · intro z _ hz
    by_cases hzx : vecSum z = x
    · have hrep :
          vecSumRep (n := n) (k := c) hc (vecSum z) =
            vecSumRep (n := n) (k := c) hc x := by rw [hzx]
      have hne :
          z ≠ vecSumRep (n := n) (k := c) hc (vecSum z) := by
        intro h
        apply hz
        rw [h, hrep]
      rw [if_pos hzx, if_neg hne]
    · simp [hzx]
  · simp

theorem range_triangleLeafE6BPairRootCurl_eq_hdiff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    LinearMap.range
        (triangleLeafE6BPairRootCurl
          (n := n) (a := a) (b := b) (c := c) (d := d) hb) =
      LinearMap.range
        (triangleLeafE6PairCurlHdiffEmbed (n := n) (d := d)) := by
  apply le_antisymm
  · intro T hT
    rcases hT with ⟨j, rfl⟩
    have hj :
        j.1 ∈ LinearMap.range
          (pullYW (n := n) (b := b) (c := c) (d := d)) := by
      rw [range_pullYW_eq_inf_YW
        (n := n) (b := b) (c := c) (d := d) hb hd]
      exact j.2
    rcases hj with ⟨M, hM⟩
    let jM : TriangleLeafE6PairCurlJ n b c d :=
      ⟨pullYW (n := n) (b := b) (c := c) (d := d) M,
        range_pullYW_le_inf_YW
          (n := n) (b := b) (c := c) (d := d) ⟨M, rfl⟩⟩
    have hjM : jM = j := by
      apply Subtype.ext
      exact hM
    refine
      ⟨triangleLeafE6RootCurlProfile
          (triangleLeafE6RootTrace (n := n) (c := c) M), ?_⟩
    rw [← hjM]
    exact
      (triangleLeafE6BPairRootCurl_pullYW_eq_hdiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb M).symm
  · intro T hT
    rcases hT with ⟨S, rfl⟩
    let R : I n → MatrixZeroSum n :=
      triangleLeafE6RootCurlSection S
    let M : YWCoeff n c :=
      triangleLeafE6RootTraceSection hc R
    let jM : TriangleLeafE6PairCurlJ n b c d :=
      ⟨pullYW (n := n) (b := b) (c := c) (d := d) M,
        range_pullYW_le_inf_YW
          (n := n) (b := b) (c := c) (d := d) ⟨M, rfl⟩⟩
    refine ⟨jM, ?_⟩
    rw [triangleLeafE6BPairRootCurl_pullYW_eq_hdiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb M]
    have htrace :
        triangleLeafE6RootTrace (n := n) (c := c) M = R :=
      triangleLeafE6RootTrace_section
        (n := n) (c := c) hc R
    rw [htrace]
    rw [triangleLeafE6RootCurlProfile_section]

lemma triangleLeafE6BCompatPSum_BDiagEmbed
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (U : BDiagCoeff n a d)
    (w : WVec n d) (sy sz : I n) :
    BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
        (BDiagEmbed (n := n) (a := a) (b := b) (d := d) U) sy sz w =
      ∑ p : PVec n a, (U p w).1 sy (sy + sz) := by
  unfold BCompatPSum BDiagEmbed
  change
    (∑ p : PVec n a,
      (U p w).1
        (vecSum (vecSumRep (n := n) (k := b) hb sy))
        (vecSum (vecSumRep (n := n) (k := b) hb sy) + sz)) =
      ∑ p : PVec n a, (U p w).1 sy (sy + sz)
  rw [vecSum_vecSumRep (n := n) (k := b) hb sy]

lemma triangleLeafE6BDiagCurl_pointwise
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (U : BDiagCoeff n a d)
    (w : WVec n d) (x t : I n) :
    ((triangleLeafE6BDiagCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb U w).1 x t) =
      ∑ p : PVec n a,
        ((U p w).1 (t - x) t +
          (U p w).1 (t - x + 1) (t + 1)) := by
  change
    (BPairCurl
      (n := n) (a := a) (b := b) (c := c) (d := d) hb
      (0,
        ⟨BDiagEmbed (n := n) (a := a) (b := b) (d := d) U,
          ⟨U, rfl⟩⟩) w).1 x t = _
  unfold BPairCurl shearDiagVal BPairRawCurl
  change
    BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
          (0 : RootTarget n b c d) (t - x) x w +
        BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
          (0 : RootTarget n b c d) (t - x + 1) (x - 1) w +
        BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
          (BDiagEmbed (n := n) (a := a) (b := b) (d := d) U)
          (t - x) x w +
        BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
          (BDiagEmbed (n := n) (a := a) (b := b) (d := d) U)
          (t - x + 1) x w =
      ∑ p : PVec n a,
        ((U p w).1 (t - x) t +
          (U p w).1 (t - x + 1) (t + 1))
  rw [triangleLeafE6BCompatPSum_BDiagEmbed
    (n := n) (a := a) (b := b) (d := d) hb U w (t - x) x]
  rw [triangleLeafE6BCompatPSum_BDiagEmbed
    (n := n) (a := a) (b := b) (d := d) hb U w (t - x + 1) x]
  simp only [BRootFiberSum]
  simp only [Pi.zero_apply, ite_self, Finset.sum_const_zero, add_zero,
    sub_add_cancel, zero_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p _
  have hcoord₂ : t - x + 1 + x = t + 1 := by abel
  rw [hcoord₂]

noncomputable def triangleLeafE6DiagRow
    {n d : ℕ} [NeZero n]
    (N : WVec n d → PairCurlSpace n)
    (w : WVec n d) (x : I n) :
    ZeroSumProfile n :=
  ⟨fun t => (N w).1 x t, by
    apply LinearMap.mem_ker.mpr
    exact matrix_row_zero (N w) x⟩

noncomputable def triangleLeafE6DiagPrimitive
    {n d : ℕ} [NeZero n]
    (N : WVec n d → PairCurlSpace n)
    (w : WVec n d) (x : I n) :
    I n → F :=
  cycPrimitiveM (n := n) F (triangleLeafE6DiagRow N w x)

lemma triangleLeafE6DiagPrimitive_step
    {n d : ℕ} [NeZero n]
    (N : WVec n d → PairCurlSpace n)
    (w : WVec n d) (x t : I n) :
    triangleLeafE6DiagPrimitive N w x t +
        triangleLeafE6DiagPrimitive N w x (t + 1) =
      (N w).1 x t := by
  have h :=
    congrArg Subtype.val
      (cycDiff_cycPrimitiveM (n := n) F
        (triangleLeafE6DiagRow N w x))
  change
    cycDiff (n := n) F (triangleLeafE6DiagPrimitive N w x) =
      (triangleLeafE6DiagRow N w x).1 at h
  exact congrFun h t

noncomputable def triangleLeafE6DiagLine
    {n d : ℕ} [NeZero n]
    (N : WVec n d → PairCurlSpace n)
    (w : WVec n d) :
    LineZeroSum n :=
  ⟨fun y t => triangleLeafE6DiagPrimitive N w (t - y) t, by
    apply LinearMap.mem_ker.mpr
    change
      (∑ y : I n,
        (fun t : I n => triangleLeafE6DiagPrimitive N w (t - y) t)) = 0
    funext t
    simp only [Finset.sum_apply, Pi.zero_apply]
    have hshift :
        (∑ y : I n, triangleLeafE6DiagPrimitive N w (t - y) t) =
          ∑ x : I n, triangleLeafE6DiagPrimitive N w x t := by
      simpa using
        ((zmodSubLeftEquiv (n := n) t).sum_comp
          (fun x : I n => triangleLeafE6DiagPrimitive N w x t))
    rw [hshift]
    have hrows :
        (∑ x : I n, triangleLeafE6DiagRow N w x) = 0 := by
      apply Subtype.ext
      funext u
      change
        ((Submodule.subtype (ZeroSumProfile n))
          (∑ x : I n, triangleLeafE6DiagRow N w x)) u = 0
      rw [map_sum]
      simp only [Finset.sum_apply]
      change (∑ x : I n, (N w).1 x u) = 0
      exact matrix_col_zero (N w) u
    have hsum :
        (∑ x : I n, triangleLeafE6DiagPrimitive N w x) = 0 := by
      change
        (∑ x : I n,
          cycPrimitiveM (n := n) F
            (triangleLeafE6DiagRow N w x)) = 0
      rw [← map_sum]
      calc
        cycPrimitiveM (n := n) F
            (∑ x : I n, triangleLeafE6DiagRow N w x) =
            cycPrimitiveM (n := n) F (0 : ZeroSumProfile n) :=
          congrArg (fun q : ZeroSumProfile n =>
            cycPrimitiveM (n := n) F q) hrows
        _ = 0 := (cycPrimitiveM (n := n) F).map_zero
    have ht := congrFun hsum t
    simpa only [Finset.sum_apply, Pi.zero_apply] using ht⟩

noncomputable def triangleLeafE6BDiagSection
    {n a d : ℕ} [NeZero n]
    (N : WVec n d → PairCurlSpace n) :
    BDiagCoeff n a d :=
  fun p w =>
    if p = (zeroVec : PVec n a)
    then triangleLeafE6DiagLine N w
    else 0

lemma triangleLeafE6BDiagSection_sum
    {n a d : ℕ} [NeZero n]
    (N : WVec n d → PairCurlSpace n)
    (w : WVec n d) (y t : I n) :
    (∑ p : PVec n a,
      (triangleLeafE6BDiagSection N p w).1 y t) =
      (triangleLeafE6DiagLine N w).1 y t := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · simp [triangleLeafE6BDiagSection]
  · intro p _ hp
    simp [triangleLeafE6BDiagSection, hp]
  · simp

theorem triangleLeafE6BDiagCurl_section
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b)
    (N : WVec n d → PairCurlSpace n) :
    triangleLeafE6BDiagCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb
        (triangleLeafE6BDiagSection N) = N := by
  funext w
  apply Subtype.ext
  funext x t
  rw [triangleLeafE6BDiagCurl_pointwise
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb (triangleLeafE6BDiagSection N) w x t]
  rw [Finset.sum_add_distrib]
  rw [triangleLeafE6BDiagSection_sum
    (n := n) (a := a) (d := d) N w (t - x) t]
  rw [triangleLeafE6BDiagSection_sum
    (n := n) (a := a) (d := d) N w (t - x + 1) (t + 1)]
  change
    triangleLeafE6DiagPrimitive N w (t - (t - x)) t +
        triangleLeafE6DiagPrimitive N w
          ((t + 1) - (t - x + 1)) (t + 1) =
      (N w).1 x t
  have hcoord₁ : t - (t - x) = x := by abel
  have hcoord₂ : (t + 1) - (t - x + 1) = x := by abel
  rw [hcoord₁, hcoord₂]
  exact triangleLeafE6DiagPrimitive_step N w x t

theorem triangleLeafE6BDiagCurl_surjective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) :
    Function.Surjective
      (triangleLeafE6BDiagCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  intro N
  exact
    ⟨triangleLeafE6BDiagSection N,
      triangleLeafE6BDiagCurl_section
        (n := n) (a := a) (b := b) (c := c) (d := d) hb N⟩

end Core4loop
