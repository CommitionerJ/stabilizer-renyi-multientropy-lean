import Core4loop.Square.Rank.PairMapsCore
import Core4loop.Square.Rank.Diagonal
import Core4loop.BDiag

open scoped BigOperators

namespace Core4loop

lemma zmod_eq_sub_add_one_iff {n : ℕ} [NeZero n] (x sy sz : I n) :
    x = sy + sz - (sy + 1) ↔ x + 1 = sz := by
  constructor
  · intro h
    rw [h]
    abel
  · intro h
    rw [← h]
    abel

lemma lineZeroSum_col_mem_ZeroSumProfile {n : ℕ} [NeZero n]
    (L : LineZeroSum n) (t : I n) :
    (fun sy : I n => L.1 sy t) ∈ ZeroSumProfile n := by
  apply LinearMap.mem_ker.mpr
  have hsum : sigmaMapM (n := n) (Profile n) L.1 = 0 :=
    LinearMap.mem_ker.mp L.2
  change (∑ sy : I n, L.1 sy t) = 0
  change (∑ sy : I n, L.1 sy) = 0 at hsum
  simpa only [Finset.sum_apply, Pi.zero_apply] using congrFun hsum t

theorem BDiagEmbed_BDiagOfB_eq_squareCompat_B
    {n a b c d : ℕ} [NeZero n] (B : BFun4 n a c d) :
    BDiagEmbed (n := n) (a := a) (b := b) (d := d)
        (BDiagOfB (n := n) (a := a) (c := c) (d := d) B) =
      ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) B := by
  classical
  funext p y sz w
  change
    (BDiagOfB (n := n) (a := a) (c := c) (d := d) B p w).1
        (vecSum y) (vecSum y + sz) =
      squareCompatFun B 0 p y sz w
  unfold BDiagOfB squareCompatFun betaB gammaB xiW zetaW
  simp only [cycDiff_apply, Pi.zero_apply, add_zero]
  change
    ((∑ z : ZVec n c,
        if vecSum z = vecSum y + sz - vecSum y then B p (vecSum y) z w else 0)
      + ∑ z : ZVec n c,
        if vecSum z = vecSum y + sz - (vecSum y + 1) then
          B p (vecSum y + 1) z w
        else 0)
      =
      (∑ z : ZVec n c, if vecSum z = sz then B p (vecSum y) z w else 0)
        + ∑ z : ZVec n c,
          if vecSum z + 1 = sz then B p (vecSum y + 1) z w else 0
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro z _
    have hcoord : vecSum y + sz - vecSum y = sz := by abel
    rw [hcoord]
  · refine Finset.sum_congr rfl ?_
    intro z _
    have hiff :
        vecSum z = vecSum y + sz - (vecSum y + 1) ↔ vecSum z + 1 = sz :=
      zmod_eq_sub_add_one_iff (vecSum z) (vecSum y) sz
    exact if_congr hiff rfl rfl

theorem range_squareCompat_B_le_BDiagSpace
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
      BDiagSpace (n := n) (a := a) (b := b) (d := d) := by
  intro C hC
  rcases hC with ⟨B, rfl⟩
  refine ⟨BDiagOfB (n := n) (a := a) (c := c) (d := d) B, ?_⟩
  exact (BDiagEmbed_BDiagOfB_eq_squareCompat_B
    (n := n) (a := a) (b := b) (c := c) (d := d) B)

theorem BDiagSpace_le_range_squareCompat_B
    {n a b c d : ℕ} [NeZero n] (hc : 0 < c) :
    BDiagSpace (n := n) (a := a) (b := b) (d := d) ≤
      LinearMap.range
        ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  classical
  intro C hC
  rcases hC with ⟨U, rfl⟩
  choose H hH using fun (p : PVec n a) (w : WVec n d) (t : I n) =>
    show ∃ h : Profile n,
        cycDiff (n := n) F h = fun sy : I n => (U p w).1 sy t by
      have hm :
          (fun sy : I n => (U p w).1 sy t) ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact lineZeroSum_col_mem_ZeroSumProfile (U p w) t
      exact hm
  choose zOf hzOf using vecSum_surjective (n := n) (k := c) hc
  let B : BFun4 n a c d := fun p sy z w =>
    if z = zOf (vecSum z) then H p w (sy + vecSum z) sy else 0
  have hfiber :
      ∀ (p : PVec n a) (w : WVec n d) (sy t : I n),
        (∑ z : ZVec n c, if vecSum z = t - sy then B p sy z w else 0) =
          H p w t sy := by
    intro p w sy t
    rw [Finset.sum_eq_single (zOf (t - sy))]
    · have hcoord : sy + (t - sy) = t := by abel
      simp [B, hzOf, hcoord]
    · intro z _ hz_ne
      by_cases hv : vecSum z = t - sy
      · simp [B, hv, hz_ne]
      · simp [hv]
    · simp
  refine ⟨B, ?_⟩
  rw [← BDiagEmbed_BDiagOfB_eq_squareCompat_B
    (n := n) (a := a) (b := b) (c := c) (d := d) B]
  congr 1
  funext p w
  apply Subtype.ext
  funext sy t
  unfold BDiagOfB
  simp only [cycDiff_apply]
  change
    (∑ z : ZVec n c, if vecSum z = t - sy then B p sy z w else 0)
        + (∑ z : ZVec n c, if vecSum z = t - (sy + 1) then B p (sy + 1) z w else 0) =
      (U p w).1 sy t
  rw [hfiber p w sy t, hfiber p w (sy + 1) t]
  exact congrFun (hH p w t) sy

theorem range_squareCompat_B_eq_BDiagSpace
    {n a b c d : ℕ} [NeZero n] (_hb : 0 < b) (hc : 0 < c) :
    LinearMap.range
        ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) =
      BDiagSpace (n := n) (a := a) (b := b) (d := d) := by
  apply le_antisymm
  · exact range_squareCompat_B_le_BDiagSpace
  · exact BDiagSpace_le_range_squareCompat_B
      (n := n) (a := a) (b := b) (c := c) (d := d) hc

noncomputable def WDiagOfW {n a b c : ℕ} [NeZero n]
    (W : WFun4 n a b c) : WDiagCoeff n a b :=
  fun p y =>
    ⟨cycDiff (n := n) (Profile n)
      (fun sw : I n => fun t : I n =>
        ∑ z : ZVec n c, if vecSum z = t - sw then W p y z sw else 0),
      cycDiff_mem_ZeroSumProfileM
        (fun sw : I n => fun t : I n =>
          ∑ z : ZVec n c, if vecSum z = t - sw then W p y z sw else 0)⟩

noncomputable def WDiagOfWLinear {n a b c : ℕ} [NeZero n] :
    WFun4 n a b c →ₗ[F] WDiagCoeff n a b where
  toFun W := WDiagOfW (n := n) (a := a) (b := b) (c := c) W
  map_add' W W' := by
    funext p y
    apply Subtype.ext
    change
      cycDiff (n := n) (Profile n)
          (fun sw : I n => fun t : I n =>
            ∑ z : ZVec n c, if vecSum z = t - sw then (W + W') p y z sw else 0) =
        cycDiff (n := n) (Profile n)
            (fun sw : I n => fun t : I n =>
              ∑ z : ZVec n c, if vecSum z = t - sw then W p y z sw else 0) +
          cycDiff (n := n) (Profile n)
            (fun sw : I n => fun t : I n =>
              ∑ z : ZVec n c, if vecSum z = t - sw then W' p y z sw else 0)
    rw [← (cycDiff (n := n) (Profile n)).map_add]
    congr
    funext sw t
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = t - sw <;> simp [hz]
  map_smul' r W := by
    funext p y
    apply Subtype.ext
    change
      cycDiff (n := n) (Profile n)
          (fun sw : I n => fun t : I n =>
            ∑ z : ZVec n c, if vecSum z = t - sw then (r • W) p y z sw else 0) =
        r • cycDiff (n := n) (Profile n)
          (fun sw : I n => fun t : I n =>
            ∑ z : ZVec n c, if vecSum z = t - sw then W p y z sw else 0)
    rw [← (cycDiff (n := n) (Profile n)).map_smul]
    congr
    funext sw t
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = t - sw <;> simp [hz, mul_zero]

@[simp]
theorem WDiagOfWLinear_apply {n a b c : ℕ} [NeZero n]
    (W : WFun4 n a b c) :
    WDiagOfWLinear (n := n) (a := a) (b := b) (c := c) W =
      WDiagOfW (n := n) (a := a) (b := b) (c := c) W :=
  rfl

theorem WDiagEmbed_WDiagOfW_eq_squareCompat_W
    {n a b c d : ℕ} [NeZero n] (W : WFun4 n a b c) :
    WDiagEmbed (n := n) (a := a) (b := b) (d := d)
        (WDiagOfW (n := n) (a := a) (b := b) (c := c) W) =
      ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) W := by
  classical
  funext p y sz w
  change
    (WDiagOfW (n := n) (a := a) (b := b) (c := c) W p y).1
        (vecSum w) (vecSum w + sz) =
      squareCompatFun 0 W p y sz w
  unfold WDiagOfW squareCompatFun betaB gammaB xiW zetaW
  simp only [cycDiff_apply, Pi.zero_apply, zero_add]
  change
    ((∑ z : ZVec n c,
        if vecSum z = vecSum w + sz - vecSum w then W p y z (vecSum w) else 0)
      + ∑ z : ZVec n c,
        if vecSum z = vecSum w + sz - (vecSum w + 1) then
          W p y z (vecSum w + 1)
        else 0)
      =
      (∑ z : ZVec n c, if vecSum z = sz then W p y z (vecSum w) else 0)
        + ∑ z : ZVec n c,
          if vecSum z + 1 = sz then W p y z (vecSum w + 1) else 0
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro z _
    have hcoord : vecSum w + sz - vecSum w = sz := by abel
    rw [hcoord]
  · refine Finset.sum_congr rfl ?_
    intro z _
    have hiff :
        vecSum z = vecSum w + sz - (vecSum w + 1) ↔ vecSum z + 1 = sz :=
      zmod_eq_sub_add_one_iff (vecSum z) (vecSum w) sz
    exact if_congr hiff rfl rfl

theorem range_squareCompat_W_le_WDiagSpace
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
      WDiagSpace (n := n) (a := a) (b := b) (d := d) := by
  intro C hC
  rcases hC with ⟨W, rfl⟩
  refine ⟨WDiagOfW (n := n) (a := a) (b := b) (c := c) W, ?_⟩
  exact (WDiagEmbed_WDiagOfW_eq_squareCompat_W
    (n := n) (a := a) (b := b) (c := c) (d := d) W)

theorem WDiagSpace_le_range_squareCompat_W
    {n a b c d : ℕ} [NeZero n] (hc : 0 < c) :
    WDiagSpace (n := n) (a := a) (b := b) (d := d) ≤
      LinearMap.range
        ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  classical
  intro C hC
  rcases hC with ⟨U, rfl⟩
  choose H hH using fun (p : PVec n a) (y : YVec n b) (t : I n) =>
    show ∃ h : Profile n,
        cycDiff (n := n) F h = fun sw : I n => (U p y).1 sw t by
      have hm :
          (fun sw : I n => (U p y).1 sw t) ∈
            LinearMap.range (cycDiff (n := n) F) := by
        rw [range_cycDiff_eq_ZeroSumProfile]
        exact lineZeroSum_col_mem_ZeroSumProfile (U p y) t
      exact hm
  choose zOf hzOf using vecSum_surjective (n := n) (k := c) hc
  let W : WFun4 n a b c := fun p y z sw =>
    if z = zOf (vecSum z) then H p y (sw + vecSum z) sw else 0
  have hfiber :
      ∀ (p : PVec n a) (y : YVec n b) (sw t : I n),
        (∑ z : ZVec n c, if vecSum z = t - sw then W p y z sw else 0) =
          H p y t sw := by
    intro p y sw t
    rw [Finset.sum_eq_single (zOf (t - sw))]
    · have hcoord : sw + (t - sw) = t := by abel
      simp [W, hzOf, hcoord]
    · intro z _ hz_ne
      by_cases hv : vecSum z = t - sw
      · simp [W, hv, hz_ne]
      · simp [hv]
    · simp
  refine ⟨W, ?_⟩
  rw [← WDiagEmbed_WDiagOfW_eq_squareCompat_W
    (n := n) (a := a) (b := b) (c := c) (d := d) W]
  congr 1
  funext p y
  apply Subtype.ext
  funext sw t
  unfold WDiagOfW
  simp only [cycDiff_apply]
  change
    (∑ z : ZVec n c, if vecSum z = t - sw then W p y z sw else 0)
        + (∑ z : ZVec n c, if vecSum z = t - (sw + 1) then W p y z (sw + 1) else 0) =
      (U p y).1 sw t
  rw [hfiber p y sw t, hfiber p y (sw + 1) t]
  exact congrFun (hH p y t) sw

theorem range_squareCompat_W_eq_WDiagSpace
    {n a b c d : ℕ} [NeZero n] (hc : 0 < c) (_hd : 0 < d) :
    LinearMap.range
        ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) =
      WDiagSpace (n := n) (a := a) (b := b) (d := d) := by
  apply le_antisymm
  · exact range_squareCompat_W_le_WDiagSpace
  · exact WDiagSpace_le_range_squareCompat_W
      (n := n) (a := a) (b := b) (c := c) (d := d) hc

end Core4loop
