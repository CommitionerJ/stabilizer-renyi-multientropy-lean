import Core4loop.Square.Rank.IntersectionRoot

open scoped BigOperators

namespace Core4loop

abbrev SquareCompatCoeff (n a : ℕ) [NeZero n] :=
  PVec n a → SquareCompatCore n

noncomputable def SquareCompatEmbed {n a b d : ℕ} [NeZero n] :
    SquareCompatCoeff n a →ₗ[F] CFun4 n a b d where
  toFun T := fun p y sz w =>
    compatCoreEval (T p) (vecSum y) sz (vecSum w)
  map_add' T U := by
    funext p y sz w
    rfl
  map_smul' r T := by
    funext p y sz w
    rfl

lemma SquareCompatEmbed_apply_eq
    {n a b d : ℕ} [NeZero n]
    (T : SquareCompatCoeff n a)
    (p : PVec n a) (y : YVec n b) (sz : I n) (w : WVec n d) :
    SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) T p y sz w =
      (T p (vecSum y + sz + vecSum w)).1 (vecSum y) (vecSum w) := rfl

theorem range_SquareCompatEmbed_le_BDiagSpace
    {n a b d : ℕ} [NeZero n] :
    LinearMap.range (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)) ≤
      BDiagSpace (n := n) (a := a) (b := b) (d := d) := by
  intro C hC
  rcases hC with ⟨T, rfl⟩
  refine ⟨fun p w =>
    ⟨fun sy r => (T p (r + vecSum w)).1 sy (vecSum w), ?_⟩, ?_⟩
  · apply LinearMap.mem_ker.mpr
    change (∑ sy : I n, fun r : I n => (T p (r + vecSum w)).1 sy (vecSum w)) = 0
    funext r
    simp only [Finset.sum_apply, Pi.zero_apply]
    exact matrix_col_zero (T p (r + vecSum w)) (vecSum w)
  · funext p y sz w
    simp [SquareCompatEmbed, BDiagEmbed, compatCoreEval, add_assoc]

theorem range_SquareCompatEmbed_le_WDiagSpace
    {n a b d : ℕ} [NeZero n] :
    LinearMap.range (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)) ≤
      WDiagSpace (n := n) (a := a) (b := b) (d := d) := by
  intro C hC
  rcases hC with ⟨T, rfl⟩
  refine ⟨fun p y =>
    ⟨fun sw r => (T p (vecSum y + r)).1 (vecSum y) sw, ?_⟩, ?_⟩
  · apply LinearMap.mem_ker.mpr
    change (∑ sw : I n, fun r : I n => (T p (vecSum y + r)).1 (vecSum y) sw) = 0
    funext r
    simp only [Finset.sum_apply, Pi.zero_apply]
    exact matrix_row_zero (T p (vecSum y + r)) (vecSum y)
  · funext p y sz w
    have hcoord : vecSum y + (vecSum w + sz) = vecSum y + sz + vecSum w := by
      abel
    simp [SquareCompatEmbed, WDiagEmbed, compatCoreEval, hcoord]

theorem SquareCompatEmbed_injective
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    Function.Injective
      (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)) := by
  intro T U h
  funext p t
  apply Subtype.ext
  funext sy sw
  let y := vecSumRep (n := n) (k := b) hb sy
  let w := vecSumRep (n := n) (k := d) hd sw
  let sz : I n := t - sy - sw
  have hy : vecSum y = sy := vecSum_vecSumRep (n := n) (k := b) hb sy
  have hw : vecSum w = sw := vecSum_vecSumRep (n := n) (k := d) hd sw
  have hcoord : vecSum y + sz + vecSum w = t := by
    change vecSum y + (t - sy - sw) + vecSum w = t
    rw [hy, hw]
    abel
  have hcoord' : sy + sz + sw = t := by
    simpa [hy, hw] using hcoord
  have hv := congrFun (congrFun (congrFun (congrFun h p) y) sz) w
  rw [SquareCompatEmbed_apply_eq, SquareCompatEmbed_apply_eq] at hv
  simpa [hy, hw, hcoord'] using hv

lemma BDiag_mem_eq_of_same_sy_same_t
    {n a b d : ℕ} [NeZero n]
    {C : CFun4 n a b d}
    (hC : C ∈ BDiagSpace (n := n) (a := a) (b := b) (d := d))
    {p : PVec n a} {y y' : YVec n b} {sz sz' : I n} {w : WVec n d}
    (hsy : vecSum y = vecSum y')
    (ht : vecSum y + sz = vecSum y' + sz') :
    C p y sz w = C p y' sz' w := by
  rcases hC with ⟨U, rfl⟩
  change (U p w).1 (vecSum y) (vecSum y + sz) =
    (U p w).1 (vecSum y') (vecSum y' + sz')
  rw [hsy]
  exact congrArg (fun t => (U p w).1 (vecSum y') t) (by simpa [hsy] using ht)

lemma WDiag_mem_eq_of_same_sw_same_t
    {n a b d : ℕ} [NeZero n]
    {C : CFun4 n a b d}
    (hC : C ∈ WDiagSpace (n := n) (a := a) (b := b) (d := d))
    {p : PVec n a} {y : YVec n b} {sz sz' : I n} {w w' : WVec n d}
    (hsw : vecSum w = vecSum w')
    (ht : vecSum w + sz = vecSum w' + sz') :
    C p y sz w = C p y sz' w' := by
  rcases hC with ⟨V, rfl⟩
  change (V p y).1 (vecSum w) (vecSum w + sz) =
    (V p y).1 (vecSum w') (vecSum w' + sz')
  rw [hsw]
  exact congrArg (fun t => (V p y).1 (vecSum w') t) (by simpa [hsw] using ht)

theorem range_SquareCompatEmbed_eq_inf_BDiag_WDiag
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    LinearMap.range (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)) =
      BDiagSpace (n := n) (a := a) (b := b) (d := d) ⊓
        WDiagSpace (n := n) (a := a) (b := b) (d := d) := by
  classical
  apply le_antisymm
  · intro C hC
    exact ⟨range_SquareCompatEmbed_le_BDiagSpace (n := n) (a := a) (b := b) (d := d) hC,
      range_SquareCompatEmbed_le_WDiagSpace (n := n) (a := a) (b := b) (d := d) hC⟩
  · intro C hC
    rcases hC with ⟨hB, hW⟩
    have hBmem := hB
    have hWmem := hW
    rcases hB with ⟨U, hU⟩
    rcases hW with ⟨V, hV⟩
    let yOf : I n → YVec n b := fun sy => vecSumRep (n := n) (k := b) hb sy
    let wOf : I n → WVec n d := fun sw => vecSumRep (n := n) (k := d) hd sw
    have hyOf : ∀ sy : I n, vecSum (yOf sy) = sy := by
      intro sy
      exact vecSum_vecSumRep (n := n) (k := b) hb sy
    have hwOf : ∀ sw : I n, vecSum (wOf sw) = sw := by
      intro sw
      exact vecSum_vecSumRep (n := n) (k := d) hd sw
    let T : SquareCompatCoeff n a := fun p t =>
      ⟨fun sy sw => C p (yOf sy) (t - sy - sw) (wOf sw), by
        constructor
        · apply LinearMap.mem_ker.mpr
          funext sy
          change (∑ sw : I n, C p (yOf sy) (t - sy - sw) (wOf sw)) = 0
          calc
            (∑ sw : I n, C p (yOf sy) (t - sy - sw) (wOf sw))
                = ∑ sw : I n, (V p (yOf sy)).1 sw (t - sy) := by
                    refine Finset.sum_congr rfl ?_
                    intro sw _
                    have hv :=
                      congrFun (congrFun (congrFun (congrFun hV p) (yOf sy))
                        (t - sy - sw)) (wOf sw)
                    have hcoord : vecSum (wOf sw) + (t - sy - sw) = t - sy := by
                      rw [hwOf sw]
                      abel
                    have hcoord' : sw + (t - sy - sw) = t - sy := by
                      abel
                    simpa [WDiagEmbed, hwOf sw, hcoord'] using hv.symm
            _ = 0 := lineZeroSum_coord_zero (n := n) (V p (yOf sy)) (t - sy)
        · apply LinearMap.mem_ker.mpr
          funext sw
          change (∑ sy : I n, C p (yOf sy) (t - sy - sw) (wOf sw)) = 0
          calc
            (∑ sy : I n, C p (yOf sy) (t - sy - sw) (wOf sw))
                = ∑ sy : I n, (U p (wOf sw)).1 sy (t - sw) := by
                    refine Finset.sum_congr rfl ?_
                    intro sy _
                    have hu :=
                      congrFun (congrFun (congrFun (congrFun hU p) (yOf sy))
                        (t - sy - sw)) (wOf sw)
                    have hcoord : vecSum (yOf sy) + (t - sy - sw) = t - sw := by
                      rw [hyOf sy]
                      abel
                    have hcoord' : sy + (t - sy - sw) = t - sw := by
                      abel
                    simpa [BDiagEmbed, hyOf sy, hcoord'] using hu.symm
            _ = 0 := lineZeroSum_coord_zero (n := n) (U p (wOf sw)) (t - sw)⟩
    refine ⟨T, ?_⟩
    funext p y sz w
    rw [SquareCompatEmbed_apply_eq]
    let sy : I n := vecSum y
    let sw : I n := vecSum w
    let t : I n := sy + sz + sw
    change C p (yOf sy) (t - sy - sw) (wOf sw) = C p y sz w
    have hy : vecSum (yOf sy) = vecSum y := by
      simpa [sy] using hyOf sy
    have hstepY : C p y sz w = C p (yOf sy) sz w := by
      apply BDiag_mem_eq_of_same_sy_same_t
        (n := n) (a := a) (b := b) (d := d) hBmem
      · exact hy.symm
      · simp [hy]
    have hw : vecSum (wOf sw) = vecSum w := by
      simpa [sw] using hwOf sw
    have hstepW : C p (yOf sy) sz w = C p (yOf sy) (t - sy - sw) (wOf sw) := by
      apply WDiag_mem_eq_of_same_sw_same_t
        (n := n) (a := a) (b := b) (d := d) hWmem
      · exact hw.symm
      · rw [hw]
        change sw + sz = sw + (t - sy - sw)
        simp [t]
        abel
    exact (hstepY.trans hstepW).symm

theorem finrank_SquareCompatCoeff
    {n a : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F (SquareCompatCoeff n a) =
      (n - 1) ^ 2 * n ^ a := by
  calc
    Module.finrank F (SquareCompatCoeff n a)
        = ∑ _ : PVec n a, Module.finrank F (SquareCompatCore n) := by
            simp [SquareCompatCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : PVec n a => SquareCompatCore n)]
    _ = Fintype.card (PVec n a) * (n * (n - 1) ^ 2) := by
            simp [finrank_SquareCompatCore]
    _ = n ^ (a - 1) * (n * (n - 1) ^ 2) := by
            rw [card_vec]
    _ = (n - 1) ^ 2 * n ^ a := by
            calc
              n ^ (a - 1) * (n * (n - 1) ^ 2)
                  = (n - 1) ^ 2 * (n ^ (a - 1) * n) := by ring
              _ = (n - 1) ^ 2 * n ^ ((a - 1) + 1) := by
                    rw [pow_succ]
                    ring
              _ = (n - 1) ^ 2 * n ^ a := by
                    congr 1
                    congr 1
                    omega

noncomputable def SquareCompatTrace {n a : ℕ} [NeZero n] :
    SquareCompatCoeff n a →ₗ[F] SquareCompatCore n where
  toFun T := fun t => ∑ p : PVec n a, T p t
  map_add' T U := by
    funext t
    apply Subtype.ext
    funext sy sw
    change
      ((Submodule.subtype (MatrixZeroSum n))
        (∑ p : PVec n a, (T + U) p t)) sy sw =
        ((Submodule.subtype (MatrixZeroSum n))
          ((∑ p : PVec n a, T p t) + ∑ p : PVec n a, U p t)) sy sw
    rw [map_add]
    simp only [Pi.add_apply]
    have hL :
        ((Submodule.subtype (MatrixZeroSum n))
          (Finset.sum Finset.univ
            (fun p : PVec n a => (T p t) + (U p t)))) sy sw =
          Finset.sum Finset.univ
            (fun p : PVec n a => (T p t).1 sy sw + (U p t).1 sy sw) := by
      rw [map_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro p _
      simp
    have hT :
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ p : PVec n a, T p t)) sy sw =
          ∑ p : PVec n a, (T p t).1 sy sw := by
      rw [map_sum]
      simp only [Finset.sum_apply]
      rfl
    have hU :
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ p : PVec n a, U p t)) sy sw =
          ∑ p : PVec n a, (U p t).1 sy sw := by
      rw [map_sum]
      simp only [Finset.sum_apply]
      rfl
    rw [hL, hT, hU]
    rw [Finset.sum_add_distrib]
  map_smul' r T := by
    funext t
    apply Subtype.ext
    funext sy sw
    change
      ((Submodule.subtype (MatrixZeroSum n))
        (∑ p : PVec n a, (r • T) p t)) sy sw =
        ((Submodule.subtype (MatrixZeroSum n))
          (r • ∑ p : PVec n a, T p t)) sy sw
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hL :
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ p : PVec n a, r • (T p t))) sy sw =
          ∑ p : PVec n a, r * (T p t).1 sy sw := by
      rw [map_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro p _
      simp [smul_eq_mul]
    have hT :
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ p : PVec n a, T p t)) sy sw =
          ∑ p : PVec n a, (T p t).1 sy sw := by
      rw [map_sum]
      simp only [Finset.sum_apply]
      rfl
    rw [hL, hT]
    rw [Finset.mul_sum]

noncomputable def SquareCompatTraceSection {n a : ℕ} [NeZero n]
    (S : SquareCompatCore n) : SquareCompatCoeff n a :=
  fun p => if p = 0 then S else 0

lemma SquareCompatTrace_section_apply
    {n a : ℕ} [NeZero n]
    (S : SquareCompatCore n) (t : I n) :
    SquareCompatTrace (n := n) (a := a)
        (SquareCompatTraceSection (n := n) (a := a) S) t = S t := by
  classical
  change (∑ p : PVec n a,
      (SquareCompatTraceSection (n := n) (a := a) S p) t) = S t
  unfold SquareCompatTraceSection
  rw [Finset.sum_eq_single (0 : PVec n a)]
  · simp
  · intro p _ hp
    simp [hp]
  · intro hnot
    simp at hnot

theorem SquareCompatTrace_surjective
    {n a : ℕ} [NeZero n] :
    Function.Surjective (SquareCompatTrace (n := n) (a := a)) := by
  intro S
  refine ⟨SquareCompatTraceSection (n := n) (a := a) S, ?_⟩
  funext t
  exact SquareCompatTrace_section_apply (n := n) (a := a) S t

theorem finrank_ker_SquareCompatTrace_add_core
    {n a : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F (LinearMap.ker (SquareCompatTrace (n := n) (a := a)))
      + n * (n - 1) ^ 2 =
    (n - 1) ^ 2 * n ^ a := by
  let L := SquareCompatTrace (n := n) (a := a)
  have hnull := LinearMap.finrank_range_add_finrank_ker L
  have hsurj : LinearMap.range L = ⊤ :=
    LinearMap.range_eq_top.mpr (SquareCompatTrace_surjective (n := n) (a := a))
  rw [hsurj, finrank_top, finrank_SquareCompatCore, finrank_SquareCompatCoeff ha] at hnull
  calc
    Module.finrank F (LinearMap.ker L) + n * (n - 1) ^ 2
        = n * (n - 1) ^ 2 + Module.finrank F (LinearMap.ker L) := by
            ring
    _ = (n - 1) ^ 2 * n ^ a := hnull

noncomputable def BDiagWDiagInfCoeffRead
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (x : ↑(BDiagSpace (n := n) (a := a) (b := b) (d := d) ⊓
      WDiagSpace (n := n) (a := a) (b := b) (d := d))) :
    SquareCompatCoeff n a :=
  Classical.choose
    (show ∃ T : SquareCompatCoeff n a,
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) T = x.1 by
      have hx :
          x.1 ∈ LinearMap.range
            (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)) := by
        rw [range_SquareCompatEmbed_eq_inf_BDiag_WDiag
          (n := n) (a := a) (b := b) (d := d) hb hd]
        exact x.2
      exact hx)

lemma SquareCompatEmbed_BDiagWDiagInfCoeffRead
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (x : ↑(BDiagSpace (n := n) (a := a) (b := b) (d := d) ⊓
      WDiagSpace (n := n) (a := a) (b := b) (d := d))) :
    SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
        (BDiagWDiagInfCoeffRead (n := n) (a := a) (b := b) (d := d) hb hd x) =
      x.1 := by
  unfold BDiagWDiagInfCoeffRead
  exact Classical.choose_spec
    (show ∃ T : SquareCompatCoeff n a,
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) T = x.1 by
      have hx :
          x.1 ∈ LinearMap.range
            (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)) := by
        rw [range_SquareCompatEmbed_eq_inf_BDiag_WDiag
          (n := n) (a := a) (b := b) (d := d) hb hd]
        exact x.2
      exact hx)

noncomputable def BDiagWDiagInfEquivCoeff
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    ↑(BDiagSpace (n := n) (a := a) (b := b) (d := d) ⊓
      WDiagSpace (n := n) (a := a) (b := b) (d := d)) ≃ₗ[F]
      SquareCompatCoeff n a where
  toFun := BDiagWDiagInfCoeffRead (n := n) (a := a) (b := b) (d := d) hb hd
  invFun T :=
    ⟨SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) T, by
      rw [← range_SquareCompatEmbed_eq_inf_BDiag_WDiag
        (n := n) (a := a) (b := b) (d := d) hb hd]
      exact ⟨T, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact SquareCompatEmbed_BDiagWDiagInfCoeffRead
      (n := n) (a := a) (b := b) (d := d) hb hd x
  right_inv T := by
    apply SquareCompatEmbed_injective (n := n) (a := a) (b := b) (d := d) hb hd
    exact SquareCompatEmbed_BDiagWDiagInfCoeffRead
      (n := n) (a := a) (b := b) (d := d) hb hd
      ⟨SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) T, by
        rw [← range_SquareCompatEmbed_eq_inf_BDiag_WDiag
          (n := n) (a := a) (b := b) (d := d) hb hd]
        exact ⟨T, rfl⟩⟩
  map_add' x y := by
    apply SquareCompatEmbed_injective (n := n) (a := a) (b := b) (d := d) hb hd
    rw [SquareCompatEmbed_BDiagWDiagInfCoeffRead
      (n := n) (a := a) (b := b) (d := d) hb hd (x + y)]
    rw [(SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)).map_add]
    rw [SquareCompatEmbed_BDiagWDiagInfCoeffRead
      (n := n) (a := a) (b := b) (d := d) hb hd x]
    rw [SquareCompatEmbed_BDiagWDiagInfCoeffRead
      (n := n) (a := a) (b := b) (d := d) hb hd y]
    rfl
  map_smul' r x := by
    apply SquareCompatEmbed_injective (n := n) (a := a) (b := b) (d := d) hb hd
    rw [SquareCompatEmbed_BDiagWDiagInfCoeffRead
      (n := n) (a := a) (b := b) (d := d) hb hd (r • x)]
    rw [(SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)).map_smul]
    rw [SquareCompatEmbed_BDiagWDiagInfCoeffRead
      (n := n) (a := a) (b := b) (d := d) hb hd x]
    rfl

end Core4loop
