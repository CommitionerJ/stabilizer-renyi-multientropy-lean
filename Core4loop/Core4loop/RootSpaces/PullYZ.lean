import Core4loop.RootSpaces.Basic

namespace Core4loop

abbrev YZCoeff (n d : ℕ) [NeZero n] := WVec n d → MatrixZeroSum n
abbrev YWCoeff (n c : ℕ) [NeZero n] := ZVec n c → MatrixZeroSum n
abbrev ZWCoeff (n b : ℕ) [NeZero n] := YVec n b → MatrixZeroSum n

noncomputable def pullYZ {n b c d : ℕ} [NeZero n] :
    YZCoeff n d →ₗ[F] RootTarget n b c d where
  toFun M := fun y z w => (M w).1 (vecSum y) (vecSum z)
  map_add' M N := by
    funext y z w
    rfl
  map_smul' r M := by
    funext y z w
    rfl

noncomputable def pullYW {n b c d : ℕ} [NeZero n] :
    YWCoeff n c →ₗ[F] RootTarget n b c d where
  toFun M := fun y z w => (M z).1 (vecSum y) (vecSum w)
  map_add' M N := by
    funext y z w
    rfl
  map_smul' r M := by
    funext y z w
    rfl

noncomputable def pullZW {n b c d : ℕ} [NeZero n] :
    ZWCoeff n b →ₗ[F] RootTarget n b c d where
  toFun M := fun y z w => (M y).1 (vecSum z) (vecSum w)
  map_add' M N := by
    funext y z w
    rfl
  map_smul' r M := by
    funext y z w
    rfl

theorem pullYZ_injective {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Function.Injective (pullYZ (n := n) (b := b) (c := c) (d := d)) := by
  intro M N h
  funext w
  apply Subtype.ext
  funext sy sz
  rcases vecSum_surjective (n := n) (k := b) hb sy with ⟨y, hy⟩
  rcases vecSum_surjective (n := n) (k := c) hc sz with ⟨z, hz⟩
  have hv := congrFun (congrFun (congrFun h y) z) w
  simpa [pullYZ, hy, hz] using hv

theorem pullYW_injective {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    Function.Injective (pullYW (n := n) (b := b) (c := c) (d := d)) := by
  intro M N h
  funext z
  apply Subtype.ext
  funext sy sw
  rcases vecSum_surjective (n := n) (k := b) hb sy with ⟨y, hy⟩
  rcases vecSum_surjective (n := n) (k := d) hd sw with ⟨w, hw⟩
  have hv := congrFun (congrFun (congrFun h y) z) w
  simpa [pullYW, hy, hw] using hv

theorem pullZW_injective {n b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    Function.Injective (pullZW (n := n) (b := b) (c := c) (d := d)) := by
  intro M N h
  funext y
  apply Subtype.ext
  funext sz sw
  rcases vecSum_surjective (n := n) (k := c) hc sz with ⟨z, hz⟩
  rcases vecSum_surjective (n := n) (k := d) hd sw with ⟨w, hw⟩
  have hv := congrFun (congrFun (congrFun h y) z) w
  simpa [pullZW, hz, hw] using hv

lemma finrank_YZCoeff {n d : ℕ} [NeZero n] :
    Module.finrank F (YZCoeff n d) = n ^ d * (n - 1) ^ 2 := by
  calc
    Module.finrank F (YZCoeff n d)
        = ∑ _ : WVec n d, Module.finrank F (MatrixZeroSum n) := by
            simp [YZCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : WVec n d => MatrixZeroSum n)]
    _ = Fintype.card (WVec n d) * (n - 1) ^ 2 := by
            simp [finrank_MatrixZeroSum]
    _ = n ^ d * (n - 1) ^ 2 := by
            rw [card_vec]

lemma finrank_YWCoeff {n c : ℕ} [NeZero n] :
    Module.finrank F (YWCoeff n c) = n ^ c * (n - 1) ^ 2 := by
  calc
    Module.finrank F (YWCoeff n c)
        = ∑ _ : ZVec n c, Module.finrank F (MatrixZeroSum n) := by
            simp [YWCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : ZVec n c => MatrixZeroSum n)]
    _ = Fintype.card (ZVec n c) * (n - 1) ^ 2 := by
            simp [finrank_MatrixZeroSum]
    _ = n ^ c * (n - 1) ^ 2 := by
            rw [card_vec]

lemma finrank_ZWCoeff {n b : ℕ} [NeZero n] :
    Module.finrank F (ZWCoeff n b) = n ^ b * (n - 1) ^ 2 := by
  calc
    Module.finrank F (ZWCoeff n b)
        = ∑ _ : YVec n b, Module.finrank F (MatrixZeroSum n) := by
            simp [ZWCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : YVec n b => MatrixZeroSum n)]
    _ = Fintype.card (YVec n b) * (n - 1) ^ 2 := by
            simp [finrank_MatrixZeroSum]
    _ = n ^ b * (n - 1) ^ 2 := by
            rw [card_vec]

theorem finrank_range_pullYZ {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Module.finrank F
      (LinearMap.range (pullYZ (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) ^ 2 * n ^ d := by
  calc
    Module.finrank F
      (LinearMap.range (pullYZ (n := n) (b := b) (c := c) (d := d)))
        = Module.finrank F (YZCoeff n d) := by
            exact LinearMap.finrank_range_of_inj
              (pullYZ_injective (n := n) (b := b) (c := c) (d := d) hb hc)
    _ = (n - 1) ^ 2 * n ^ d := by
            rw [finrank_YZCoeff]
            ring

theorem finrank_range_pullYW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F
      (LinearMap.range (pullYW (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) ^ 2 * n ^ c := by
  calc
    Module.finrank F
      (LinearMap.range (pullYW (n := n) (b := b) (c := c) (d := d)))
        = Module.finrank F (YWCoeff n c) := by
            exact LinearMap.finrank_range_of_inj
              (pullYW_injective (n := n) (b := b) (c := c) (d := d) hb hd)
    _ = (n - 1) ^ 2 * n ^ c := by
            rw [finrank_YWCoeff]
            ring

theorem finrank_range_pullZW {n b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
      (LinearMap.range (pullZW (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) ^ 2 * n ^ b := by
  calc
    Module.finrank F
      (LinearMap.range (pullZW (n := n) (b := b) (c := c) (d := d)))
        = Module.finrank F (ZWCoeff n b) := by
            exact LinearMap.finrank_range_of_inj
              (pullZW_injective (n := n) (b := b) (c := c) (d := d) hc hd)
    _ = (n - 1) ^ 2 * n ^ b := by
            rw [finrank_ZWCoeff]
            ring

theorem range_pullYZ_le_inf_YZ {n b c d : ℕ} [NeZero n] :
    LinearMap.range (pullYZ (n := n) (b := b) (c := c) (d := d)) ≤
      YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  intro f hf
  rcases hf with ⟨M, rfl⟩
  constructor
  · refine ⟨(fun z w =>
      ⟨fun sy => (M w).1 sy (vecSum z), ?_⟩), ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact matrix_col_zero (M w) (vecSum z)
    · funext y z w
      rfl
  · refine ⟨(fun y w =>
      ⟨fun sz => (M w).1 (vecSum y) sz, ?_⟩), ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact matrix_row_zero (M w) (vecSum y)
    · funext y z w
      rfl

theorem inf_YZ_le_range_pullYZ {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) ≤
      LinearMap.range (pullYZ (n := n) (b := b) (c := c) (d := d)) := by
  classical
  intro f hf
  rcases hf.1 with ⟨U, hU⟩
  rcases hf.2 with ⟨V, hV⟩
  let yOf : I n → YVec n b := fun sy =>
    Classical.choose (vecSum_surjective (n := n) (k := b) hb sy)
  let zOf : I n → ZVec n c := fun sz =>
    Classical.choose (vecSum_surjective (n := n) (k := c) hc sz)
  have hyOf : ∀ sy : I n, vecSum (yOf sy) = sy := by
    intro sy
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := b) hb sy)
  have hzOf : ∀ sz : I n, vecSum (zOf sz) = sz := by
    intro sz
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := c) hc sz)
  let M : YZCoeff n d := fun w =>
    ⟨fun sy sz => f (yOf sy) (zOf sz) w, by
      constructor
      · apply LinearMap.mem_ker.mpr
        funext sy
        calc
          (∑ sz : I n, f (yOf sy) (zOf sz) w)
              = ∑ sz : I n, (V (yOf sy) w).1 sz := by
                  refine Finset.sum_congr rfl ?_
                  intro sz _
                  have hv := congrFun (congrFun (congrFun hV (yOf sy)) (zOf sz)) w
                  exact (by simpa [ZDiffEmbed, hzOf sz] using hv.symm)
          _ = 0 := by
                  exact LinearMap.mem_ker.mp (V (yOf sy) w).2
      · apply LinearMap.mem_ker.mpr
        funext sz
        calc
          (∑ sy : I n, f (yOf sy) (zOf sz) w)
              = ∑ sy : I n, (U (zOf sz) w).1 sy := by
                  refine Finset.sum_congr rfl ?_
                  intro sy _
                  have hu := congrFun (congrFun (congrFun hU (yOf sy)) (zOf sz)) w
                  exact (by simpa [YDiffEmbed, hyOf sy] using hu.symm)
          _ = 0 := by
                  exact LinearMap.mem_ker.mp (U (zOf sz) w).2⟩
  refine ⟨M, ?_⟩
  funext y z w
  let sy : I n := vecSum y
  let sz : I n := vecSum z
  calc
    (pullYZ (n := n) (b := b) (c := c) (d := d) M) y z w
        = f (yOf sy) (zOf sz) w := rfl
    _ = (U (zOf sz) w).1 sy := by
          have hu := congrFun (congrFun (congrFun hU (yOf sy)) (zOf sz)) w
          exact (by simpa [YDiffEmbed, sy, hyOf sy] using hu.symm)
    _ = f y (zOf sz) w := by
          have hu := congrFun (congrFun (congrFun hU y) (zOf sz)) w
          exact (by simpa [YDiffEmbed, sy] using hu)
    _ = (V y w).1 sz := by
          have hv := congrFun (congrFun (congrFun hV y) (zOf sz)) w
          exact (by simpa [ZDiffEmbed, sz, hzOf sz] using hv.symm)
    _ = f y z w := by
          have hv := congrFun (congrFun (congrFun hV y) z) w
          exact (by simpa [ZDiffEmbed, sz] using hv)

theorem range_pullYZ_eq_inf_YZ {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    LinearMap.range (pullYZ (n := n) (b := b) (c := c) (d := d)) =
      YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  apply le_antisymm
  · exact range_pullYZ_le_inf_YZ (n := n) (b := b) (c := c) (d := d)
  · exact inf_YZ_le_range_pullYZ (n := n) (b := b) (c := c) (d := d) hb hc

theorem range_pullYW_le_inf_YW {n b c d : ℕ} [NeZero n] :
    LinearMap.range (pullYW (n := n) (b := b) (c := c) (d := d)) ≤
      YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  intro f hf
  rcases hf with ⟨M, rfl⟩
  constructor
  · refine ⟨(fun z w =>
      ⟨fun sy => (M z).1 sy (vecSum w), ?_⟩), ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact matrix_col_zero (M z) (vecSum w)
    · funext y z w
      rfl
  · refine ⟨(fun y z =>
      ⟨fun sw => (M z).1 (vecSum y) sw, ?_⟩), ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact matrix_row_zero (M z) (vecSum y)
    · funext y z w
      rfl

theorem inf_YW_le_range_pullYW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d) ≤
      LinearMap.range (pullYW (n := n) (b := b) (c := c) (d := d)) := by
  classical
  intro f hf
  rcases hf.1 with ⟨U, hU⟩
  rcases hf.2 with ⟨R, hR⟩
  let yOf : I n → YVec n b := fun sy =>
    Classical.choose (vecSum_surjective (n := n) (k := b) hb sy)
  let wOf : I n → WVec n d := fun sw =>
    Classical.choose (vecSum_surjective (n := n) (k := d) hd sw)
  have hyOf : ∀ sy : I n, vecSum (yOf sy) = sy := by
    intro sy
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := b) hb sy)
  have hwOf : ∀ sw : I n, vecSum (wOf sw) = sw := by
    intro sw
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := d) hd sw)
  let M : YWCoeff n c := fun z =>
    ⟨fun sy sw => f (yOf sy) z (wOf sw), by
      constructor
      · apply LinearMap.mem_ker.mpr
        funext sy
        calc
          (∑ sw : I n, f (yOf sy) z (wOf sw))
              = ∑ sw : I n, (R (yOf sy) z).1 sw := by
                  refine Finset.sum_congr rfl ?_
                  intro sw _
                  have hr := congrFun (congrFun (congrFun hR (yOf sy)) z) (wOf sw)
                  exact (by simpa [WDiffEmbed, hwOf sw] using hr.symm)
          _ = 0 := by
                  exact LinearMap.mem_ker.mp (R (yOf sy) z).2
      · apply LinearMap.mem_ker.mpr
        funext sw
        calc
          (∑ sy : I n, f (yOf sy) z (wOf sw))
              = ∑ sy : I n, (U z (wOf sw)).1 sy := by
                  refine Finset.sum_congr rfl ?_
                  intro sy _
                  have hu := congrFun (congrFun (congrFun hU (yOf sy)) z) (wOf sw)
                  exact (by simpa [YDiffEmbed, hyOf sy] using hu.symm)
          _ = 0 := by
                  exact LinearMap.mem_ker.mp (U z (wOf sw)).2⟩
  refine ⟨M, ?_⟩
  funext y z w
  let sy : I n := vecSum y
  let sw : I n := vecSum w
  calc
    (pullYW (n := n) (b := b) (c := c) (d := d) M) y z w
        = f (yOf sy) z (wOf sw) := rfl
    _ = (U z (wOf sw)).1 sy := by
          have hu := congrFun (congrFun (congrFun hU (yOf sy)) z) (wOf sw)
          exact (by simpa [YDiffEmbed, sy, hyOf sy] using hu.symm)
    _ = f y z (wOf sw) := by
          have hu := congrFun (congrFun (congrFun hU y) z) (wOf sw)
          exact (by simpa [YDiffEmbed, sy] using hu)
    _ = (R y z).1 sw := by
          have hr := congrFun (congrFun (congrFun hR y) z) (wOf sw)
          exact (by simpa [WDiffEmbed, sw, hwOf sw] using hr.symm)
    _ = f y z w := by
          have hr := congrFun (congrFun (congrFun hR y) z) w
          exact (by simpa [WDiffEmbed, sw] using hr)

theorem range_pullYW_eq_inf_YW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    LinearMap.range (pullYW (n := n) (b := b) (c := c) (d := d)) =
      YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  apply le_antisymm
  · exact range_pullYW_le_inf_YW (n := n) (b := b) (c := c) (d := d)
  · exact inf_YW_le_range_pullYW (n := n) (b := b) (c := c) (d := d) hb hd

theorem range_pullZW_le_inf_ZW {n b c d : ℕ} [NeZero n] :
    LinearMap.range (pullZW (n := n) (b := b) (c := c) (d := d)) ≤
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  intro f hf
  rcases hf with ⟨M, rfl⟩
  constructor
  · refine ⟨(fun y w =>
      ⟨fun sz => (M y).1 sz (vecSum w), ?_⟩), ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact matrix_col_zero (M y) (vecSum w)
    · funext y z w
      rfl
  · refine ⟨(fun y z =>
      ⟨fun sw => (M y).1 (vecSum z) sw, ?_⟩), ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact matrix_row_zero (M y) (vecSum z)
    · funext y z w
      rfl

theorem inf_ZW_le_range_pullZW {n b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d) ≤
      LinearMap.range (pullZW (n := n) (b := b) (c := c) (d := d)) := by
  classical
  intro f hf
  rcases hf.1 with ⟨V, hV⟩
  rcases hf.2 with ⟨R, hR⟩
  let zOf : I n → ZVec n c := fun sz =>
    Classical.choose (vecSum_surjective (n := n) (k := c) hc sz)
  let wOf : I n → WVec n d := fun sw =>
    Classical.choose (vecSum_surjective (n := n) (k := d) hd sw)
  have hzOf : ∀ sz : I n, vecSum (zOf sz) = sz := by
    intro sz
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := c) hc sz)
  have hwOf : ∀ sw : I n, vecSum (wOf sw) = sw := by
    intro sw
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := d) hd sw)
  let M : ZWCoeff n b := fun y =>
    ⟨fun sz sw => f y (zOf sz) (wOf sw), by
      constructor
      · apply LinearMap.mem_ker.mpr
        funext sz
        calc
          (∑ sw : I n, f y (zOf sz) (wOf sw))
              = ∑ sw : I n, (R y (zOf sz)).1 sw := by
                  refine Finset.sum_congr rfl ?_
                  intro sw _
                  have hr := congrFun (congrFun (congrFun hR y) (zOf sz)) (wOf sw)
                  exact (by simpa [WDiffEmbed, hwOf sw] using hr.symm)
          _ = 0 := by
                  exact LinearMap.mem_ker.mp (R y (zOf sz)).2
      · apply LinearMap.mem_ker.mpr
        funext sw
        calc
          (∑ sz : I n, f y (zOf sz) (wOf sw))
              = ∑ sz : I n, (V y (wOf sw)).1 sz := by
                  refine Finset.sum_congr rfl ?_
                  intro sz _
                  have hv := congrFun (congrFun (congrFun hV y) (zOf sz)) (wOf sw)
                  exact (by simpa [ZDiffEmbed, hzOf sz] using hv.symm)
          _ = 0 := by
                  exact LinearMap.mem_ker.mp (V y (wOf sw)).2⟩
  refine ⟨M, ?_⟩
  funext y z w
  let sz : I n := vecSum z
  let sw : I n := vecSum w
  calc
    (pullZW (n := n) (b := b) (c := c) (d := d) M) y z w
        = f y (zOf sz) (wOf sw) := rfl
    _ = (V y (wOf sw)).1 sz := by
          have hv := congrFun (congrFun (congrFun hV y) (zOf sz)) (wOf sw)
          exact (by simpa [ZDiffEmbed, sz, hzOf sz] using hv.symm)
    _ = f y z (wOf sw) := by
          have hv := congrFun (congrFun (congrFun hV y) z) (wOf sw)
          exact (by simpa [ZDiffEmbed, sz] using hv)
    _ = (R y z).1 sw := by
          have hr := congrFun (congrFun (congrFun hR y) z) (wOf sw)
          exact (by simpa [WDiffEmbed, sw, hwOf sw] using hr.symm)
    _ = f y z w := by
          have hr := congrFun (congrFun (congrFun hR y) z) w
          exact (by simpa [WDiffEmbed, sw] using hr)

theorem range_pullZW_eq_inf_ZW {n b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    LinearMap.range (pullZW (n := n) (b := b) (c := c) (d := d)) =
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  apply le_antisymm
  · exact range_pullZW_le_inf_ZW (n := n) (b := b) (c := c) (d := d)
  · exact inf_ZW_le_range_pullZW (n := n) (b := b) (c := c) (d := d) hc hd

end Core4loop
