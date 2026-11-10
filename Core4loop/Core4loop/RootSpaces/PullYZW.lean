import Core4loop.RootSpaces.Basic

namespace Core4loop

noncomputable def pullYZW {n b c d : ℕ} [NeZero n] :
    CubeZeroSum n →ₗ[F] RootTarget n b c d where
  toFun T := fun y z w => T.1 (vecSum y) (vecSum z) (vecSum w)
  map_add' T U := by
    funext y z w
    rfl
  map_smul' r T := by
    funext y z w
    rfl

theorem pullYZW_injective {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Function.Injective (pullYZW (n := n) (b := b) (c := c) (d := d)) := by
  intro T U h
  apply Subtype.ext
  funext sy sz sw
  rcases vecSum_surjective (n := n) (k := b) hb sy with ⟨y, hy⟩
  rcases vecSum_surjective (n := n) (k := c) hc sz with ⟨z, hz⟩
  rcases vecSum_surjective (n := n) (k := d) hd sw with ⟨w, hw⟩
  have hv := congrFun (congrFun (congrFun h y) z) w
  simpa [pullYZW, hy, hz, hw] using hv

theorem finrank_range_pullYZW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
      (LinearMap.range (pullYZW (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) ^ 3 := by
  calc
    Module.finrank F
      (LinearMap.range (pullYZW (n := n) (b := b) (c := c) (d := d)))
        = Module.finrank F (CubeZeroSum n) := by
            exact LinearMap.finrank_range_of_inj
              (pullYZW_injective (n := n) (b := b) (c := c) (d := d) hb hc hd)
    _ = (n - 1) ^ 3 := finrank_CubeZeroSum

theorem range_pullYZW_le_inf_YZW {n b c d : ℕ} [NeZero n] :
    LinearMap.range (pullYZW (n := n) (b := b) (c := c) (d := d)) ≤
      (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  intro f hf
  rcases hf with ⟨T, rfl⟩
  constructor
  · constructor
    · refine ⟨(fun z w =>
        ⟨fun sy => T.1 sy (vecSum z) (vecSum w), ?_⟩), ?_⟩
      · apply LinearMap.mem_ker.mpr
        exact cube_sumX_zero T (vecSum z) (vecSum w)
      · funext y z w
        rfl
    · refine ⟨(fun y w =>
        ⟨fun sz => T.1 (vecSum y) sz (vecSum w), ?_⟩), ?_⟩
      · apply LinearMap.mem_ker.mpr
        exact cube_sumY_zero T (vecSum y) (vecSum w)
      · funext y z w
        rfl
  · refine ⟨(fun y z =>
      ⟨fun sw => T.1 (vecSum y) (vecSum z) sw, ?_⟩), ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact cube_sumZ_zero T (vecSum y) (vecSum z)
    · funext y z w
      rfl

theorem inf_YZW_le_range_pullYZW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
      WDiffSpace (n := n) (b := b) (c := c) (d := d) ≤
    LinearMap.range (pullYZW (n := n) (b := b) (c := c) (d := d)) := by
  classical
  intro f hf
  rcases hf.1.1 with ⟨U, hU⟩
  rcases hf.1.2 with ⟨V, hV⟩
  rcases hf.2 with ⟨R, hR⟩
  let yOf : I n → YVec n b := fun sy =>
    Classical.choose (vecSum_surjective (n := n) (k := b) hb sy)
  let zOf : I n → ZVec n c := fun sz =>
    Classical.choose (vecSum_surjective (n := n) (k := c) hc sz)
  let wOf : I n → WVec n d := fun sw =>
    Classical.choose (vecSum_surjective (n := n) (k := d) hd sw)
  have hyOf : ∀ sy : I n, vecSum (yOf sy) = sy := by
    intro sy
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := b) hb sy)
  have hzOf : ∀ sz : I n, vecSum (zOf sz) = sz := by
    intro sz
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := c) hc sz)
  have hwOf : ∀ sw : I n, vecSum (wOf sw) = sw := by
    intro sw
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := d) hd sw)
  let T : CubeZeroSum n :=
    ⟨fun sy sz sw => f (yOf sy) (zOf sz) (wOf sw), by
      constructor
      · constructor
        · apply LinearMap.mem_ker.mpr
          funext sz sw
          calc
            (∑ sy : I n, f (yOf sy) (zOf sz) (wOf sw))
                = ∑ sy : I n, (U (zOf sz) (wOf sw)).1 sy := by
                    refine Finset.sum_congr rfl ?_
                    intro sy _
                    have hu := congrFun (congrFun (congrFun hU (yOf sy)) (zOf sz)) (wOf sw)
                    exact (by simpa [YDiffEmbed, hyOf sy] using hu.symm)
            _ = 0 := by
                    exact LinearMap.mem_ker.mp (U (zOf sz) (wOf sw)).2
        · apply LinearMap.mem_ker.mpr
          funext sy sw
          calc
            (∑ sz : I n, f (yOf sy) (zOf sz) (wOf sw))
                = ∑ sz : I n, (V (yOf sy) (wOf sw)).1 sz := by
                    refine Finset.sum_congr rfl ?_
                    intro sz _
                    have hv := congrFun (congrFun (congrFun hV (yOf sy)) (zOf sz)) (wOf sw)
                    exact (by simpa [ZDiffEmbed, hzOf sz] using hv.symm)
            _ = 0 := by
                    exact LinearMap.mem_ker.mp (V (yOf sy) (wOf sw)).2
      · apply LinearMap.mem_ker.mpr
        funext sy sz
        calc
          (∑ sw : I n, f (yOf sy) (zOf sz) (wOf sw))
              = ∑ sw : I n, (R (yOf sy) (zOf sz)).1 sw := by
                  refine Finset.sum_congr rfl ?_
                  intro sw _
                  have hr := congrFun (congrFun (congrFun hR (yOf sy)) (zOf sz)) (wOf sw)
                  exact (by simpa [WDiffEmbed, hwOf sw] using hr.symm)
          _ = 0 := by
                  exact LinearMap.mem_ker.mp (R (yOf sy) (zOf sz)).2⟩
  refine ⟨T, ?_⟩
  funext y z w
  let sy : I n := vecSum y
  let sz : I n := vecSum z
  let sw : I n := vecSum w
  calc
    (pullYZW (n := n) (b := b) (c := c) (d := d) T) y z w
        = f (yOf sy) (zOf sz) (wOf sw) := rfl
    _ = (U (zOf sz) (wOf sw)).1 sy := by
          have hu := congrFun (congrFun (congrFun hU (yOf sy)) (zOf sz)) (wOf sw)
          exact (by simpa [YDiffEmbed, sy, hyOf sy] using hu.symm)
    _ = f y (zOf sz) (wOf sw) := by
          have hu := congrFun (congrFun (congrFun hU y) (zOf sz)) (wOf sw)
          exact (by simpa [YDiffEmbed, sy] using hu)
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

theorem range_pullYZW_eq_inf_YZW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    LinearMap.range (pullYZW (n := n) (b := b) (c := c) (d := d)) =
      (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  apply le_antisymm
  · exact range_pullYZW_le_inf_YZW (n := n) (b := b) (c := c) (d := d)
  · exact inf_YZW_le_range_pullYZW (n := n) (b := b) (c := c) (d := d) hb hc hd

end Core4loop
