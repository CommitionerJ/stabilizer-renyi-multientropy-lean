import Core4loop.RootSpaces.Intersections

open scoped BigOperators

namespace Core4loop

private lemma F_eq_of_add_eq_zero {x y : F} (h : x + y = 0) : x = y := by
  calc
    x = x + 0 := by simp
    _ = x + (y + y) := by rw [F_add_self y]
    _ = (x + y) + y := by ring
    _ = y := by
      rw [h]
      simp

theorem sup_inf_YW_ZW_le_inf_sup_YZ_W {n b c d : ℕ} [NeZero n] :
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊔
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d)) ≤
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
      WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  intro f hf
  rcases Submodule.mem_sup.mp hf with ⟨fy, hfy, fz, hfz, rfl⟩
  constructor
  · exact Submodule.mem_sup.mpr ⟨fy, hfy.1, fz, hfz.1, rfl⟩
  · exact Submodule.add_mem
      (WDiffSpace (n := n) (b := b) (c := c) (d := d)) hfy.2 hfz.2

theorem inf_YW_inf_ZW_eq_inf_YZW {n b c d : ℕ} [NeZero n] :
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d)) =
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
      WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  apply le_antisymm
  · intro f hf
    exact ⟨⟨hf.1.1, hf.2.1⟩, hf.1.2⟩
  · intro f hf
    exact ⟨⟨hf.1.1, hf.2⟩, ⟨hf.1.2, hf.2⟩⟩

theorem finrank_sup_inf_YW_ZW_add_finrank_inf {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
            WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊔
          (ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
            WDiffSpace (n := n) (b := b) (c := c) (d := d))))
      + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ b := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
      WDiffSpace (n := n) (b := b) (c := c) (d := d))
    (ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
      WDiffSpace (n := n) (b := b) (c := c) (d := d))
  rw [inf_YW_inf_ZW_eq_inf_YZW (n := n) (b := b) (c := c) (d := d),
    finrank_inf_YZW (n := n) (b := b) (c := c) (d := d) hb hc hd,
    finrank_inf_YW (n := n) (b := b) (c := c) (d := d) hb hd,
    finrank_inf_ZW (n := n) (b := b) (c := c) (d := d) hc hd] at h
  exact h

theorem inf_sup_YZ_W_le_sup_inf_YW_ZW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
      WDiffSpace (n := n) (b := b) (c := c) (d := d) ≤
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊔
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d)) := by
  classical
  intro f hf
  rcases Submodule.mem_sup.mp hf.1 with ⟨fy, hfy, fz, hfz, hsum⟩
  rcases hfy with ⟨U, hU⟩
  rcases hfz with ⟨V, hV⟩
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
  have hrel_wOf :
      ∀ (y : YVec n b) (z : ZVec n c) (sw : I n),
        (U z (wOf sw)).1 (vecSum y) + (V y (wOf sw)).1 (vecSum z) =
          (R y z).1 sw := by
    intro y z sw
    have hu := congrFun (congrFun (congrFun hU y) z) (wOf sw)
    have hv := congrFun (congrFun (congrFun hV y) z) (wOf sw)
    have hs := congrFun (congrFun (congrFun hsum y) z) (wOf sw)
    have hr := congrFun (congrFun (congrFun hR y) z) (wOf sw)
    have hu' : (U z (wOf sw)).1 (vecSum y) = fy y z (wOf sw) := by
      simpa [YDiffEmbed] using hu
    have hv' : (V y (wOf sw)).1 (vecSum z) = fz y z (wOf sw) := by
      simpa [ZDiffEmbed] using hv
    have hr' : (R y z).1 sw = f y z (wOf sw) := by
      simpa [WDiffEmbed, hwOf sw] using hr
    calc
      (U z (wOf sw)).1 (vecSum y) + (V y (wOf sw)).1 (vecSum z)
          = fy y z (wOf sw) + fz y z (wOf sw) := by
              rw [hu', hv']
      _ = f y z (wOf sw) := by
              simpa using hs
      _ = (R y z).1 sw := by
              exact hr'.symm
  have hsumU_eq_sumV :
      ∀ (y : YVec n b) (z : ZVec n c),
        (∑ sw : I n, (U z (wOf sw)).1 (vecSum y)) =
          ∑ sw : I n, (V y (wOf sw)).1 (vecSum z) := by
    intro y z
    apply F_eq_of_add_eq_zero
    calc
      (∑ sw : I n, (U z (wOf sw)).1 (vecSum y)) +
          (∑ sw : I n, (V y (wOf sw)).1 (vecSum z))
          = ∑ sw : I n,
              ((U z (wOf sw)).1 (vecSum y) + (V y (wOf sw)).1 (vecSum z)) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ sw : I n, (R y z).1 sw := by
              refine Finset.sum_congr rfl ?_
              intro sw _
              exact hrel_wOf y z sw
      _ = 0 := by
              exact LinearMap.mem_ker.mp (R y z).2
  let C : I n → I n → F := fun sy sz =>
    ∑ sw : I n, (U (zOf sz) (wOf sw)).1 sy
  have hsumU_eq_C :
      ∀ (z : ZVec n c) (sy : I n),
        (∑ sw : I n, (U z (wOf sw)).1 sy) = C sy (vecSum z) := by
    intro z sy
    calc
      (∑ sw : I n, (U z (wOf sw)).1 sy)
          = ∑ sw : I n, (V (yOf sy) (wOf sw)).1 (vecSum z) := by
              simpa [hyOf sy] using hsumU_eq_sumV (yOf sy) z
      _ = ∑ sw : I n, (U (zOf (vecSum z)) (wOf sw)).1 sy := by
              have h := hsumU_eq_sumV (yOf sy) (zOf (vecSum z))
              simpa [hyOf sy, hzOf (vecSum z)] using h.symm
      _ = C sy (vecSum z) := rfl
  have hsumV_eq_C :
      ∀ (y : YVec n b) (sz : I n),
        (∑ sw : I n, (V y (wOf sw)).1 sz) = C (vecSum y) sz := by
    intro y sz
    calc
      (∑ sw : I n, (V y (wOf sw)).1 sz)
          = ∑ sw : I n, (U (zOf sz) (wOf sw)).1 (vecSum y) := by
              have h := hsumU_eq_sumV y (zOf sz)
              simpa [hzOf sz] using h.symm
      _ = C (vecSum y) sz := rfl
  have hC_sum_sy_zero : ∀ sz : I n, (∑ sy : I n, C sy sz) = 0 := by
    intro sz
    calc
      (∑ sy : I n, C sy sz)
          = ∑ sy : I n, ∑ sw : I n, (U (zOf sz) (wOf sw)).1 sy := rfl
      _ = ∑ sw : I n, ∑ sy : I n, (U (zOf sz) (wOf sw)).1 sy := by
              rw [Finset.sum_comm]
      _ = ∑ sw : I n, 0 := by
              refine Finset.sum_congr rfl ?_
              intro sw _
              have hzero : (∑ sy : I n, (U (zOf sz) (wOf sw)).1 sy) = 0 := by
                exact LinearMap.mem_ker.mp (U (zOf sz) (wOf sw)).2
              exact hzero
      _ = 0 := by simp
  have hC_sum_sz_zero : ∀ sy : I n, (∑ sz : I n, C sy sz) = 0 := by
    intro sy
    calc
      (∑ sz : I n, C sy sz)
          = ∑ sz : I n, ∑ sw : I n, (V (yOf sy) (wOf sw)).1 sz := by
              refine Finset.sum_congr rfl ?_
              intro sz _
              have h := hsumV_eq_C (yOf sy) sz
              simpa [hyOf sy] using h.symm
      _ = ∑ sw : I n, ∑ sz : I n, (V (yOf sy) (wOf sw)).1 sz := by
              rw [Finset.sum_comm]
      _ = ∑ sw : I n, 0 := by
              refine Finset.sum_congr rfl ?_
              intro sw _
              have hzero : (∑ sz : I n, (V (yOf sy) (wOf sw)).1 sz) = 0 := by
                exact LinearMap.mem_ker.mp (V (yOf sy) (wOf sw)).2
              exact hzero
      _ = 0 := by simp
  let L : I n → I n → I n → F := fun sy sz sw =>
    if sw = 0 then C sy sz else 0
  have hL_sum_sw : ∀ sy sz : I n, (∑ sw : I n, L sy sz sw) = C sy sz := by
    intro sy sz
    simp [L]
  have hL_sum_sy : ∀ sz sw : I n, (∑ sy : I n, L sy sz sw) = 0 := by
    intro sz sw
    by_cases hsw : sw = 0
    · simp [L, hsw, hC_sum_sy_zero sz]
    · simp [L, hsw]
  have hL_sum_sz : ∀ sy sw : I n, (∑ sz : I n, L sy sz sw) = 0 := by
    intro sy sw
    by_cases hsw : sw = 0
    · simp [L, hsw, hC_sum_sz_zero sy]
    · simp [L, hsw]
  let A : YWCoeff n c := fun z =>
    ⟨fun sy sw => (U z (wOf sw)).1 sy + L sy (vecSum z) sw, by
      constructor
      · apply LinearMap.mem_ker.mpr
        funext sy
        calc
          (∑ sw : I n, ((U z (wOf sw)).1 sy + L sy (vecSum z) sw))
              = (∑ sw : I n, (U z (wOf sw)).1 sy) +
                  ∑ sw : I n, L sy (vecSum z) sw := by
                    rw [Finset.sum_add_distrib]
          _ = C sy (vecSum z) + C sy (vecSum z) := by
                    rw [hsumU_eq_C z sy, hL_sum_sw sy (vecSum z)]
          _ = 0 := F_add_self (C sy (vecSum z))
      · apply LinearMap.mem_ker.mpr
        funext sw
        calc
          (∑ sy : I n, ((U z (wOf sw)).1 sy + L sy (vecSum z) sw))
              = (∑ sy : I n, (U z (wOf sw)).1 sy) +
                  ∑ sy : I n, L sy (vecSum z) sw := by
                    rw [Finset.sum_add_distrib]
          _ = 0 + 0 := by
                    have hzero : (∑ sy : I n, (U z (wOf sw)).1 sy) = 0 := by
                      exact LinearMap.mem_ker.mp (U z (wOf sw)).2
                    rw [hzero, hL_sum_sy (vecSum z) sw]
          _ = 0 := by simp⟩
  let B : ZWCoeff n b := fun y =>
    ⟨fun sz sw => (V y (wOf sw)).1 sz + L (vecSum y) sz sw, by
      constructor
      · apply LinearMap.mem_ker.mpr
        funext sz
        calc
          (∑ sw : I n, ((V y (wOf sw)).1 sz + L (vecSum y) sz sw))
              = (∑ sw : I n, (V y (wOf sw)).1 sz) +
                  ∑ sw : I n, L (vecSum y) sz sw := by
                    rw [Finset.sum_add_distrib]
          _ = C (vecSum y) sz + C (vecSum y) sz := by
                    rw [hsumV_eq_C y sz, hL_sum_sw (vecSum y) sz]
          _ = 0 := F_add_self (C (vecSum y) sz)
      · apply LinearMap.mem_ker.mpr
        funext sw
        calc
          (∑ sz : I n, ((V y (wOf sw)).1 sz + L (vecSum y) sz sw))
              = (∑ sz : I n, (V y (wOf sw)).1 sz) +
                  ∑ sz : I n, L (vecSum y) sz sw := by
                    rw [Finset.sum_add_distrib]
          _ = 0 + 0 := by
                    have hzero : (∑ sz : I n, (V y (wOf sw)).1 sz) = 0 := by
                      exact LinearMap.mem_ker.mp (V y (wOf sw)).2
                    rw [hzero, hL_sum_sz (vecSum y) sw]
          _ = 0 := by simp⟩
  refine Submodule.mem_sup.mpr ⟨
    pullYW (n := n) (b := b) (c := c) (d := d) A, ?_,
    pullZW (n := n) (b := b) (c := c) (d := d) B, ?_, ?_⟩
  · rw [← range_pullYW_eq_inf_YW (n := n) (b := b) (c := c) (d := d) hb hd]
    exact ⟨A, rfl⟩
  · rw [← range_pullZW_eq_inf_ZW (n := n) (b := b) (c := c) (d := d) hc hd]
    exact ⟨B, rfl⟩
  · funext y z w
    let sy : I n := vecSum y
    let sz : I n := vecSum z
    let sw : I n := vecSum w
    have hrel_final :
        (U z (wOf sw)).1 sy + (V y (wOf sw)).1 sz = f y z w := by
      calc
        (U z (wOf sw)).1 sy + (V y (wOf sw)).1 sz
            = (R y z).1 sw := by
                simpa [sy, sz] using hrel_wOf y z sw
        _ = f y z w := by
                have hr := congrFun (congrFun (congrFun hR y) z) w
                simpa [WDiffEmbed, sw] using hr
    calc
      (pullYW (n := n) (b := b) (c := c) (d := d) A +
          pullZW (n := n) (b := b) (c := c) (d := d) B) y z w
          = ((U z (wOf sw)).1 sy + L sy sz sw) +
              ((V y (wOf sw)).1 sz + L sy sz sw) := by
                simp [pullYW, pullZW, A, B, sy, sz, sw]
      _ = ((U z (wOf sw)).1 sy + (V y (wOf sw)).1 sz) +
            (L sy sz sw + L sy sz sw) := by
              ring
      _ = (U z (wOf sw)).1 sy + (V y (wOf sw)).1 sz := by
              rw [F_add_self (L sy sz sw)]
              simp
      _ = f y z w := hrel_final

theorem inf_sup_YZ_W_eq_sup_inf_YW_ZW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
      WDiffSpace (n := n) (b := b) (c := c) (d := d) =
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊔
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d)) := by
  apply le_antisymm
  · exact inf_sup_YZ_W_le_sup_inf_YW_ZW
      (n := n) (b := b) (c := c) (d := d) hb hc hd
  · exact sup_inf_YW_ZW_le_inf_sup_YZ_W (n := n) (b := b) (c := c) (d := d)

theorem finrank_sup_YZW_add_pair_infs {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (↑(((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
              ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊔
            WDiffSpace (n := n) (b := b) (c := c) (d := d))))
      + (n - 1) ^ 2 * n ^ d
      + (n - 1) ^ 2 * n ^ c
      + (n - 1) ^ 2 * n ^ b =
      (n - 1) * n ^ (c + d)
      + (n - 1) * n ^ (b + d)
      + (n - 1) * n ^ (b + c)
      + (n - 1) ^ 3 := by
  have hYZ := finrank_sup_YZ_add_finrank_inf
    (n := n) (b := b) (c := c) (d := d) hb hc
  have hYWZW := finrank_sup_inf_YW_ZW_add_finrank_inf
    (n := n) (b := b) (c := c) (d := d) hb hc hd
  have hTop := Submodule.finrank_sup_add_finrank_inf_eq
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
      ZDiffSpace (n := n) (b := b) (c := c) (d := d))
    (WDiffSpace (n := n) (b := b) (c := c) (d := d))
  rw [inf_sup_YZ_W_eq_sup_inf_YW_ZW
      (n := n) (b := b) (c := c) (d := d) hb hc hd,
    finrank_WDiffSpace (n := n) (b := b) (c := c) (d := d) hd] at hTop
  omega

theorem finrank_inf_sup_YW_Z_add_finrank_inf_YZW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
            WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b := by
  have hTop := Submodule.finrank_sup_add_finrank_inf_eq
    (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
      WDiffSpace (n := n) (b := b) (c := c) (d := d))
    (ZDiffSpace (n := n) (b := b) (c := c) (d := d))
  have hSupPerm :
      (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊔
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) =
      (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊔
        WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
    ac_rfl
  rw [hSupPerm] at hTop
  have hYW := finrank_sup_YW_add_finrank_inf
    (n := n) (b := b) (c := c) (d := d) hb hd
  have hYZW := finrank_sup_YZW_add_pair_infs
    (n := n) (b := b) (c := c) (d := d) hb hc hd
  have hYZ := finrank_inf_YZ (n := n) (b := b) (c := c) (d := d) hb hc
  have hYWInf := finrank_inf_YW (n := n) (b := b) (c := c) (d := d) hb hd
  have hZW := finrank_inf_ZW (n := n) (b := b) (c := c) (d := d) hc hd
  have hTriple :=
    finrank_inf_YZW (n := n) (b := b) (c := c) (d := d) hb hc hd
  have hZ := finrank_ZDiffSpace (n := n) (b := b) (c := c) (d := d) hc
  omega

end Core4loop
