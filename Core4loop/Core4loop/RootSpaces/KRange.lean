import Core4loop.RootSpaces.Distributivity

open scoped BigOperators

namespace Core4loop

noncomputable def KBMap {n a b c d : ℕ} [NeZero n] :
    BFun4 n a c d →ₗ[F] RootTarget n b c d where
  toFun B := fun y z w => ∑ p : PVec n a, dyB B p y z w
  map_add' B B' := by
    funext y z w
    unfold dyB betaB gammaB
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  map_smul' r B := by
    funext y z w
    unfold dyB betaB gammaB
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring

noncomputable def KCMap {n a b c d : ℕ} [NeZero n] :
    CFun4 n a b d →ₗ[F] RootTarget n b c d where
  toFun C := fun y z w => ∑ p : PVec n a, dzC C p y z w
  map_add' C C' := by
    funext y z w
    unfold dzC deltaC etaC
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  map_smul' r C := by
    funext y z w
    unfold dzC deltaC etaC
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring

noncomputable def KWMap {n a b c d : ℕ} [NeZero n] :
    WFun4 n a b c →ₗ[F] RootTarget n b c d where
  toFun W := fun y z w => ∑ p : PVec n a, dwW W p y z w
  map_add' W W' := by
    funext y z w
    unfold dwW xiW zetaW
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  map_smul' r W := by
    funext y z w
    unfold dwW xiW zetaW
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring

theorem range_KBMap_eq_YDiffSpace {n a b c d : ℕ} [NeZero n] :
    LinearMap.range (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)) =
      YDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨B, rfl⟩
    let U : YCoeff n c d := fun z w =>
      ⟨cycDiff (n := n) F (fun sy => ∑ p : PVec n a, B p sy z w),
        cycDiff_mem_ZeroSumProfile (fun sy => ∑ p : PVec n a, B p sy z w)⟩
    refine ⟨U, ?_⟩
    funext y z w
    simp [KBMap, YDiffEmbed, U, cycDiff, dyB, betaB, gammaB, Finset.sum_add_distrib]
  · intro f hf
    rcases hf with ⟨U, rfl⟩
    choose H hH using fun z w =>
      show ∃ h : Profile n, cycDiff (n := n) F h = (U z w).1 by
        have hm : (U z w).1 ∈ LinearMap.range (cycDiff (n := n) F) := by
          rw [range_cycDiff_eq_ZeroSumProfile]
          exact (U z w).2
        exact hm
    let B : BFun4 n a c d := fun p sy z w =>
      if p = (zeroVec : PVec n a) then H z w sy else 0
    refine ⟨B, ?_⟩
    funext y z w
    have hpoint := congrFun (hH z w) (vecSum y)
    calc
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B y z w
          = H z w (vecSum y) + H z w (vecSum y + 1) := by
              simp [KBMap, B, dyB, betaB, gammaB, Finset.sum_add_distrib]
      _ = (U z w).1 (vecSum y) := by
              simpa [cycDiff] using hpoint

theorem range_KCMap_eq_ZDiffSpace {n a b c d : ℕ} [NeZero n] :
    LinearMap.range (KCMap (n := n) (a := a) (b := b) (c := c) (d := d)) =
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨C, rfl⟩
    let V : ZCoeff n b d := fun y w =>
      ⟨cycDiff (n := n) F (fun sz => ∑ p : PVec n a, C p y sz w),
        cycDiff_mem_ZeroSumProfile (fun sz => ∑ p : PVec n a, C p y sz w)⟩
    refine ⟨V, ?_⟩
    funext y z w
    simp [KCMap, ZDiffEmbed, V, cycDiff, dzC, deltaC, etaC, Finset.sum_add_distrib]
  · intro f hf
    rcases hf with ⟨V, rfl⟩
    choose H hH using fun y w =>
      show ∃ h : Profile n, cycDiff (n := n) F h = (V y w).1 by
        have hm : (V y w).1 ∈ LinearMap.range (cycDiff (n := n) F) := by
          rw [range_cycDiff_eq_ZeroSumProfile]
          exact (V y w).2
        exact hm
    let C : CFun4 n a b d := fun p y sz w =>
      if p = (zeroVec : PVec n a) then H y w sz else 0
    refine ⟨C, ?_⟩
    funext y z w
    have hpoint := congrFun (hH y w) (vecSum z)
    calc
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C y z w
          = H y w (vecSum z) + H y w (vecSum z + 1) := by
              simp [KCMap, C, dzC, deltaC, etaC, Finset.sum_add_distrib]
      _ = (V y w).1 (vecSum z) := by
              simpa [cycDiff] using hpoint

theorem range_KWMap_eq_WDiffSpace {n a b c d : ℕ} [NeZero n] :
    LinearMap.range (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)) =
      WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨W, rfl⟩
    let R : WCoeff n b c := fun y z =>
      ⟨cycDiff (n := n) F (fun sw => ∑ p : PVec n a, W p y z sw),
        cycDiff_mem_ZeroSumProfile (fun sw => ∑ p : PVec n a, W p y z sw)⟩
    refine ⟨R, ?_⟩
    funext y z w
    simp [KWMap, WDiffEmbed, R, cycDiff, dwW, xiW, zetaW, Finset.sum_add_distrib]
  · intro f hf
    rcases hf with ⟨R, rfl⟩
    choose H hH using fun y z =>
      show ∃ h : Profile n, cycDiff (n := n) F h = (R y z).1 by
        have hm : (R y z).1 ∈ LinearMap.range (cycDiff (n := n) F) := by
          rw [range_cycDiff_eq_ZeroSumProfile]
          exact (R y z).2
        exact hm
    let W : WFun4 n a b c := fun p y z sw =>
      if p = (zeroVec : PVec n a) then H y z sw else 0
    refine ⟨W, ?_⟩
    funext y z w
    have hpoint := congrFun (hH y z) (vecSum w)
    calc
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W y z w
          = H y z (vecSum w) + H y z (vecSum w + 1) := by
              simp [KWMap, W, dwW, xiW, zetaW, Finset.sum_add_distrib]
      _ = (R y z).1 (vecSum w) := by
              simpa [cycDiff] using hpoint

theorem range_K_yzw_eq_sup_YZW {n a b c d : ℕ} [NeZero n] :
    LinearMap.range (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d)) =
      (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊔
      WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨x, rfl⟩
    refine Submodule.mem_sup.mpr ⟨
      (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) x.1) +
        (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) x.2.1), ?_,
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d) x.2.2, ?_, ?_⟩
    · refine Submodule.mem_sup.mpr ⟨
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) x.1, ?_,
        KCMap (n := n) (a := a) (b := b) (c := c) (d := d) x.2.1, ?_, rfl⟩
      · rw [← range_KBMap_eq_YDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
        exact ⟨x.1, rfl⟩
      · rw [← range_KCMap_eq_ZDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
        exact ⟨x.2.1, rfl⟩
    · rw [← range_KWMap_eq_WDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
      exact ⟨x.2.2, rfl⟩
    · funext y z w
      change
        (∑ p : PVec n a, dyB x.1 p y z w) +
            (∑ p : PVec n a, dzC x.2.1 p y z w) +
            (∑ p : PVec n a, dwW x.2.2 p y z w) =
          ∑ p : PVec n a,
            (dyB x.1 p y z w + dzC x.2.1 p y z w + dwW x.2.2 p y z w)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  · intro f hf
    rcases Submodule.mem_sup.mp hf with ⟨fYZ, hfYZ, fW, hfW, rfl⟩
    rcases Submodule.mem_sup.mp hfYZ with ⟨fY, hfY, fZ, hfZ, rfl⟩
    rw [← range_KBMap_eq_YDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)] at hfY
    rw [← range_KCMap_eq_ZDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)] at hfZ
    rw [← range_KWMap_eq_WDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)] at hfW
    rcases hfY with ⟨B, rfl⟩
    rcases hfZ with ⟨C, rfl⟩
    rcases hfW with ⟨W, rfl⟩
    refine ⟨(B, C, W), ?_⟩
    funext y z w
    change
      (∑ p : PVec n a, (dyB B p y z w + dzC C p y z w + dwW W p y z w)) =
        (∑ p : PVec n a, dyB B p y z w) +
          (∑ p : PVec n a, dzC C p y z w) +
          (∑ p : PVec n a, dwW W p y z w)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem range_K_yw_eq_sup_YW {n a b c d : ℕ} [NeZero n] :
    LinearMap.range (K_yw (n := n) (a := a) (b := b) (c := c) (d := d)) =
      YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
        WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨x, rfl⟩
    refine Submodule.mem_sup.mpr ⟨
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) x.1, ?_,
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d) x.2, ?_, ?_⟩
    · rw [← range_KBMap_eq_YDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
      exact ⟨x.1, rfl⟩
    · rw [← range_KWMap_eq_WDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
      exact ⟨x.2, rfl⟩
    · funext y z w
      change
        (∑ p : PVec n a, dyB x.1 p y z w) +
            (∑ p : PVec n a, dwW x.2 p y z w) =
          ∑ p : PVec n a, (dyB x.1 p y z w + dwW x.2 p y z w)
      rw [Finset.sum_add_distrib]
  · intro f hf
    rcases Submodule.mem_sup.mp hf with ⟨fY, hfY, fW, hfW, rfl⟩
    rw [← range_KBMap_eq_YDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)] at hfY
    rw [← range_KWMap_eq_WDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)] at hfW
    rcases hfY with ⟨B, rfl⟩
    rcases hfW with ⟨W, rfl⟩
    refine ⟨(B, W), ?_⟩
    funext y z w
    change
      (∑ p : PVec n a, (dyB B p y z w + dwW W p y z w)) =
        (∑ p : PVec n a, dyB B p y z w) +
          (∑ p : PVec n a, dwW W p y z w)
    rw [Finset.sum_add_distrib]

theorem finrank_range_K_yzw_add_pair_infs {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ d
      + (n - 1) ^ 2 * n ^ c
      + (n - 1) ^ 2 * n ^ b =
      (n - 1) * n ^ (c + d)
      + (n - 1) * n ^ (b + d)
      + (n - 1) * n ^ (b + c)
      + (n - 1) ^ 3 := by
  rw [range_K_yzw_eq_sup_YZW (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact finrank_sup_YZW_add_pair_infs (n := n) (b := b) (c := c) (d := d) hb hc hd

theorem finrank_range_K_yw_add_inf {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range (K_yw (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ c =
      (n - 1) * n ^ (c + d) + (n - 1) * n ^ (b + c) := by
  rw [range_K_yw_eq_sup_YW (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact finrank_sup_YW_add_finrank_inf (n := n) (b := b) (c := c) (d := d) hb hd

end Core4loop
