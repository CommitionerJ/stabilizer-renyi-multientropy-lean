import Core4loop.Square.Rank.CoreParam
import Core4loop.RootSpaces.Intersections

open scoped BigOperators

namespace Core4loop

noncomputable def SquareRootTrace {n c : ℕ} [NeZero n] :
    YWCoeff n c →ₗ[F] SquareRootCore n where
  toFun M := fun sz => ∑ z : ZVec n c, if vecSum z = sz then M z else 0
  map_add' M N := by
    funext sz
    apply Subtype.ext
    funext sy sw
    change
      ((Submodule.subtype (MatrixZeroSum n))
        (∑ z : ZVec n c, if vecSum z = sz then (M + N) z else 0)) sy sw =
        ((Submodule.subtype (MatrixZeroSum n))
          ((∑ z : ZVec n c, if vecSum z = sz then M z else 0) +
            ∑ z : ZVec n c, if vecSum z = sz then N z else 0)) sy sw
    rw [map_add]
    simp only [Pi.add_apply]
    have hL :
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ z : ZVec n c, if vecSum z = sz then M z + N z else 0)) sy sw =
          ∑ z : ZVec n c,
            if vecSum z = sz then (M z).1 sy sw + (N z).1 sy sw else 0 := by
      rw [map_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : vecSum z = sz <;> simp [hz]
    have hM :
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ z : ZVec n c, if vecSum z = sz then M z else 0)) sy sw =
          ∑ z : ZVec n c, if vecSum z = sz then (M z).1 sy sw else 0 := by
      rw [map_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : vecSum z = sz <;> simp [hz]
    have hN :
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ z : ZVec n c, if vecSum z = sz then N z else 0)) sy sw =
          ∑ z : ZVec n c, if vecSum z = sz then (N z).1 sy sw else 0 := by
      rw [map_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : vecSum z = sz <;> simp [hz]
    rw [hL, hM, hN]
    rw [sum_if_add_F]
  map_smul' r M := by
    funext sz
    apply Subtype.ext
    funext sy sw
    change
      ((Submodule.subtype (MatrixZeroSum n))
        (∑ z : ZVec n c, if vecSum z = sz then (r • M) z else 0)) sy sw =
        ((Submodule.subtype (MatrixZeroSum n))
          (r • ∑ z : ZVec n c, if vecSum z = sz then M z else 0)) sy sw
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hL :
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ z : ZVec n c, if vecSum z = sz then r • M z else 0)) sy sw =
          ∑ z : ZVec n c, if vecSum z = sz then r * (M z).1 sy sw else 0 := by
      rw [map_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : vecSum z = sz <;> simp [hz, smul_eq_mul]
    have hM :
        ((Submodule.subtype (MatrixZeroSum n))
          (∑ z : ZVec n c, if vecSum z = sz then M z else 0)) sy sw =
          ∑ z : ZVec n c, if vecSum z = sz then (M z).1 sy sw else 0 := by
      rw [map_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : vecSum z = sz <;> simp [hz]
    rw [hL, hM]
    rw [sum_if_mul_F]

noncomputable def SquareRootTraceSection {n c : ℕ} [NeZero n]
    (hc : 0 < c) (R : SquareRootCore n) : YWCoeff n c :=
  fun z => if z = vecSumRep (n := n) (k := c) hc (vecSum z) then R (vecSum z) else 0

lemma SquareRootTrace_section_apply
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (R : SquareRootCore n) (sz : I n) :
    SquareRootTrace (n := n) (c := c)
        (SquareRootTraceSection (n := n) (c := c) hc R) sz = R sz := by
  classical
  change
    (∑ z : ZVec n c,
      if vecSum z = sz then SquareRootTraceSection (n := n) (c := c) hc R z else 0) =
      R sz
  unfold SquareRootTraceSection
  rw [Finset.sum_eq_single (vecSumRep (n := n) (k := c) hc sz)]
  · rw [vecSum_vecSumRep (n := n) (k := c) hc sz]
    simp
  · intro z _ hz
    by_cases hvec : vecSum z = sz
    · simp [hvec, hz]
    · simp [hvec]
  · intro hnot
    simp at hnot

theorem SquareRootTrace_surjective
    {n c : ℕ} [NeZero n] (hc : 0 < c) :
    Function.Surjective (SquareRootTrace (n := n) (c := c)) := by
  intro R
  refine ⟨SquareRootTraceSection (n := n) (c := c) hc R, ?_⟩
  funext sz
  exact SquareRootTrace_section_apply (n := n) (c := c) hc R sz

theorem finrank_ker_SquareRootTrace_add_core
    {n c : ℕ} [NeZero n] (hc : 0 < c) :
    Module.finrank F (LinearMap.ker (SquareRootTrace (n := n) (c := c)))
      + n * (n - 1) ^ 2 =
    (n - 1) ^ 2 * n ^ c := by
  let L := SquareRootTrace (n := n) (c := c)
  have hnull := LinearMap.finrank_range_add_finrank_ker L
  have hsurj : LinearMap.range L = ⊤ :=
    LinearMap.range_eq_top.mpr (SquareRootTrace_surjective (n := n) (c := c) hc)
  rw [hsurj, finrank_top, finrank_SquareRootCore, finrank_YWCoeff] at hnull
  calc
    Module.finrank F (LinearMap.ker L) + n * (n - 1) ^ 2
        = n * (n - 1) ^ 2 + Module.finrank F (LinearMap.ker L) := by
            ring
    _ = n ^ c * (n - 1) ^ 2 := hnull
    _ = (n - 1) ^ 2 * n ^ c := by
            ring

noncomputable def YWInfCoeffRead
    {n b c d : ℕ} [NeZero n] (hb : 0 < b) (hd : 0 < d)
    (x : ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
      WDiffSpace (n := n) (b := b) (c := c) (d := d))) :
    YWCoeff n c :=
  Classical.choose
    (show ∃ M : YWCoeff n c,
        pullYW (n := n) (b := b) (c := c) (d := d) M = x.1 by
      have hx : x.1 ∈ LinearMap.range (pullYW (n := n) (b := b) (c := c) (d := d)) := by
        rw [range_pullYW_eq_inf_YW (n := n) (b := b) (c := c) (d := d) hb hd]
        exact x.2
      exact hx)

lemma pullYW_YWInfCoeffRead
    {n b c d : ℕ} [NeZero n] (hb : 0 < b) (hd : 0 < d)
    (x : ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
      WDiffSpace (n := n) (b := b) (c := c) (d := d))) :
    pullYW (n := n) (b := b) (c := c) (d := d)
        (YWInfCoeffRead (n := n) (b := b) (c := c) (d := d) hb hd x) = x.1 := by
  unfold YWInfCoeffRead
  exact Classical.choose_spec
    (show ∃ M : YWCoeff n c,
        pullYW (n := n) (b := b) (c := c) (d := d) M = x.1 by
      have hx : x.1 ∈ LinearMap.range (pullYW (n := n) (b := b) (c := c) (d := d)) := by
        rw [range_pullYW_eq_inf_YW (n := n) (b := b) (c := c) (d := d) hb hd]
        exact x.2
      exact hx)

noncomputable def YWInfEquivCoeff
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
      WDiffSpace (n := n) (b := b) (c := c) (d := d)) ≃ₗ[F]
      YWCoeff n c where
  toFun := YWInfCoeffRead (n := n) (b := b) (c := c) (d := d) hb hd
  invFun M :=
    ⟨pullYW (n := n) (b := b) (c := c) (d := d) M, by
      rw [← range_pullYW_eq_inf_YW (n := n) (b := b) (c := c) (d := d) hb hd]
      exact ⟨M, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact pullYW_YWInfCoeffRead (n := n) (b := b) (c := c) (d := d) hb hd x
  right_inv M := by
    apply pullYW_injective (n := n) (b := b) (c := c) (d := d) hb hd
    exact pullYW_YWInfCoeffRead (n := n) (b := b) (c := c) (d := d) hb hd
      ⟨pullYW (n := n) (b := b) (c := c) (d := d) M, by
        rw [← range_pullYW_eq_inf_YW (n := n) (b := b) (c := c) (d := d) hb hd]
        exact ⟨M, rfl⟩⟩
  map_add' x y := by
    apply pullYW_injective (n := n) (b := b) (c := c) (d := d) hb hd
    rw [pullYW_YWInfCoeffRead (n := n) (b := b) (c := c) (d := d) hb hd (x + y)]
    rw [(pullYW (n := n) (b := b) (c := c) (d := d)).map_add]
    rw [pullYW_YWInfCoeffRead (n := n) (b := b) (c := c) (d := d) hb hd x]
    rw [pullYW_YWInfCoeffRead (n := n) (b := b) (c := c) (d := d) hb hd y]
    rfl
  map_smul' a x := by
    apply pullYW_injective (n := n) (b := b) (c := c) (d := d) hb hd
    rw [pullYW_YWInfCoeffRead (n := n) (b := b) (c := c) (d := d) hb hd (a • x)]
    rw [(pullYW (n := n) (b := b) (c := c) (d := d)).map_smul]
    rw [pullYW_YWInfCoeffRead (n := n) (b := b) (c := c) (d := d) hb hd x]
    rfl

end Core4loop
