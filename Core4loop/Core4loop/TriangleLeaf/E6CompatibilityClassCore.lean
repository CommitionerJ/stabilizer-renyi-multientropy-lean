import Core4loop.TriangleLeaf.E6SharedKernelEquiv
import Core4loop.TriangleLeaf.E6ShearedS1Witness
import Core4loop.TriangleLeaf.E6ThetaQuotient

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
# Triangle+leaf E6 compatibility-class quotient

This file identifies the intrinsic compatibility-class quotient `J0` with
the pair-curl quotient.  The proof uses equality of the two actual kernels:
no finrank comparison is used.

The results are logical-level 5 structural certificates.  They prove no
residual signed-sum, raw `Delta`, support, `Gamma`, or catalogue theorem.
-/

theorem ker_triangleLeafE6BarO_eq_map_alpha_CCompat
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    LinearMap.ker
        (triangleLeafE6BarO
          (n := n) (a := a) (b := b) (c := c) (d := d) hb) =
      Submodule.map
        (triangleLeafBDiagAlpha
          (n := n) (a := a) (b := b) (d := d))
        (triangleLeafCCompat n a b c d) := by
  let alpha :=
    triangleLeafBDiagAlpha
      (n := n) (a := a) (b := b) (d := d)
  let O :=
    triangleLeafE6Obstruction
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have halpha : Function.Surjective alpha :=
    triangleLeafBDiagAlpha_surjective hb
  apply le_antisymm
  · intro x hx
    rcases halpha x with ⟨C, rfl⟩
    have hq :
        C ∈ LinearMap.ker
          (rangeQuotientMap O (LinearMap.ker alpha)) := by
      apply LinearMap.mem_ker.mpr
      rw [← barO_apply_alpha alpha O halpha]
      exact LinearMap.mem_ker.mp hx
    rw [ker_rangeQuotientMap] at hq
    rcases Submodule.mem_sup.mp hq with ⟨C₀, hC₀, C₁, hC₁, hsum⟩
    refine ⟨C₁, ?_, ?_⟩
    · rw [triangleLeafCCompat_eq_ker_e6Obstruction]
      exact hC₁
    · have hAlphaC₀ : alpha C₀ = 0 := LinearMap.mem_ker.mp hC₀
      rw [← hsum, map_add, hAlphaC₀, zero_add]
  · rintro x ⟨C, hC, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [triangleLeafE6BarO_apply_alpha hb]
    apply LinearMap.mem_ker.mp
    rw [ker_rangeQuotientMap]
    apply (le_sup_right :
      LinearMap.ker O ≤ LinearMap.ker alpha ⊔ LinearMap.ker O)
    rw [← triangleLeafCCompat_eq_ker_e6Obstruction]
    exact hC

noncomputable def triangleLeafE6ThetaAfterAlphaToShear
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    Module.Dual F (BDiagCoeff n a d) →ₗ[F]
      ((WVec n d → PairCurlSpace n) ⧸
        triangleLeafE6PairCurlHdiff n d) :=
  (triangleLeafE6Theta
      (n := n) (a := a) (b := b) (c := c) (d := d) hb).comp
    (triangleLeafE6AlphaToShearEquiv
      (n := n) (a := a) (b := b) (d := d) hb).toLinearMap

theorem triangleLeafE6ThetaAfterAlphaToShear_surjective
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Surjective
      (triangleLeafE6ThetaAfterAlphaToShear
        (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  exact
    (triangleLeafE6Theta_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) hb).comp
      (triangleLeafE6AlphaToShearEquiv
        (n := n) (a := a) (b := b) (d := d) hb).surjective

theorem ker_triangleLeafE6BarO_eq_ker_thetaAfterAlphaToShear
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd : 0 < d) :
    LinearMap.ker
        (triangleLeafE6BarO
          (n := n) (a := a) (b := b) (c := c) (d := d) (by omega)) =
      LinearMap.ker
        (triangleLeafE6ThetaAfterAlphaToShear
          (n := n) (a := a) (b := b) (c := c) (d := d) (by omega)) := by
  let alpha :=
    triangleLeafBDiagAlpha
      (n := n) (a := a) (b := b) (d := d)
  let eAlpha :=
    triangleLeafE6AlphaShearCoeff
      (n := n) (a := a) (b := b) (d := d)
  let e :=
    triangleLeafE6AlphaToShearEquiv
      (n := n) (a := a) (b := b) (d := d) (by omega : 0 < b)
  let theta :=
    triangleLeafE6Theta
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (by omega : 0 < b)
  have halpha : Function.Surjective alpha :=
    triangleLeafBDiagAlpha_surjective (by omega)
  have hImage :
      Submodule.map eAlpha (triangleLeafCCompat n a b c d) =
        LinearMap.ker theta := by
    calc
      Submodule.map eAlpha (triangleLeafCCompat n a b c d) =
          LinearMap.range
            (triangleLeafBOnlyBDiagMap
              (n := n) (a := a) (b := b) (c := c) (d := d)) :=
        map_triangleLeafE6AlphaShearCoeff_CCompat_eq_range_BOnlyBDiag
          hn hb2 hc
      _ = LinearMap.ker theta :=
        (ker_triangleLeafE6Theta_eq_range_BOnlyBDiag
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (by omega) hc hd).symm
  rw [ker_triangleLeafE6BarO_eq_map_alpha_CCompat (by omega)]
  apply le_antisymm
  · rintro x ⟨C, hC, rfl⟩
    apply LinearMap.mem_ker.mpr
    change theta (e (alpha C)) = 0
    rw [triangleLeafE6AlphaToShearEquiv_apply_alpha]
    apply LinearMap.mem_ker.mp
    rw [← hImage]
    exact ⟨C, hC, rfl⟩
  · intro x hx
    rcases halpha x with ⟨C, rfl⟩
    have hTheta : eAlpha C ∈ LinearMap.ker theta := by
      apply LinearMap.mem_ker.mpr
      have hxZero := LinearMap.mem_ker.mp hx
      change theta (e (alpha C)) = 0 at hxZero
      rw [show e (alpha C) = eAlpha C by
        exact triangleLeafE6AlphaToShearEquiv_apply_alpha _ _] at hxZero
      exact hxZero
    have hMap :
        eAlpha C ∈
          Submodule.map eAlpha (triangleLeafCCompat n a b c d) := by
      rw [hImage]
      exact hTheta
    rcases hMap with ⟨C', hC', hEq⟩
    refine ⟨C', hC', ?_⟩
    apply e.injective
    rw [triangleLeafE6AlphaToShearEquiv_apply_alpha,
      triangleLeafE6AlphaToShearEquiv_apply_alpha]
    exact hEq

noncomputable def triangleLeafE6J0EquivPairCurl
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd : 0 < d) :
    triangleLeafE6J0 n a b c d ≃ₗ[F]
      ((WVec n d → PairCurlSpace n) ⧸
        triangleLeafE6PairCurlHdiff n d) := by
  let barO :=
    triangleLeafE6BarO
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (by omega : 0 < b)
  let thetaAfter :=
    triangleLeafE6ThetaAfterAlphaToShear
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (by omega : 0 < b)
  have hBarO : Function.Surjective barO :=
    triangleLeafE6BarO_surjective (by omega)
  have hThetaAfter : Function.Surjective thetaAfter :=
    triangleLeafE6ThetaAfterAlphaToShear_surjective (by omega)
  have hKer : LinearMap.ker barO = LinearMap.ker thetaAfter :=
    ker_triangleLeafE6BarO_eq_ker_thetaAfterAlphaToShear
      hn hb2 hc hd
  exact
    ((LinearMap.quotKerEquivOfSurjective barO hBarO).symm.trans
      (Submodule.quotEquivOfEq
        (LinearMap.ker barO) (LinearMap.ker thetaAfter) hKer)).trans
      (LinearMap.quotKerEquivOfSurjective thetaAfter hThetaAfter)

@[simp]
theorem triangleLeafE6J0EquivPairCurl_apply_barO
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd : 0 < d)
    (x : Module.Dual F (BDiagCoeff n a d)) :
    triangleLeafE6J0EquivPairCurl hn hb2 hc hd
        (triangleLeafE6BarO
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (by omega) x) =
      triangleLeafE6Theta
        (n := n) (a := a) (b := b) (c := c) (d := d) (by omega)
        (triangleLeafE6AlphaToShearEquiv
          (n := n) (a := a) (b := b) (d := d) (by omega) x) := by
  unfold triangleLeafE6J0EquivPairCurl
  simp only [LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

@[simp]
theorem triangleLeafE6J0EquivPairCurl_apply_alpha
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd : 0 < d)
    (C : CFun4 n a b d) :
    triangleLeafE6J0EquivPairCurl hn hb2 hc hd
        (triangleLeafE6BarO
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (by omega)
          (triangleLeafBDiagAlpha
            (n := n) (a := a) (b := b) (d := d) C)) =
      triangleLeafE6Theta
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (by omega)
        (triangleLeafE6AlphaShearCoeff
          (n := n) (a := a) (b := b) (d := d) C) := by
  rw [triangleLeafE6J0EquivPairCurl_apply_barO]
  change
    triangleLeafE6Theta
        (n := n) (a := a) (b := b) (c := c) (d := d) (by omega)
        (triangleLeafE6AlphaToShearEquiv
          (n := n) (a := a) (b := b) (d := d) (by omega)
          (triangleLeafBDiagAlpha
            (n := n) (a := a) (b := b) (d := d) C)) =
      triangleLeafE6Theta
        (n := n) (a := a) (b := b) (c := c) (d := d) (by omega)
        (triangleLeafE6AlphaShearCoeff
          (n := n) (a := a) (b := b) (d := d) C)
  rw [triangleLeafE6AlphaToShearEquiv_apply_alpha]

end

end TriangleLeaf
end Core4loop
