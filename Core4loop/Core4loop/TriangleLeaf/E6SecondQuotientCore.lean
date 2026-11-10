import Core4loop.LinearAlgebra.RangeQuotient
import Core4loop.TriangleLeaf.E6CoeffPairingCore

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Generic second-quotient specialization for the TriangleLeaf E6 coefficient map.

This file contains only intrinsic range quotients and the `alpha`/`rho`
factorization.  It makes no coordinate, parity, or rank claim.
-/

abbrev triangleLeafE6RelationSpace
    (n b c d : ℕ) [NeZero n] :
    Submodule F (RootTarget n b c d) :=
  YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
    WDiffSpace (n := n) (b := b) (c := c) (d := d)

noncomputable def triangleLeafE6Obstruction
    {n a b c d : ℕ} [NeZero n] :
    CFun4 n a b d →ₗ[F]
      (RootTarget n b c d ⧸ triangleLeafE6RelationSpace n b c d) :=
  (Submodule.mkQ (triangleLeafE6RelationSpace n b c d)).comp
    (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))

abbrev triangleLeafE6K0
    (n a b d : ℕ) [NeZero n] :
    Submodule F (CFun4 n a b d) :=
  LinearMap.ker
    (triangleLeafBDiagAlpha (n := n) (a := a) (b := b) (d := d))

abbrev triangleLeafE6K1
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (Module.Dual F (BDiagCoeff n a d)) :=
  LinearMap.ker
    (triangleLeafBOnlyBDiagDualRestrict
      (n := n) (a := a) (b := b) (c := c) (d := d))

abbrev triangleLeafE6J0
    (n a b c d : ℕ) [NeZero n] :=
  LinearMap.range
      (triangleLeafE6Obstruction
        (n := n) (a := a) (b := b) (c := c) (d := d)) ⧸
    restrictedImage
      (triangleLeafE6Obstruction
        (n := n) (a := a) (b := b) (c := c) (d := d))
      (triangleLeafE6K0 n a b d)

theorem triangleLeafCCompat_eq_ker_e6Obstruction
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafCCompat n a b c d =
      LinearMap.ker
        (triangleLeafE6Obstruction
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  ext C
  rw [mem_triangleLeafCCompat_iff_KCMap_mem_sup,
    LinearMap.mem_ker]
  change
    KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C ∈
        triangleLeafE6RelationSpace n b c d ↔
      Submodule.Quotient.mk
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) =
        0
  exact
    (Submodule.Quotient.mk_eq_zero
      (triangleLeafE6RelationSpace n b c d)).symm

theorem ker_triangleLeafQ1BOnlyCoeffAll_eq_comap_K1
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (triangleLeafQ1BOnlyCoeffAll
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      Submodule.comap
        (triangleLeafBDiagAlpha
          (n := n) (a := a) (b := b) (d := d))
        (triangleLeafE6K1 n a b c d) := by
  rw [triangleLeafQ1BOnlyCoeffAll_eq_dualRestrict_comp_alpha]
  exact LinearMap.ker_comp _ _

noncomputable def triangleLeafE6BarO
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    Module.Dual F (BDiagCoeff n a d) →ₗ[F]
      triangleLeafE6J0 n a b c d :=
  barO
    (triangleLeafBDiagAlpha
      (n := n) (a := a) (b := b) (d := d))
    (triangleLeafE6Obstruction
      (n := n) (a := a) (b := b) (c := c) (d := d))
    (triangleLeafBDiagAlpha_surjective
      (n := n) (a := a) (b := b) (d := d) hb)

theorem triangleLeafE6BarO_apply_alpha
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b)
    (C : CFun4 n a b d) :
    triangleLeafE6BarO
        (n := n) (a := a) (b := b) (c := c) (d := d) hb
        (triangleLeafBDiagAlpha
          (n := n) (a := a) (b := b) (d := d) C) =
      rangeQuotientMap
        (triangleLeafE6Obstruction
          (n := n) (a := a) (b := b) (c := c) (d := d))
        (triangleLeafE6K0 n a b d) C := by
  exact
    barO_apply_alpha
      (triangleLeafBDiagAlpha
        (n := n) (a := a) (b := b) (d := d))
      (triangleLeafE6Obstruction
        (n := n) (a := a) (b := b) (c := c) (d := d))
      (triangleLeafBDiagAlpha_surjective
        (n := n) (a := a) (b := b) (d := d) hb)
      C

theorem triangleLeafE6BarO_surjective
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Surjective
      (triangleLeafE6BarO
        (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  exact
    barO_surjective
      (triangleLeafBDiagAlpha
        (n := n) (a := a) (b := b) (d := d))
      (triangleLeafE6Obstruction
        (n := n) (a := a) (b := b) (c := c) (d := d))
      (triangleLeafBDiagAlpha_surjective
        (n := n) (a := a) (b := b) (d := d) hb)

noncomputable def triangleLeafE6SecondQuotientEquiv
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    (LinearMap.range
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d)) ⧸
        restrictedImage
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d))
          (triangleLeafCCompat n a b c d)) ≃ₗ[F]
      (triangleLeafE6J0 n a b c d ⧸
        Submodule.map
          (triangleLeafE6BarO
            (n := n) (a := a) (b := b) (c := c) (d := d) hb)
          (triangleLeafE6K1 n a b c d)) := by
  let q :=
    triangleLeafQ1BOnlyCoeffAll
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let alpha :=
    triangleLeafBDiagAlpha
      (n := n) (a := a) (b := b) (d := d)
  let rho :=
    triangleLeafBOnlyBDiagDualRestrict
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let O :=
    triangleLeafE6Obstruction
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hcompat :
      triangleLeafCCompat n a b c d = LinearMap.ker O :=
    triangleLeafCCompat_eq_ker_e6Obstruction
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hqMap : q = rho.comp alpha :=
    triangleLeafQ1BOnlyCoeffAll_eq_dualRestrict_comp_alpha
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hqKer :
      LinearMap.ker q = LinearMap.ker (rho.comp alpha) :=
    congrArg LinearMap.ker hqMap
  let eCompat :
      (LinearMap.range q ⧸
          restrictedImage q (triangleLeafCCompat n a b c d)) ≃ₗ[F]
        (LinearMap.range q ⧸
          restrictedImage q (LinearMap.ker O)) :=
    Submodule.quotEquivOfEq _ _
      (congrArg (restrictedImage q) hcompat)
  let eSwap :=
    rangeQuotientSwapEquiv q O
  let eKer :
      (LinearMap.range O ⧸ restrictedImage O (LinearMap.ker q)) ≃ₗ[F]
        (LinearMap.range O ⧸
          restrictedImage O (LinearMap.ker (rho.comp alpha))) :=
    Submodule.quotEquivOfEq _ _
      (congrArg (restrictedImage O) hqKer)
  exact
    ((eCompat.trans eSwap).trans eKer).trans
      (secondQuotientEquiv alpha rho O
        (triangleLeafBDiagAlpha_surjective
          (n := n) (a := a) (b := b) (d := d) hb))

end

end TriangleLeaf
end Core4loop
