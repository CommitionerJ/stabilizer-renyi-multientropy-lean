import Core4loop.TriangleLeaf.E6SharedKernelCore

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
The coefficient equivalence induced by the common source quotient

`CFun4 / ker triangleLeafBDiagAlpha
  = CFun4 / ker triangleLeafE6AlphaShearCoeff`.

The construction uses the two first-isomorphism equivalences and the
coordinate kernel equality from `E6SharedKernelCore`.
-/

noncomputable def triangleLeafE6AlphaToShearEquiv
    {n a b d : ℕ} [NeZero n] (hb : 0 < b) :
    Module.Dual F (BDiagCoeff n a d) ≃ₗ[F]
      BDiagCoeff n a d := by
  let alpha :
      CFun4 n a b d →ₗ[F] Module.Dual F (BDiagCoeff n a d) :=
    triangleLeafBDiagAlpha
      (n := n) (a := a) (b := b) (d := d)
  let eAlpha :
      CFun4 n a b d →ₗ[F] BDiagCoeff n a d :=
    triangleLeafE6AlphaShearCoeff
      (n := n) (a := a) (b := b) (d := d)
  have hAlpha : Function.Surjective alpha :=
    triangleLeafBDiagAlpha_surjective hb
  have hEAlpha : Function.Surjective eAlpha :=
    triangleLeafE6AlphaShearCoeff_surjective hb
  have hKer : LinearMap.ker alpha = LinearMap.ker eAlpha :=
    (ker_triangleLeafE6AlphaShearCoeff_eq_K0
      (n := n) (a := a) (b := b) (d := d)).symm
  exact
    ((LinearMap.quotKerEquivOfSurjective alpha hAlpha).symm.trans
      (Submodule.quotEquivOfEq
        (LinearMap.ker alpha) (LinearMap.ker eAlpha) hKer)).trans
      (LinearMap.quotKerEquivOfSurjective eAlpha hEAlpha)

@[simp]
theorem triangleLeafE6AlphaToShearEquiv_apply_alpha
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (C : CFun4 n a b d) :
    triangleLeafE6AlphaToShearEquiv hb
        (triangleLeafBDiagAlpha C) =
      triangleLeafE6AlphaShearCoeff C := by
  unfold triangleLeafE6AlphaToShearEquiv
  simp only [LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end

end TriangleLeaf
end Core4loop
