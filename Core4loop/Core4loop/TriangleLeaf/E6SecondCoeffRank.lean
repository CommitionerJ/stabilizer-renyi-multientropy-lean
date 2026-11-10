import Core4loop.TriangleLeaf.E6SecondQuotientFinal
import Core4loop.TriangleLeaf.E6FirstCoeffRank

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
# Triangle+leaf E6 second coefficient rank

This file transports the intrinsic denominator in the second quotient to the
range of the compatible coefficient map, then combines the resulting second
defect with the already-proved first defect.  It is a logical-level 5 rank
consequence and contains no residual signed-sum or raw `Delta` claim.
-/

theorem map_restrictedImage_triangleLeafQ1BOnlyCoeffAll_CCompat_eq_range_compat
    {n a b c d : ℕ} [NeZero n] :
    Submodule.map
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d))).subtype
        (restrictedImage
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d))
          (triangleLeafCCompat n a b c d)) =
      LinearMap.range
        (triangleLeafQ1BOnlyCoeffCompat
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [restrictedImage_eq_map, ← Submodule.map_comp]
  change
    Submodule.map
        (triangleLeafQ1BOnlyCoeffAll
          (n := n) (a := a) (b := b) (c := c) (d := d))
        (triangleLeafCCompat n a b c d) =
      LinearMap.range
        (triangleLeafQ1BOnlyCoeffCompat
          (n := n) (a := a) (b := b) (c := c) (d := d))
  exact
    (range_triangleLeafQ1BOnlyCoeffCompat_eq_map
      (n := n) (a := a) (b := b) (c := c) (d := d)).symm

theorem finrank_restrictedImage_triangleLeafQ1BOnlyCoeffAll_CCompat_eq_range_compat
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (restrictedImage
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d))
          (triangleLeafCCompat n a b c d)) =
      Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffCompat
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  rw [←
    map_restrictedImage_triangleLeafQ1BOnlyCoeffAll_CCompat_eq_range_compat
      (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact
    (Submodule.finrank_map_subtype_eq
      (LinearMap.range
        (triangleLeafQ1BOnlyCoeffAll
          (n := n) (a := a) (b := b) (c := c) (d := d)))
      (restrictedImage
        (triangleLeafQ1BOnlyCoeffAll
          (n := n) (a := a) (b := b) (c := c) (d := d))
        (triangleLeafCCompat n a b c d))).symm

theorem finrank_range_triangleLeafQ1BOnlyCoeffCompat_add_secondDefect
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffCompat
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      (n - 1) ^ 2 * (n ^ d - (n - 1)) =
    Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  have hEquiv :=
    (triangleLeafE6SecondCoefficientQuotientEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn ha2 hb2 hc hd).finrank_eq
  rw [finrank_triangleLeafE6ThetaQuotient (n := n) (d := d) hd] at hEquiv
  have hTransport :=
    finrank_restrictedImage_triangleLeafQ1BOnlyCoeffAll_CCompat_eq_range_compat
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hQuotient :=
    Submodule.finrank_quotient_add_finrank
      (restrictedImage
        (triangleLeafQ1BOnlyCoeffAll
          (n := n) (a := a) (b := b) (c := c) (d := d))
        (triangleLeafCCompat n a b c d))
  calc
    Module.finrank F
          (LinearMap.range
            (triangleLeafQ1BOnlyCoeffCompat
              (n := n) (a := a) (b := b) (c := c) (d := d))) +
        (n - 1) ^ 2 * (n ^ d - (n - 1)) =
      Module.finrank F
          (restrictedImage
            (triangleLeafQ1BOnlyCoeffAll
              (n := n) (a := a) (b := b) (c := c) (d := d))
            (triangleLeafCCompat n a b c d)) +
        Module.finrank F
          (LinearMap.range
                (triangleLeafQ1BOnlyCoeffAll
                  (n := n) (a := a) (b := b) (c := c) (d := d)) ⧸
            restrictedImage
              (triangleLeafQ1BOnlyCoeffAll
                (n := n) (a := a) (b := b) (c := c) (d := d))
              (triangleLeafCCompat n a b c d)) :=
        congrArg₂ Nat.add hTransport.symm hEquiv.symm
    _ =
      Module.finrank F
          (LinearMap.range
                (triangleLeafQ1BOnlyCoeffAll
                  (n := n) (a := a) (b := b) (c := c) (d := d)) ⧸
            restrictedImage
              (triangleLeafQ1BOnlyCoeffAll
                (n := n) (a := a) (b := b) (c := c) (d := d))
              (triangleLeafCCompat n a b c d)) +
        Module.finrank F
          (restrictedImage
            (triangleLeafQ1BOnlyCoeffAll
              (n := n) (a := a) (b := b) (c := c) (d := d))
            (triangleLeafCCompat n a b c d)) := Nat.add_comm _ _
    _ =
      Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d))) := hQuotient

theorem finrank_range_triangleLeafQ1BOnlyCoeffCompat_add_twoDefects
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffCompat
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      2 * ((n - 1) ^ 2 * (n ^ d - (n - 1))) =
    Module.finrank F (BDiagCoeff n a d) := by
  calc
    Module.finrank F
          (LinearMap.range
            (triangleLeafQ1BOnlyCoeffCompat
              (n := n) (a := a) (b := b) (c := c) (d := d))) +
        2 * ((n - 1) ^ 2 * (n ^ d - (n - 1))) =
      (Module.finrank F
          (LinearMap.range
            (triangleLeafQ1BOnlyCoeffCompat
              (n := n) (a := a) (b := b) (c := c) (d := d))) +
        (n - 1) ^ 2 * (n ^ d - (n - 1))) +
          (n - 1) ^ 2 * (n ^ d - (n - 1)) := by ring
    _ =
      Module.finrank F
          (LinearMap.range
            (triangleLeafQ1BOnlyCoeffAll
              (n := n) (a := a) (b := b) (c := c) (d := d))) +
        (n - 1) ^ 2 * (n ^ d - (n - 1)) := by
      rw [
        finrank_range_triangleLeafQ1BOnlyCoeffCompat_add_secondDefect
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hn ha2 hb2 hc hd]
    _ = Module.finrank F (BDiagCoeff n a d) :=
      finrank_range_triangleLeafQ1BOnlyCoeffAll_add_firstDefect
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (by omega) hc hd

theorem finrank_range_triangleLeafQ1BOnlyCoeffCompat_add_twoDefects_closed
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffCompat
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      2 * ((n - 1) ^ 2 * (n ^ d - (n - 1))) =
    (n - 1) * n ^ (a + d) := by
  rw [
    finrank_range_triangleLeafQ1BOnlyCoeffCompat_add_twoDefects
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn ha2 hb2 hc hd]
  exact finrank_BDiagCoeff (n := n) (a := a) (d := d) (by omega)

end

end TriangleLeaf
end Core4loop
