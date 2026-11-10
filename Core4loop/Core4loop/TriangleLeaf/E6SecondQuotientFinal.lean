import Core4loop.TriangleLeaf.E6CompatibilityClassCore
import Core4loop.TriangleLeaf.E6S2PConstantCore

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
# Triangle+leaf E6 final second-quotient equivalence

This file composes the intrinsic second-quotient reduction, the vanishing of
the induced `K1` image, and the compatibility-class equivalence.  The result
is a logical-level 5 structural certificate: it contains no numerical rank,
residual signed-sum, raw `Delta`, support, `Gamma`, or catalogue claim.
-/

noncomputable def triangleLeafE6SecondCoefficientQuotientEquiv
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc : 0 < c) (hd : 0 < d) :
    (LinearMap.range
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d)) ⧸
        restrictedImage
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d))
          (triangleLeafCCompat n a b c d)) ≃ₗ[F]
      ((WVec n d → PairCurlSpace n) ⧸
        triangleLeafE6PairCurlHdiff n d) :=
  ((triangleLeafE6SecondQuotientEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (by omega : 0 < b)).trans
      ((Submodule.map
          (triangleLeafE6BarO
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (by omega : 0 < b))
          (triangleLeafE6K1 n a b c d)).quotEquivOfEqBot
        (map_triangleLeafE6BarO_K1_eq_bot
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hn ha2 (by omega : 0 < b) hc hd))).trans
    (triangleLeafE6J0EquivPairCurl
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn hb2 hc hd)

end

end TriangleLeaf
end Core4loop
