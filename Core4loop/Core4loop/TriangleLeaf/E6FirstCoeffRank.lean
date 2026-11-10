import Core4loop.TriangleLeaf.E6CoeffPairingCore
import Core4loop.TriangleLeaf.E6ThetaQuotient

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Transparent first coefficient-rank corollaries for the TriangleLeaf E6 route.
-/

theorem finrank_range_triangleLeafQ1BOnlyCoeffAll_add_firstDefect
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      (n - 1) ^ 2 * (n ^ d - (n - 1)) =
    Module.finrank F (BDiagCoeff n a d) := by
  rw [finrank_range_triangleLeafQ1BOnlyCoeffAll_eq_BDiagMap hb]
  exact
    finrank_range_triangleLeafBOnlyBDiagMap_add_firstDefect hb hc hd

theorem finrank_range_triangleLeafQ1BOnlyCoeffAll_add_firstDefect_closed
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      (n - 1) ^ 2 * (n ^ d - (n - 1)) =
    (n - 1) * n ^ (a + d) := by
  rw [finrank_range_triangleLeafQ1BOnlyCoeffAll_eq_BDiagMap hb]
  exact
    finrank_range_triangleLeafBOnlyBDiagMap_add_firstDefect_closed
      ha hb hc hd

end

end TriangleLeaf
end Core4loop
