import Core4loop.TriangleLeaf.E6SelfDual
import Core4loop.TriangleLeaf.E6ResidualRank
import Core4loop.QuadraticSignSum

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem leafCompatibleResidualSum_even_large_eq_pow_finrank
    {n a b c d : ℕ} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    leafCompatibleResidualSum n a b c d =
      (2 : ℤ) ^ Module.finrank F (triangleLeafE5LB n a b c d) := by
  letI : Fintype (triangleLeafE5LB n a b c d) :=
    Fintype.ofFinite _
  rw [leafCompatibleResidualSum_eq_compatibleSubmoduleSignSum]
  exact
    sum_bitSign_eq_pow_finrank_of_selfDual_isotropic
      (q := triangleLeafCompatibleQ)
      (polar := triangleLeafCompatiblePolar)
      (hq_add := triangleLeafCompatibleQ_add)
      (L := triangleLeafE5LB n a b c d)
      (hq_zero :=
        triangleLeafE5LB_q_zero_even_large hn2 hn ha2 hb2 hc2 hd2)
      (hself :=
        triangleLeafE5LB_selfDual_even_large hn2 hn ha2 hb2 hc2 hd2)

theorem leafCompatibleResidualSum_even_large
    {n a b c d : ℕ} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    leafCompatibleResidualSum n a b c d =
      (2 : ℤ) ^
        Int.toNat (CompatibleResidualSplitZ a b c d n) := by
  rw [leafCompatibleResidualSum_even_large_eq_pow_finrank
    hn2 hn ha2 hb2 hc2 hd2]
  rw [toNat_CompatibleResidualSplitZ_eq_finrank_triangleLeafE5LB_even_large
    hn ha2 hb2 hc2 (by omega)]

end

end TriangleLeaf
end Core4loop
