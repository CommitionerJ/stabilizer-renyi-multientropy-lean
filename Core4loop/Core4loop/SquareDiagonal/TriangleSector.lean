import Core4loop.TriangleCore.Closed
import Core4loop.SquareDiagonal.SupportTable

namespace Core4loop
namespace SquareDiagonal

noncomputable def triangleSectorContributionZ
    (r s t passive n : ℕ) : ℤ :=
  SectorExpZ r s t passive n

theorem triangle_core_closed_for_sector
    {n r s t : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    TriangleCore.DeltaTriangleCore r s t n =
      (2 : ℤ) ^ Int.toNat (XtriangleZ r s t n) :=
  TriangleCore.DeltaTriangleCore_closed
    (r := r) (s := s) (t := t) (n := n) hr hs ht

theorem triangle_sector_eval
    {n r s t passive : ℕ} [NeZero n]
    (_hn : 2 ≤ n) (_hr : 0 < r) (_hs : 0 < s) (_ht : 0 < t) :
    triangleSectorContributionZ r s t passive n = SectorExpZ r s t passive n := by
  rfl

end SquareDiagonal
end Core4loop
