import Core4loop.TriangleLeaf.TotalQCdLinear
import Core4loop.TriangleLeaf.DiffProfileFamilyCoeffZero

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem qLeafProfileKernelTotalCdExplicitLinearMap_eq_zero_iff_forall
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCdExplicitLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0
      ↔
      ∀ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
        qLeafProfileKernelTotalCdExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB kCd = 0 := by
  constructor
  · intro hL kCd
    rw [← qLeafProfileKernelTotalCdExplicitLinearMap_apply
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCd]
    rw [hL]
    rfl
  · intro hzero
    apply LinearMap.ext
    intro kCd
    rw [qLeafProfileKernelTotalCdExplicitLinearMap_apply
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCd]
    exact hzero kCd

end

end TriangleLeaf
end Core4loop
