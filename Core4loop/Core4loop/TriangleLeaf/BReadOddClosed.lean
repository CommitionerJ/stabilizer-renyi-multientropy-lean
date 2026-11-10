import Core4loop.TriangleLeaf.BReadDualReduction

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def BReadTailMainZ (a b c d n : ℕ) : ℤ :=
  (LeafProfileDimZ a d n - PassiveVisibleDimZ d n) * LeafTailUnitZ b c n

def BReadVisibleTailScaleZ (b c d n : ℕ) : ℤ :=
  PassiveVisibleDimZ d n * LeafTailUnitZ b c n

theorem BReadTailMainZ_add_visible_eq_CompatibleResidualSplitZ
    {a b c d n : ℕ} :
    BReadTailMainZ a b c d n
      + PassiveVisibleDimZ d n * LeafVisibleUnitZ a b c d n
    =
    CompatibleResidualSplitZ a b c d n := by
  unfold BReadTailMainZ CompatibleResidualSplitZ
  ring

theorem BReadVisibleTailScaleZ_add_CompatibleResidualSplitZ
    {a b c d n : ℕ} :
    BReadVisibleTailScaleZ b c d n
      + CompatibleResidualSplitZ a b c d n
    =
    BReadTailMainZ a b c d n
      + PassiveVisibleDimZ d n *
        (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n) := by
  unfold BReadVisibleTailScaleZ BReadTailMainZ CompatibleResidualSplitZ
  ring

end

end TriangleLeaf
end Core4loop
