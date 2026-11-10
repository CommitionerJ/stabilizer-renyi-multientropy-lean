import Core4loop.TriangleLeaf.ProfileFibers
import Core4loop.TriangleLeaf.CompatibleSourceCore

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Gate C1, Round 1: the exact compatible source and the one-sided orthogonal
certificate for the `b = 1` TriangleLeaf E5 branch.
-/

noncomputable def triangleLeafCompatibleEquiv
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafCompatibleSubmodule n a b c d ≃
      LeafCompatibleBC n a b c d where
  toFun X :=
    ⟨X.1,
      (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) X.1).mp X.2⟩
  invFun X :=
    ⟨X.1,
      (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) X.1).mpr X.2⟩
  left_inv X := by ext <;> rfl
  right_inv X := by ext <;> rfl

theorem leafCompatibleResidualSum_eq_compatibleSubmoduleSignSum
    {n a b c d : ℕ} [NeZero n] :
    leafCompatibleResidualSum n a b c d =
      ∑ X : triangleLeafCompatibleSubmodule n a b c d,
        bitSign (Q1 X.1.1 X.1.2) := by
  classical
  rw [leafCompatibleResidualSum_eq_subtypeSignSum]
  unfold leafCompatibleSubtypeSignSum
  simpa [triangleLeafCompatibleEquiv] using
    ((triangleLeafCompatibleEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d)).sum_comp
        (fun X => bitSign (Q1 X.1.1 X.1.2))).symm

noncomputable def triangleLeafCompatibleQ
    {n a b c d : ℕ} [NeZero n]
    (X : triangleLeafCompatibleSubmodule n a b c d) : F :=
  Q1 X.1.1 X.1.2


end

end TriangleLeaf
end Core4loop
