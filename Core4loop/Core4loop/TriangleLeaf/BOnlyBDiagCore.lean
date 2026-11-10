import Core4loop.TriangleLeaf.CompatibleSourceCore
import Core4loop.BDiag

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable def triangleLeafBOnlyBDiagMap
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafBOnly n a b c d →ₗ[F] BDiagCoeff n a d where
  toFun Y :=
    BDiagOfBLinear
      (n := n) (a := a) (c := c) (d := d) Y.1.1.1
  map_add' Y Z := by
    exact (BDiagOfBLinear
      (n := n) (a := a) (c := c) (d := d)).map_add Y.1.1.1 Z.1.1.1
  map_smul' r Y := by
    exact (BDiagOfBLinear
      (n := n) (a := a) (c := c) (d := d)).map_smul r Y.1.1.1

@[simp]
theorem triangleLeafBOnlyBDiagMap_apply
    {n a b c d : ℕ} [NeZero n]
    (Y : triangleLeafBOnly n a b c d) :
    triangleLeafBOnlyBDiagMap
        (n := n) (a := a) (b := b) (c := c) (d := d) Y =
      BDiagOfB
        (n := n) (a := a) (c := c) (d := d) Y.1.1.1 :=
  rfl

end

end TriangleLeaf
end Core4loop
