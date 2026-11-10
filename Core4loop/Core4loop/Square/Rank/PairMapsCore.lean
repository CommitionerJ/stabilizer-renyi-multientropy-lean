import Core4loop.Square.CompatCore
import Core4loop.RootSpaces.KRange

namespace Core4loop

noncomputable def SquareBInclusion {n a b c d : ℕ} [NeZero n] :
    BFun4 n a c d →ₗ[F] BFun4 n a c d × WFun4 n a b c where
  toFun B := (B, 0)
  map_add' B B' := by
    ext <;> rfl
  map_smul' r B := by
    ext <;> rfl

noncomputable def SquareWInclusion {n a b c d : ℕ} [NeZero n] :
    WFun4 n a b c →ₗ[F] BFun4 n a c d × WFun4 n a b c where
  toFun W := (0, W)
  map_add' W W' := by
    ext <;> rfl
  map_smul' r W := by
    ext <;> rfl

noncomputable def SquareBMap {n a b c d : ℕ} [NeZero n] :
    BFun4 n a c d →ₗ[F] (RootTarget n b c d × CFun4 n a b d) :=
  LinearMap.prod
    (KBMap (n := n) (a := a) (b := b) (c := c) (d := d))
    ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))

noncomputable def SquareWMap {n a b c d : ℕ} [NeZero n] :
    WFun4 n a b c →ₗ[F] (RootTarget n b c d × CFun4 n a b d) :=
  LinearMap.prod
    (KWMap (n := n) (a := a) (b := b) (c := c) (d := d))
    ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))

end Core4loop
