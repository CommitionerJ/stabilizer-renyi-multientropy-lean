import Core4loop.TriangleLeaf.ProfileKernelIndexDiffSum
import Core3loop.ProfileKernelSplit

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafScalarBProfileKernelCoord (n a c : ℕ) [NeZero n] :=
  I n → ZVec n c → LeafScalarProfileKernel n a

abbrev LeafScalarCProfileKernelCoord (n a b : ℕ) [NeZero n] :=
  YVec n b → I n → LeafScalarProfileKernel n a

noncomputable def leafScalarBProfileKernelCoordEquivCore3BWodd
    {n a c : ℕ} [NeZero n] :
    LeafScalarBProfileKernelCoord n a c ≃ Core3loop.BWoddBCoefABC a c n where
  toFun K :=
    ⟨fun t z => (K t z).1,
      by
        intro t z
        exact (K t z).2⟩
  invFun B := fun t z =>
    ⟨B.1 t z, B.2 t z⟩
  left_inv K := by
    funext t z
    apply Subtype.ext
    rfl
  right_inv B := by
    apply Subtype.ext
    rfl

noncomputable def leafScalarCProfileKernelCoordEquivCore3CWodd
    {n a b : ℕ} [NeZero n] :
    LeafScalarCProfileKernelCoord n a b ≃ Core3loop.CWoddCCoefABC a b n where
  toFun K :=
    ⟨fun y r => (K y r).1,
      by
        intro y r
        exact (K y r).2⟩
  invFun C := fun y r =>
    ⟨C.1 y r, C.2 y r⟩
  left_inv K := by
    funext y r
    apply Subtype.ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl

theorem leafScalarBProfileKernelCoordEquivCore3BWodd_apply
    {n a c : ℕ} [NeZero n]
    (K : LeafScalarBProfileKernelCoord n a c) (t : I n) (z : ZVec n c) :
    (leafScalarBProfileKernelCoordEquivCore3BWodd
      (n := n) (a := a) (c := c) K).1 t z =
      (K t z).1 := rfl

theorem leafScalarCProfileKernelCoordEquivCore3CWodd_apply
    {n a b : ℕ} [NeZero n]
    (K : LeafScalarCProfileKernelCoord n a b) (y : YVec n b) (r : I n) :
    (leafScalarCProfileKernelCoordEquivCore3CWodd
      (n := n) (a := a) (b := b) K).1 y r =
      (K y r).1 := rfl

noncomputable def leafPassiveScalarBProfileKernelCoordEquivCore3BWodd
    {n a c d : ℕ} [NeZero n] (hd : 0 < d) :
    (PassiveVisibleIndex n d hd → LeafScalarBProfileKernelCoord n a c)
      ≃
    (PassiveVisibleIndex n d hd → Core3loop.BWoddBCoefABC a c n) where
  toFun K := fun ω =>
    leafScalarBProfileKernelCoordEquivCore3BWodd
      (n := n) (a := a) (c := c) (K ω)
  invFun K := fun ω =>
    (leafScalarBProfileKernelCoordEquivCore3BWodd
      (n := n) (a := a) (c := c)).symm (K ω)
  left_inv K := by
    funext ω
    exact
      (leafScalarBProfileKernelCoordEquivCore3BWodd
        (n := n) (a := a) (c := c)).left_inv (K ω)
  right_inv K := by
    funext ω
    exact
      (leafScalarBProfileKernelCoordEquivCore3BWodd
        (n := n) (a := a) (c := c)).right_inv (K ω)

noncomputable def leafPassiveScalarCProfileKernelCoordEquivCore3CWodd
    {n a b d : ℕ} [NeZero n] (hd : 0 < d) :
    (PassiveVisibleIndex n d hd → LeafScalarCProfileKernelCoord n a b)
      ≃
    (PassiveVisibleIndex n d hd → Core3loop.CWoddCCoefABC a b n) where
  toFun K := fun ω =>
    leafScalarCProfileKernelCoordEquivCore3CWodd
      (n := n) (a := a) (b := b) (K ω)
  invFun K := fun ω =>
    (leafScalarCProfileKernelCoordEquivCore3CWodd
      (n := n) (a := a) (b := b)).symm (K ω)
  left_inv K := by
    funext ω
    exact
      (leafScalarCProfileKernelCoordEquivCore3CWodd
        (n := n) (a := a) (b := b)).left_inv (K ω)
  right_inv K := by
    funext ω
    exact
      (leafScalarCProfileKernelCoordEquivCore3CWodd
        (n := n) (a := a) (b := b)).right_inv (K ω)

end

end TriangleLeaf
end Core4loop
