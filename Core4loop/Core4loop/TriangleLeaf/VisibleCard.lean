import Core4loop.TriangleLeaf.VisibleCoordinates
import Core3loop.VisibleSpace

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private theorem core3_sumY_eq_vecSum {n b : ℕ} [NeZero n] (y : YVec n b) :
    Core3loop.sumY (b := b) (n := n) y = vecSum y := by
  rfl

private theorem core3_sumZ_eq_vecSum {n c : ℕ} [NeZero n] (z : ZVec n c) :
    Core3loop.sumZ (c := c) (n := n) z = vecSum z := by
  rfl

noncomputable def leafScalarVisibleKernelEquivCore3
    {n b c : ℕ} [NeZero n] :
    LeafScalarVisibleKernel n b c ≃ Core3loop.ScalarVisibleCompat b c n where
  toFun X :=
    { bcoef := X.1.1
      ccoef := X.1.2
      compat := by
        intro y z
        have hX := congrFun (congrFun (LinearMap.mem_ker.mp X.2) y) z
        exact hX }
  invFun X :=
    ⟨(X.bcoef, X.ccoef), by
      rw [LinearMap.mem_ker]
      funext y z
      have hX := X.compat y z
      exact hX⟩
  left_inv X := by
    apply Subtype.ext
    rfl
  right_inv X := by
    apply Core3loop.ScalarVisibleCompat.ext
    · rfl
    · rfl

noncomputable instance instFintypeLeafScalarVisibleKernel {n b c : ℕ} [NeZero n] :
    Fintype (LeafScalarVisibleKernel n b c) := by
  classical
  exact Fintype.ofEquiv (Core3loop.ScalarVisibleCompat b c n)
    (leafScalarVisibleKernelEquivCore3 (n := n) (b := b) (c := c)).symm

theorem card_LeafScalarVisibleKernel {n b c : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (LeafScalarVisibleKernel n b c) =
      2 ^ (n ^ b + n ^ c + (n - 1) ^ 2) := by
  rw [Fintype.card_congr
    (leafScalarVisibleKernelEquivCore3 (n := n) (b := b) (c := c))]
  exact Core3loop.card_scalarVisibleSpace_closed (b := b) (c := c) (n := n) hb hc

theorem card_LeafVisibleKernel {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Fintype.card (LeafVisibleKernel n b c d) =
      (2 ^ (n ^ b + n ^ c + (n - 1) ^ 2)) ^ (n ^ d - (n - 1)) := by
  classical
  rw [Fintype.card_congr
    (leafVisibleKernelEquivCoord (n := n) (b := b) (c := c) (d := d) hd)]
  rw [Fintype.card_fun,
    card_LeafScalarVisibleKernel (n := n) (b := b) (c := c) hb hc,
    card_PassiveVisibleIndex (n := n) (d := d) hd]

end

end TriangleLeaf
end Core4loop
