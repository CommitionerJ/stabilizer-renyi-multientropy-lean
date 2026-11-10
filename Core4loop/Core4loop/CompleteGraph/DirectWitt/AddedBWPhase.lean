import Core4loop.CompleteGraph.PreC.DiamondReuse
import Core4loop.SquareDiagonal.EvenP.SourceSplit

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop

attribute [local instance] Fintype.ofFinite

noncomputable def k4BWSlice
    {n b c d : Nat} [NeZero n]
    (B : BFun4 n 1 c d) (W : WFun4 n 1 b c) : F :=
  ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
    (betaB B (zeroVec : PVec n 1) y z w *
        xiW W (zeroVec : PVec n 1) y z w
      + gammaB B (zeroVec : PVec n 1) y z w *
        zetaW W (zeroVec : PVec n 1) y z w)

theorem k4BWSlice_zero_left
    {n b c d : Nat} [NeZero n]
    (W : WFun4 n 1 b c) :
    k4BWSlice (0 : BFun4 n 1 c d) W = 0 := by
  classical
  simp [k4BWSlice, betaB, gammaB]

theorem k4BWSlice_zero_right
    {n b c d : Nat} [NeZero n]
    (B : BFun4 n 1 c d) :
    k4BWSlice B (0 : WFun4 n 1 b c) = 0 := by
  classical
  simp [k4BWSlice, xiW, zetaW]

theorem k4BWSlice_add_left
    {n b c d : Nat} [NeZero n]
    (B₁ B₂ : BFun4 n 1 c d) (W : WFun4 n 1 b c) :
    k4BWSlice (B₁ + B₂) W =
      k4BWSlice B₁ W + k4BWSlice B₂ W := by
  classical
  simp only [k4BWSlice, betaB, gammaB, Pi.add_apply]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem k4BWSlice_add_right
    {n b c d : Nat} [NeZero n]
    (B : BFun4 n 1 c d) (W₁ W₂ : WFun4 n 1 b c) :
    k4BWSlice B (W₁ + W₂) =
      k4BWSlice B W₁ + k4BWSlice B W₂ := by
  classical
  simp only [k4BWSlice, xiW, zetaW, Pi.add_apply]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem k4BWPhaseClean_eq_sum_slices
    {n a b c d : Nat} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    k4BWPhaseClean B W =
      ∑ p : PVec n a,
        k4BWSlice
          ((SquareDiagonal.EvenP.diamondEvenPBWCurryEquiv (B, W) p).1)
          ((SquareDiagonal.EvenP.diamondEvenPBWCurryEquiv (B, W) p).2) := by
  rfl

end Core4loop
