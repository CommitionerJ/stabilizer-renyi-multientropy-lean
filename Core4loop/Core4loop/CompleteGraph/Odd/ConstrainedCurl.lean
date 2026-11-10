import Core4loop.CompleteGraph.CubeCompat.KappaCycle
import Core4loop.SquareDiagonal.DirectWitt.OddChannelProduct

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.Odd

open Core4loop
open Core4loop.CompleteGraph.CubeCompat
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.DirectWitt

noncomputable section

attribute [local instance] Fintype.ofFinite

private theorem k4CubeKappa_zero_left
    {n : Nat} [NeZero n] (W : CyclicCube n) :
    k4CubeKappa (0 : CyclicCube n) W = 0 := by
  simp [k4CubeKappa]

private theorem k4CubeKappa_add_left
    {n : Nat} [NeZero n]
    (B₁ B₂ W : CyclicCube n) :
    k4CubeKappa (B₁ + B₂) W =
      k4CubeKappa B₁ W + k4CubeKappa B₂ W := by
  unfold k4CubeKappa
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Pi.add_apply]
  ring

private theorem k4CubeKappa_add_right
    {n : Nat} [NeZero n]
    (B W₁ W₂ : CyclicCube n) :
    k4CubeKappa B (W₁ + W₂) =
      k4CubeKappa B W₁ + k4CubeKappa B W₂ := by
  unfold k4CubeKappa
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Pi.add_apply]
  ring

private noncomputable def k4CubeKappaLeftAddHom
    {n : Nat} [NeZero n] (W : CyclicCube n) :
    CyclicCube n →+ F where
  toFun B := k4CubeKappa B W
  map_zero' := k4CubeKappa_zero_left W
  map_add' B₁ B₂ := k4CubeKappa_add_left B₁ B₂ W

theorem k4OddTSSS_addedPhase_zero
    {n a : Nat} [NeZero n] (hn2 : 2 <= n)
    (x : DiamondOddTSSSSource n a) :
    (∑ pt : DiamondOddAxisTail n a,
      k4CubeKappa (x.1 pt).1
        (diamondOddAxisTailJ (CyclicCube n)
          (fun pt' => (x.1 pt').2) pt)) = 0 := by
  let B : DiamondOddAxisTail n a → CyclicCube n :=
    fun pt => (x.1 pt).1
  let W : DiamondOddAxisTail n a → CyclicCube n :=
    fun pt => (x.1 pt).2
  have hsource :
      ∀ pt : DiamondOddAxisTail n a,
        cubeDiffP (B pt) + cubeDiffR (W pt) = 0 := by
    intro pt
    have hker := LinearMap.mem_ker.mp x.2
    have hpt := congrFun hker pt
    simpa only [diamondOddTSSSSourceMap_apply] using hpt
  have hpoint :
      ∀ pt : DiamondOddAxisTail n a,
        k4CubeKappa (B pt) (W pt) = 0 := by
    intro pt
    exact k4CubeKappa_zero_of_compat hn2 (B pt) (W pt)
      (hsource pt)
  have hsumSource :
      cubeDiffP (∑ pt, B pt) + cubeDiffR (∑ pt, W pt) = 0 := by
    rw [map_sum, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun pt _ => hsource pt)
  change
    (∑ pt : DiamondOddAxisTail n a,
      k4CubeKappa (B pt)
        (diamondOddAxisTailJ (CyclicCube n) W pt)) = 0
  simp_rw [diamondOddAxisTailJ_apply, k4CubeKappa_add_right]
  rw [Finset.sum_add_distrib]
  have hleft : (∑ pt, k4CubeKappa (B pt) (W pt)) = 0 :=
    Finset.sum_eq_zero (fun pt _ => hpoint pt)
  rw [hleft, zero_add]
  calc
    (∑ pt, k4CubeKappa (B pt) (∑ pt, W pt)) =
        k4CubeKappa (∑ pt, B pt) (∑ pt, W pt) :=
      (map_sum (k4CubeKappaLeftAddHom (∑ pt, W pt))
        B Finset.univ).symm
    _ = 0 := k4CubeKappa_zero_of_compat hn2
      (∑ pt, B pt) (∑ pt, W pt) hsumSource

end

end Core4loop.CompleteGraph.Odd
