import Core4loop.CompleteGraph.Odd.ConstrainedCurl

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.Odd

open Core4loop
open Core4loop.CompleteGraph.ScalarCycle
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

private theorem ssts_kernel_gives_J_coeff
    {n c : Nat} [NeZero n] (hn : Odd n)
    (u : DiamondOddAxisTail n c → DiamondEOOOLeftAmbient n)
    (hu : u ∈ LinearMap.ker (diamondOddSSTSCross hn))
    (t : DiamondOddAxisTail n c) :
    diamondEOOOCoeffMap
        (diamondOddAxisTailJ (DiamondEOOOLeftAmbient n) u t) = 0 := by
  have hfamily :
      diamondOddAxisTailJ (DiamondEOOOLeftAmbient n) u ∈
        LinearMap.ker
          (diamondOddFamilyCross
            (T := DiamondOddAxisTail n c)
            (diamondTailFreeStarCross (n := n))) := by
    rw [LinearMap.mem_ker] at hu ⊢
    exact hu
  have ht :=
    (diamondOddFamilyCross_mem_ker_iff
      (T := DiamondOddAxisTail n c)
      (diamondTailFreeStarCross (n := n))
      (diamondOddAxisTailJ (DiamondEOOOLeftAmbient n) u)).mp
        hfamily t
  rw [LinearMap.mem_ker] at ht
  apply EEOEInternal.cubeDotDual_injective
  simpa [diamondTailFreeStarCross] using ht

private theorem ssts_kernel_gives_coeff
    {n c : Nat} [NeZero n] (hn : Odd n)
    (u : DiamondOddAxisTail n c → DiamondEOOOLeftAmbient n)
    (hu : u ∈ LinearMap.ker (diamondOddSSTSCross hn))
    (t : DiamondOddAxisTail n c) :
    diamondEOOOCoeffMap (u t) = 0 := by
  have hsq :=
    diamondOddAxisTailJ_sq_apply
      (DiamondEOOOLeftAmbient n) hn u
  have hsum :
      diamondEOOOCoeffMap
        (∑ s, diamondOddAxisTailJ
          (DiamondEOOOLeftAmbient n) u s) = 0 := by
    classical
    have hfinite :
        ∀ S : Finset (DiamondOddAxisTail n c),
          diamondEOOOCoeffMap
            (∑ s ∈ S,
              diamondOddAxisTailJ
                (DiamondEOOOLeftAmbient n) u s) = 0 := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
          exact (diamondEOOOCoeffMap (n := n)).map_zero
      | @insert s S hs hS =>
          rw [Finset.sum_insert hs]
          rw [(diamondEOOOCoeffMap (n := n)).map_add]
          rw [ssts_kernel_gives_J_coeff hn u hu s, hS, add_zero]
    simpa using hfinite Finset.univ
  rw [← congrFun hsq t]
  rw [diamondOddAxisTailJ_apply]
  rw [(diamondEOOOCoeffMap (n := n)).map_add]
  rw [ssts_kernel_gives_J_coeff hn u hu t, hsum, add_zero]

private theorem coeff_zero_gives_closure
    {n : Nat} [NeZero n]
    (B W : CyclicCube n)
    (h : diamondEOOOCoeffMap (B, W) = 0) :
    k4Closure B 0 W := by
  intro x y z
  have hp := congrFun (congrFun (congrFun h x) y) z
  simp only [diamondEOOOCoeffMap, LinearMap.coprod_apply,
    Pi.add_apply, Pi.zero_apply, EEOEInternal.cubeDiffI_apply,
    EEOEInternal.cubeDiffK_apply] at hp
  simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ,
    Pi.zero_apply, add_zero]
  exact hp

private theorem k4CubeKappa_zero_of_closure
    {n : Nat} [NeZero n] (hn2 : 2 <= n)
    (B W : CyclicCube n)
    (hcl : k4Closure B 0 W) :
    k4CubeKappa B W = 0 := by
  rw [k4CubeKappa_eq_cycleQ_zeroC_of_closure B W hcl]
  exact cycleQ_zero_of_closure hn2 B 0 W hcl

theorem k4OddSSTS_addedPhase_zero_on_crossKernel
    {n c : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Odd n)
    (u :
      DiamondOddAxisTail n c →
        DiamondEOOOLeftAmbient n)
    (hu :
      u ∈ LinearMap.ker
        (diamondOddSSTSCross (c := c) hn)) :
    (∑ t : DiamondOddAxisTail n c,
      k4CubeKappa
        (u t).1
        (diamondOddAxisTailJ
          (CyclicCube n)
          (fun s => (u s).2) t)) = 0 := by
  let B : DiamondOddAxisTail n c → CyclicCube n :=
    fun t => (u t).1
  let W : DiamondOddAxisTail n c → CyclicCube n :=
    fun t => (u t).2
  have hcoeff :
      ∀ t : DiamondOddAxisTail n c,
        diamondEOOOCoeffMap (B t, W t) = 0 := by
    intro t
    exact ssts_kernel_gives_coeff hn u hu t
  have hpoint :
      ∀ t : DiamondOddAxisTail n c,
        k4Closure (B t) 0 (W t) := by
    intro t
    exact coeff_zero_gives_closure (B t) (W t) (hcoeff t)
  have hsumCoeff :
      diamondEOOOCoeffMap
        ((∑ t, B t), (∑ t, W t)) = 0 := by
    change
      cubeDiffI (∑ t, B t) + cubeDiffK (∑ t, W t) = 0
    rw [map_sum, map_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro t _
    simpa only [diamondEOOOCoeffMap, LinearMap.coprod_apply]
      using hcoeff t
  have hsum :
      k4Closure (∑ t, B t) 0 (∑ t, W t) :=
    coeff_zero_gives_closure
      (∑ t, B t) (∑ t, W t) hsumCoeff
  have hpointKappa :
      ∀ t : DiamondOddAxisTail n c,
        k4CubeKappa (B t) (W t) = 0 := by
    intro t
    exact k4CubeKappa_zero_of_closure hn2
      (B t) (W t) (hpoint t)
  change
    (∑ t : DiamondOddAxisTail n c,
      k4CubeKappa (B t)
        (diamondOddAxisTailJ (CyclicCube n) W t)) = 0
  simp_rw [diamondOddAxisTailJ_apply, k4CubeKappa_add_right]
  rw [Finset.sum_add_distrib]
  have hleft : (∑ t, k4CubeKappa (B t) (W t)) = 0 :=
    Finset.sum_eq_zero (fun t _ => hpointKappa t)
  rw [hleft, zero_add]
  calc
    (∑ t, k4CubeKappa (B t) (∑ s, W s)) =
        k4CubeKappa (∑ t, B t) (∑ s, W s) :=
      (map_sum (k4CubeKappaLeftAddHom (∑ s, W s))
        B Finset.univ).symm
    _ = 0 := k4CubeKappa_zero_of_closure hn2
      (∑ t, B t) (∑ s, W s) hsum


end

end Core4loop.CompleteGraph.Odd
