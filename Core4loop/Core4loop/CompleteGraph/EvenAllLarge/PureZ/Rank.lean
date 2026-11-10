import Core4loop.CompleteGraph.EvenAllLarge.PureZ.Factors

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PureZ

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

attribute [local instance] Fintype.ofFinite

theorem finrank_range_matrixCycleDiff
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (matrixCycleDiff (n := n))) =
      n * (n - 1) := by
  calc
    Module.finrank F
        (LinearMap.range (matrixCycleDiff (n := n))) =
        Module.finrank F
          (LinearMap.range (cycDiff (n := n) (Profile n))) :=
      (LinearEquiv.finrank_eq
        (matrixCycleDiffRangeEquiv (n := n))).symm
    _ = Module.finrank F (ZeroSumProfileM n (Profile n)) := by
      rw [range_cycDiff_eq_ZeroSumProfileM]
    _ = (n - 1) * n := by
      rw [finrank_ZeroSumProfileM, finrank_profile]
    _ = n * (n - 1) := by ring

theorem finrank_range_kappaMatrixCoeff
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (kappaMatrixCoeff (n := n))) =
      n * (n - 1) := by
  calc
    Module.finrank F
        (LinearMap.range (kappaMatrixCoeff (n := n))) =
        Module.finrank F
          (LinearMap.range (matrixCycleDiff (n := n))) :=
      (LinearEquiv.finrank_eq
        (kappaMatrixCoeffRangeEquiv (n := n))).symm
    _ = n * (n - 1) := finrank_range_matrixCycleDiff

theorem finrank_range_kappaMatrixCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (kappaMatrixCross (n := n))) =
      n * (n - 1) := by
  calc
    Module.finrank F
        (LinearMap.range (kappaMatrixCross (n := n))) =
        Module.finrank F
          (LinearMap.range (kappaMatrixCoeff (n := n))) :=
      (LinearEquiv.finrank_eq
        (kappaMatrixCrossRangeEquivCoeff (n := n))).symm
    _ = n * (n - 1) := finrank_range_kappaMatrixCoeff

theorem rank_factorCross
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.range (factorCross (n := n))) =
      (n - 1) * (n ^ 2 + 3 * n) := by
  calc
    Module.finrank F (LinearMap.range (factorCross (n := n))) =
        Module.finrank F
          (LinearMap.range (diamondTailFreeStarCross (n := n)) ×
            (LinearMap.range (kappaMatrixCross (n := n)) ×
              LinearMap.range (kappaMatrixCross (n := n)))) :=
      LinearEquiv.finrank_eq (factorCrossRangeEquiv (n := n))
    _ = n * (n - 1) * (n + 1) +
          (n * (n - 1) + n * (n - 1)) := by
      rw [Module.finrank_prod, Module.finrank_prod,
        rank_diamondTailFreeStarCross,
        finrank_range_kappaMatrixCross]
    _ = (n - 1) * (n ^ 2 + 3 * n) := by
      obtain ⟨m, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      ring

theorem rank_localCross
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.range (localCross (n := n))) =
      (n - 1) * (n ^ 2 + 3 * n) := by
  calc
    Module.finrank F (LinearMap.range (localCross (n := n))) =
        Module.finrank F (LinearMap.range (factorCross (n := n))) :=
      LinearEquiv.finrank_eq
        (localCrossRangeEquivFactorCross (n := n))
    _ = (n - 1) * (n ^ 2 + 3 * n) := rank_factorCross

theorem range_tailCross_eq_amplify
    {n c : Nat} [NeZero n] :
    LinearMap.range (tailCross (n := n) (c := c)) =
      LinearMap.range
        (diamondTailAmplify (n := n) (k := c)
          (localCross (n := n))) := by
  rw [tailCross]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr
      (localTailEquiv (n := n) (c := c)).surjective)

theorem rank_tailCross
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    Module.finrank F
        (LinearMap.range (tailCross (n := n) (c := c))) =
      (n ^ (c - 1) - 2) *
        ((n - 1) * (n ^ 2 + 3 * n)) := by
  rw [range_tailCross_eq_amplify,
    finrank_range_diamondTailAmplify hn2 hn hc2,
    finrank_diamondEvenAxisTailZero hn2 hn hc2,
    rank_localCross]

private noncomputable def rangeCompEquivOfInjectiveMonoid
    {U V W : Type*}
    [AddCommMonoid U] [Module F U]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (f : U →ₗ[F] V) (g : V →ₗ[F] W)
    (hg : Function.Injective g) :
    LinearMap.range f ≃ₗ[F] LinearMap.range (g.comp f) := by
  let hres :
      LinearMap.range f →ₗ[F] LinearMap.range (g.comp f) :=
    { toFun := fun x =>
        ⟨g x.1, by
          rcases x.2 with ⟨u, hu⟩
          exact ⟨u, congrArg g hu⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add g _ _
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact map_smul g _ _ }
  apply LinearEquiv.ofBijective hres
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact hg (congrArg Subtype.val hxy)
  · intro y
    rcases y.2 with ⟨u, hu⟩
    refine ⟨⟨f u, LinearMap.mem_range_self f u⟩, ?_⟩
    apply Subtype.ext
    exact hu

theorem finrank_range_descendedCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (descendedCross hn2 hn hb2 hc2 hd2)) =
      (n ^ (c - 1) - 2) *
        ((n - 1) * (n ^ 2 + 3 * n)) := by
  rw [descendedCross_eq_rightRead_dual_tailCross]
  let f : K4BaseMixedZSector n c →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n c
          (DiamondEEOERightAmbient n)) :=
    tailCross (n := n) (c := c)
  let g : Module.Dual F
        (DiamondEvenAxisValueTailZero n c
          (DiamondEEOERightAmbient n)) →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
    (rightRead hn hb2 hc2 hd2).dualMap
  let E :=
    rangeCompEquivOfInjectiveMonoid f g
      (LinearMap.dualMap_injective_of_surjective
        (rightRead_surjective hn hb2 hc2 hd2))
  change Module.finrank F (LinearMap.range (g.comp f)) = _
  exact (LinearEquiv.finrank_eq E).symm.trans
    (rank_tailCross hn2 hn hc2)

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PureZ
