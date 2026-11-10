import Core4loop.CompleteGraph.EvenAllLarge.Definitions

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

attribute [local instance] Fintype.ofFinite

/-! A private finite point-pairing chart for the actual `CFun4` carrier. -/

private noncomputable def cfunLinearEquiv (n b d : Nat) :
    CFun4 n 1 b d ≃ₗ[F]
      (PVec n 1 × YVec n b × I n × WVec n d → F) where
  toEquiv := cFun4Equiv n 1 b d
  map_add' C D := by
    funext u
    rcases u with ⟨p, y, s, w⟩
    rfl
  map_smul' r C := by
    funext u
    rcases u with ⟨p, y, s, w⟩
    rfl

private theorem exists_coeffApply_of_linearMap
    {ι : Type*} [Fintype ι]
    (M : (ι → F) →ₗ[F] F) :
    ∃ c : ι → F, ∀ f : ι → F, coeffApply c f = M f := by
  classical
  let e : ι → ι → F := fun i j => if j = i then 1 else 0
  refine ⟨fun i => M (e i), ?_⟩
  intro f
  have hdecomp : f = ∑ i : ι, f i • e i := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [e]
    · intro i _ hij
      simp [e, hij.symm]
    · simp
  calc
    coeffApply (fun i => M (e i)) f = ∑ i : ι, f i * M (e i) := by
      unfold coeffApply
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    _ = M (∑ i : ι, f i • e i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp [smul_eq_mul]
    _ = M f := by rw [← hdecomp]

private noncomputable def funDotDual
    {ι : Type*} [Fintype ι] :
    (ι → F) →ₗ[F] Module.Dual F (ι → F) where
  toFun c :=
    { toFun := fun f => coeffApply c f
      map_add' := by
        intro f g
        unfold coeffApply
        simp only [Pi.add_apply]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro r f
        unfold coeffApply
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring }
  map_add' c d := by
    apply LinearMap.ext
    intro f
    change (∑ i : ι, f i * (c i + d i)) =
      (∑ i : ι, f i * c i) + ∑ i : ι, f i * d i
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' r c := by
    apply LinearMap.ext
    intro f
    change (∑ i : ι, f i * (r * c i)) = r * ∑ i : ι, f i * c i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring

noncomputable def k4BaseCFunDotDual
    {n b d : Nat} [NeZero n] :
    CFun4 n 1 b d →ₗ[F] Module.Dual F (CFun4 n 1 b d) := by
  let E := cfunLinearEquiv n b d
  exact E.toLinearMap.dualMap.comp
    ((funDotDual
      (ι := PVec n 1 × YVec n b × I n × WVec n d)).comp E.toLinearMap)

@[simp] theorem k4BaseCFunDotDual_apply
    {n b d : Nat} [NeZero n]
    (C T : CFun4 n 1 b d) :
    k4BaseCFunDotDual C T =
      coeffApply (cFun4Equiv n 1 b d C) (cFun4Equiv n 1 b d T) := by
  rfl

theorem k4BaseCFunDotDual_surjective
    {n b d : Nat} [NeZero n] :
    Function.Surjective (k4BaseCFunDotDual (n := n) (b := b) (d := d)) := by
  intro lambda
  let E := cfunLinearEquiv n b d
  let Lflat : Module.Dual F
      (PVec n 1 × YVec n b × I n × WVec n d → F) :=
    lambda.comp E.symm.toLinearMap
  rcases exists_coeffApply_of_linearMap Lflat with ⟨c, hc⟩
  refine ⟨E.symm c, ?_⟩
  apply LinearMap.ext
  intro T
  change coeffApply (E (E.symm c)) (E T) = lambda T
  rw [E.apply_symm_apply, hc]
  rfl

theorem k4BaseCFunDotDual_injective
    {n b d : Nat} [NeZero n] :
    Function.Injective (k4BaseCFunDotDual (n := n) (b := b) (d := d)) := by
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mpr k4BaseCFunDotDual_surjective

noncomputable def k4BaseCFunDotEquiv
    {n b d : Nat} [NeZero n] :
    CFun4 n 1 b d ≃ₗ[F] Module.Dual F (CFun4 n 1 b d) :=
  LinearEquiv.ofBijective k4BaseCFunDotDual
    ⟨k4BaseCFunDotDual_injective, k4BaseCFunDotDual_surjective⟩

noncomputable def k4BaseLambdaRead
    {n b d : Nat} [NeZero n] :
    Module.Dual F (CFun4 n 1 b d) →ₗ[F] CFun4 n 1 b d :=
  (k4BaseCFunDotEquiv (n := n) (b := b) (d := d)).symm.toLinearMap

@[simp] theorem k4BaseLambdaRead_build
    {n b d : Nat} [NeZero n] (C : CFun4 n 1 b d) :
    k4BaseLambdaRead (k4BaseCFunDotDual C) = C :=
  (k4BaseCFunDotEquiv (n := n) (b := b) (d := d)).symm_apply_apply C

@[simp] theorem k4BaseLambdaBuild_read
    {n b d : Nat} [NeZero n]
    (lambda : Module.Dual F (CFun4 n 1 b d)) :
    k4BaseCFunDotDual (k4BaseLambdaRead lambda) = lambda :=
  (k4BaseCFunDotEquiv (n := n) (b := b) (d := d)).apply_symm_apply lambda

/-! The two literal coefficient channels.  Both use the same `C`. -/

def K4SBCoeffEquation
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) : Prop :=
  ∀ B : BFun4 n 1 c d,
    k4BaseCFunDotDual C
        (squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)
          (B, (0 : WFun4 n 1 b c))) =
      k4BWSlice B sigma.1.2

def K4SWCoeffEquation
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) : Prop :=
  ∀ W : WFun4 n 1 b c,
    k4BaseCFunDotDual C
        (squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)
          ((0 : BFun4 n 1 c d), W)) =
      k4BWSlice sigma.1.1 W

theorem k4Base_sdual_iff_SB_and_SW
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    (squareCompat
        (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap
        (k4BaseCFunDotDual C) = k4EvenPGPolarAmbient sigma.1 ↔
      K4SBCoeffEquation sigma C ∧ K4SWCoeffEquation sigma C := by
  constructor
  · intro h
    constructor
    · intro B
      have hB := LinearMap.congr_fun h
        (B, (0 : WFun4 n 1 b c))
      change
        k4BaseCFunDotDual C
            (squareCompat
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              (B, (0 : WFun4 n 1 b c))) =
          k4EvenPSlicePolar sigma.1
            (B, (0 : WFun4 n 1 b c)) at hB
      change
        k4BaseCFunDotDual C
            (squareCompat
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              (B, (0 : WFun4 n 1 b c))) =
          k4BWSlice sigma.1.1 (0 : WFun4 n 1 b c) +
            k4BWSlice B sigma.1.2 at hB
      rw [k4BWSlice_zero_right, zero_add] at hB
      exact hB
    · intro W
      have hW := LinearMap.congr_fun h
        ((0 : BFun4 n 1 c d), W)
      change
        k4BaseCFunDotDual C
            (squareCompat
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              ((0 : BFun4 n 1 c d), W)) =
          k4EvenPSlicePolar sigma.1
            ((0 : BFun4 n 1 c d), W) at hW
      change
        k4BaseCFunDotDual C
            (squareCompat
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              ((0 : BFun4 n 1 c d), W)) =
          k4BWSlice sigma.1.1 W +
            k4BWSlice (0 : BFun4 n 1 c d) sigma.1.2 at hW
      rw [k4BWSlice_zero_left, add_zero] at hW
      exact hW
  · rintro ⟨hB, hW⟩
    apply LinearMap.ext
    intro K
    have hdecomp :
        K = (K.1, (0 : WFun4 n 1 b c)) +
          ((0 : BFun4 n 1 c d), K.2) := by
      apply Prod.ext <;> simp
    change
      k4BaseCFunDotDual C
          (squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d) K) =
        k4EvenPSlicePolar sigma.1 K
    rw [hdecomp, map_add, map_add]
    simp only [k4EvenPSlicePolar, Prod.fst_add, Prod.snd_add,
      zero_add, add_zero]
    rw [hB K.1, hW K.2]
    abel

def K4DACoeffEquation
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) : Prop :=
  ∀ A : AFun4 n b c d,
    k4BaseCFunDotDual C
        (diamondEvenPAConstraint
          (n := n) (a := 1) (b := b) (c := c) (d := d) A) =
      k4EvenPBaseRoot sigma A

theorem k4Base_ddual_iff_DA
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    (diamondEvenPAConstraint
        (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap
        (k4BaseCFunDotDual C) = k4EvenPBaseRoot sigma ↔
      K4DACoeffEquation sigma C := by
  constructor
  · intro h A
    exact LinearMap.congr_fun h A
  · intro h
    apply LinearMap.ext
    exact h

theorem k4Base_multiplier_same_coefficient_iff
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    (sigma, k4BaseCFunDotDual C) ∈
        K4EvenPBaseMultiplierSolution n b c d ↔
      K4DACoeffEquation sigma C ∧
        K4SBCoeffEquation sigma C ∧ K4SWCoeffEquation sigma C := by
  rw [k4EvenPBaseMultiplierSolution_mem_iff]
  simp only [LinearMap.mem_ker.mp sigma.2, true_and]
  rw [k4Base_ddual_iff_DA, k4Base_sdual_iff_SB_and_SW]

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
