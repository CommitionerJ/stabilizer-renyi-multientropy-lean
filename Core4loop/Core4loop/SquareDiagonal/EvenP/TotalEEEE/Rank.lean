import Core4loop.SquareDiagonal.EvenP.TotalEEEE.BlockAlignment
import Core4loop.SquareDiagonal.EvenP.EEEEIsolated

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 4000000
set_option maxSynthPendingDepth 2048

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEEEERankInternal

section RankComponents

theorem jKernel_j_const
    {n : Nat} [NeZero n]
    (q : T37RightP1.T37JKernel n)
    (i j k : I n) :
    q.1 i j k = q.1 i 0 k := by
  have hzero :
      cubeDiffJInv q.1 = 0 :=
    LinearMap.mem_ker.mp q.2
  have hstep :
      ∀ s : I n, q.1 i (s + 1) k = q.1 i s k := by
    intro s
    have hs :=
      congrFun (congrFun (congrFun hzero i) (s + 1)) k
    simp only [Pi.zero_apply] at hs
    rw [EEOEInternal.cubeDiffJInv_apply] at hs
    rw [show (s + 1) - 1 = s by abel] at hs
    exact EEOEInternal.eq_of_add_eq_zero hs
  exact zmod_step_const (fun s => q.1 i s k) hstep j

noncomputable def jKernelRead
    {n : Nat} [NeZero n] :
    T37RightP1.T37JKernel n →ₗ[F] MatrixProfile n where
  toFun q := fun i k => q.1 i 0 k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def jKernelBuild
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] T37RightP1.T37JKernel n where
  toFun M :=
    ⟨fun i _j k => M i k, by
      apply LinearMap.mem_ker.mpr
      funext i j k
      rw [EEOEInternal.cubeDiffJInv_apply]
      exact F_add_self _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def jKernelEquivMatrix
    {n : Nat} [NeZero n] :
    T37RightP1.T37JKernel n ≃ₗ[F] MatrixProfile n where
  toFun := jKernelRead
  invFun := jKernelBuild
  left_inv q := by
    apply Subtype.ext
    funext i j k
    exact (jKernel_j_const q i j k).symm
  right_inv _ := rfl
  map_add' := map_add jKernelRead
  map_smul' := map_smul jKernelRead

theorem finrank_jKernel
    {n : Nat} [NeZero n] :
    Module.finrank F (T37RightP1.T37JKernel n) = n ^ 2 := by
  rw [LinearEquiv.finrank_eq (jKernelEquivMatrix (n := n))]
  simp [MatrixProfile, Module.finrank_pi_fintype, I, ZMod.card,
    pow_two]

/-- The flipped `i`-difference on the exact `J`-kernel carrier. -/
noncomputable def jKernelIDiff
    {n : Nat} [NeZero n] :
    T37RightP1.T37JKernel n →ₗ[F] CyclicCube n where
  toFun q := fun i j k => q.1 i j k + q.1 (i - 1) j k
  map_add' q q' := by
    funext i j k
    simp only [Submodule.coe_add, Pi.add_apply]
    abel
  map_smul' r q := by
    funext i j k
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem iDiffKernel_i_const
    {n : Nat} [NeZero n]
    (q : LinearMap.ker (jKernelIDiff (n := n)))
    (i j k : I n) :
    q.1.1 i j k = q.1.1 0 j k := by
  have hzero : jKernelIDiff q.1 = 0 :=
    LinearMap.mem_ker.mp q.2
  have hstep :
      ∀ s : I n, q.1.1 (s + 1) j k = q.1.1 s j k := by
    intro s
    have hs :=
      congrFun (congrFun (congrFun hzero (s + 1)) j) k
    simp only [Pi.zero_apply] at hs
    change
      q.1.1 (s + 1) j k +
          q.1.1 ((s + 1) - 1) j k = 0 at hs
    rw [show (s + 1) - 1 = s by abel] at hs
    exact EEOEInternal.eq_of_add_eq_zero hs
  exact zmod_step_const (fun s => q.1.1 s j k) hstep i

noncomputable def iDiffKernelRead
    {n : Nat} [NeZero n] :
    LinearMap.ker (jKernelIDiff (n := n)) →ₗ[F] Profile n where
  toFun q := fun k => q.1.1 0 0 k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def iDiffKernelBuild
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] LinearMap.ker (jKernelIDiff (n := n)) where
  toFun h :=
    ⟨jKernelBuild (fun _i k => h k), by
      apply LinearMap.mem_ker.mpr
      funext i j k
      change h k + h k = 0
      exact F_add_self _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def iDiffKernelEquivProfile
    {n : Nat} [NeZero n] :
    LinearMap.ker (jKernelIDiff (n := n)) ≃ₗ[F] Profile n where
  toFun := iDiffKernelRead
  invFun := iDiffKernelBuild
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j k
    calc
      q.1.1 0 0 k = q.1.1 0 j k :=
        (jKernel_j_const q.1 0 j k).symm
      _ = q.1.1 i j k :=
        (iDiffKernel_i_const q i j k).symm
  right_inv _ := rfl
  map_add' := map_add iDiffKernelRead
  map_smul' := map_smul iDiffKernelRead

theorem finrank_ker_jKernelIDiff
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.ker (jKernelIDiff (n := n))) = n := by
  rw [LinearEquiv.finrank_eq
    (iDiffKernelEquivProfile (n := n))]
  exact finrank_profile

theorem rank_jKernelIDiff
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (jKernelIDiff (n := n))) =
      n * (n - 1) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (jKernelIDiff (n := n))
  rw [finrank_ker_jKernelIDiff, finrank_jKernel] at hnull
  have hn : 0 < n := NeZero.pos n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring_nf at hnull ⊢
  omega

theorem cubeDiffI_pairing_jKernelIDiff
    {n : Nat} [NeZero n]
    (x : CyclicCube n) (q : T37RightP1.T37JKernel n) :
    cubeDot (cubeDiffI x) q.1 =
      cubeDot x (jKernelIDiff q) := by
  have hshift :
      (∑ z : I n × I n × I n,
          x (z.1 + 1) z.2.1 z.2.2 *
            q.1 z.1 z.2.1 z.2.2) =
        ∑ z : I n × I n × I n,
          x z.1 z.2.1 z.2.2 *
            q.1 (z.1 - 1) z.2.1 z.2.2 := by
    let e :=
      Equiv.prodCongr (Equiv.addRight (1 : I n))
        (Equiv.refl (I n × I n))
    apply Fintype.sum_equiv e
    intro z
    simp [e]
  simp only [cubeDot, EEOEInternal.cubeDiffI_apply,
    jKernelIDiff, LinearMap.coe_mk, AddHom.coe_mk,
    add_mul, mul_add, Finset.sum_add_distrib]
  exact congrArg
    (fun t =>
      (∑ z : I n × I n × I n,
          x z.1 z.2.1 z.2.2 *
            q.1 z.1 z.2.1 z.2.2) + t)
    hshift

/-- The exact free-cube to `J`-kernel-dual component. -/
noncomputable def freeToJKernelI
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F]
      Module.Dual F (T37RightP1.T37JKernel n) :=
  EEOEInternal.cubeDotDual.compl₁₂
    (cubeDiffI (n := n))
    (T37RightP1.T37JKernel n).subtype

theorem freeToJKernelI_eq_dual
    {n : Nat} [NeZero n] :
    freeToJKernelI (n := n) =
      (jKernelIDiff (n := n)).dualMap.comp
        (EEOEInternal.cubeDotEquiv (n := n)).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro q
  exact cubeDiffI_pairing_jKernelIDiff x q

theorem rank_freeToJKernelI
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (freeToJKernelI (n := n))) =
      n * (n - 1) := by
  rw [freeToJKernelI_eq_dual]
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range
      (EEOEInternal.cubeDotEquiv (n := n)))]
  exact
    (LinearMap.finrank_range_dualMap_eq_finrank_range
      (jKernelIDiff (n := n))).trans
      rank_jKernelIDiff

noncomputable def jKernelSwapIK
    {n : Nat} [NeZero n] :
    T37RightP1.T37JKernel n ≃ₗ[F]
      T37RightP1.T37JKernel n where
  toFun q :=
    ⟨EEOEInternal.swapIK q.1, by
      apply LinearMap.mem_ker.mpr
      rw [← EEOEInternal.swapIK_cubeDiffJInv,
        LinearMap.mem_ker.mp q.2, map_zero]⟩
  invFun q :=
    ⟨EEOEInternal.swapIK q.1, by
      apply LinearMap.mem_ker.mpr
      rw [← EEOEInternal.swapIK_cubeDiffJInv,
        LinearMap.mem_ker.mp q.2, map_zero]⟩
  left_inv q := by
    apply Subtype.ext
    exact EEOEInternal.swapIK_swapIK q.1
  right_inv q := by
    apply Subtype.ext
    exact EEOEInternal.swapIK_swapIK q.1
  map_add' q q' := by
    apply Subtype.ext
    exact map_add EEOEInternal.swapIK q.1 q'.1
  map_smul' r q := by
    apply Subtype.ext
    exact map_smul EEOEInternal.swapIK r q.1

noncomputable def freeToJKernelK
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F]
      Module.Dual F (T37RightP1.T37JKernel n) :=
  EEOEInternal.cubeDotDual.compl₁₂
    (cubeDiffK (n := n))
    (T37RightP1.T37JKernel n).subtype

theorem freeToJKernelK_to_I_phase
    {n : Nat} [NeZero n]
    (x : CyclicCube n) (q : T37RightP1.T37JKernel n) :
    freeToJKernelI (EEOEInternal.swapIK x)
        (jKernelSwapIK q) =
      freeToJKernelK x q := by
  change
    cubeDot (cubeDiffI (EEOEInternal.swapIK x))
        (EEOEInternal.swapIK q.1) =
      cubeDot (cubeDiffK x) q.1
  rw [← EEOEInternal.swapIK_cubeDiffK,
    EEOEInternal.cubeDot_swap_both]

theorem rank_freeToJKernelK
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (freeToJKernelK (n := n))) =
      n * (n - 1) := by
  have h :=
    BWSymmetryInternal.rankTransport
      (freeToJKernelK (n := n))
      (freeToJKernelI (n := n))
      (EEOEInternal.swapIK (n := n))
      (jKernelSwapIK (n := n))
      (freeToJKernelK_to_I_phase (n := n))
  exact h.symm.trans rank_freeToJKernelI

noncomputable def rangeCompEquivOfInjective
    {U V W : Type*}
    [AddCommGroup U] [Module F U]
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

noncomputable def rKerFreeBlock
    {n : Nat} [NeZero n] :
    EEOEInternal.RBlockLeft n →ₗ[F]
      Module.Dual F (CyclicCube n) :=
  EEOEInternal.cubeDotDual.comp
    ((cubeDiffK (n := n)).comp
      (EEOEInternal.RBlockLeft n).subtype)

theorem rKerFree_to_pKerFree_phase
    {n : Nat} [NeZero n]
    (u : EEOEInternal.RBlockLeft n)
    (q : CyclicCube n) :
    diamondEOEEWKerPFreeBlock
        (EEOEInternal.rLeftEquivP u)
        (EEOEInternal.swapIK q) =
      rKerFreeBlock u q := by
  change
    cubeDot
        (cubeDiffI (EEOEInternal.swapIK u.1))
        (EEOEInternal.swapIK q) =
      cubeDot (cubeDiffK u.1) q
  rw [← EEOEInternal.swapIK_cubeDiffK,
    EEOEInternal.cubeDot_swap_both]

theorem rank_rKerFreeBlock
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (rKerFreeBlock (n := n))) =
      n * (n - 1) := by
  have h :=
    BWSymmetryInternal.rankTransport
      (rKerFreeBlock (n := n))
      (diamondEOEEWKerPFreeBlock (n := n))
      (EEOEInternal.rLeftEquivP (n := n))
      (EEOEInternal.swapIK (n := n))
      (rKerFree_to_pKerFree_phase (n := n))
  exact h.symm.trans rank_diamondEOEEWKerPFreeBlock

noncomputable def totalWActiveDirect
    {n : Nat} [NeZero n] :
    (EEOEInternal.PBlockLeft n × CyclicCube n) →ₗ[F]
      Module.Dual F
        (CyclicCube n × T37RightP1.T37JKernel n) :=
  diamondCrossProd
    (diamondEOEEWKerPFreeBlock (n := n))
    (freeToJKernelI (n := n))

noncomputable def totalYActiveDirect
    {n : Nat} [NeZero n] :
    (EEOEInternal.RBlockLeft n × CyclicCube n) →ₗ[F]
      Module.Dual F
        (CyclicCube n × T37RightP1.T37JKernel n) :=
  diamondCrossProd
    (rKerFreeBlock (n := n))
    (freeToJKernelK (n := n))

theorem rank_totalWActiveDirect
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (totalWActiveDirect (n := n))) =
      2 * n * (n - 1) := by
  unfold totalWActiveDirect
  rw [finrank_range_diamondCrossProd,
    rank_diamondEOEEWKerPFreeBlock,
    rank_freeToJKernelI]
  ring

theorem rank_totalYActiveDirect
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (totalYActiveDirect (n := n))) =
      2 * n * (n - 1) := by
  unfold totalYActiveDirect
  rw [finrank_range_diamondCrossProd,
    rank_rKerFreeBlock,
    rank_freeToJKernelK]
  ring

noncomputable def totalYActiveProjection
    {n : Nat} [NeZero n] :
    TotalEEEERightInternal.YRightBase n →ₗ[F]
      (CyclicCube n × T37RightP1.T37JKernel n) where
  toFun q := (q.2.1, q.1.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def totalWActiveProjection
    {n : Nat} [NeZero n] :
    TotalEEEERightInternal.WRightBase n →ₗ[F]
      (CyclicCube n × T37RightP1.T37JKernel n) where
  toFun q := (q.1.2, q.1.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem totalYActiveProjection_surjective
    {n : Nat} [NeZero n] :
    Function.Surjective (totalYActiveProjection (n := n)) := by
  intro q
  exact ⟨((q.2, 0), (q.1, 0)), rfl⟩

theorem totalWActiveProjection_surjective
    {n : Nat} [NeZero n] :
    Function.Surjective (totalWActiveProjection (n := n)) := by
  intro q
  exact ⟨((q.2, q.1), (0, 0)), rfl⟩

noncomputable def totalYPulledActive
    {n : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEYLeftBase n →ₗ[F]
      Module.Dual F (TotalEEEERightInternal.YRightBase n) :=
  (totalYActiveProjection (n := n)).dualMap.comp
    (totalYActiveDirect (n := n))

noncomputable def totalWPulledActive
    {n : Nat} [NeZero n] :
    TotalEEEEInternal.TotalEEEEWLeftBase n →ₗ[F]
      Module.Dual F (TotalEEEERightInternal.WRightBase n) :=
  (totalWActiveProjection (n := n)).dualMap.comp
    (totalWActiveDirect (n := n))

theorem totalYPulledActive_eq_production
    {n : Nat} [NeZero n] :
    totalYPulledActive (n := n) =
      TotalEEEEBlockP2.totalEEEEYBaseCross (n := n) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro q
  change
    totalYPulledActive x q =
      TotalEEEEPhase.totalEEEEYBasePhase x q
  rw [TotalEEEEPhase.totalEEEEYBasePhase_reduced]
  change
    cubeDot (cubeDiffK x.1.1) q.2.1 +
        cubeDot (cubeDiffK x.2) q.1.1.1 =
      cubeDot (cubeDiffK x.2) q.1.1.1 +
        cubeDot (cubeDiffK x.1.1) q.2.1
  ac_rfl

theorem totalWPulledActive_eq_production
    {n : Nat} [NeZero n] :
    totalWPulledActive (n := n) =
      TotalEEEEBlockP2.totalEEEEWBaseCross (n := n) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro q
  change
    totalWPulledActive x q =
      TotalEEEEPhase.totalEEEEWBasePhase x q
  rw [TotalEEEEPhase.totalEEEEWBasePhase_reduced]
  change
    cubeDot (cubeDiffI x.1.1) q.1.2 +
        cubeDot (cubeDiffI x.2) q.1.1.1 =
      cubeDot (cubeDiffI x.2) q.1.1.1 +
        cubeDot (cubeDiffI x.1.1) q.1.2
  ac_rfl

theorem rank_totalYPulledActive
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (totalYPulledActive (n := n))) =
      2 * n * (n - 1) := by
  let E :=
    rangeCompEquivOfInjective
      (totalYActiveDirect (n := n))
      (totalYActiveProjection (n := n)).dualMap
      (LinearMap.dualMap_injective_of_surjective
        (totalYActiveProjection_surjective (n := n)))
  calc
    Module.finrank F
        (LinearMap.range (totalYPulledActive (n := n))) =
        Module.finrank F
          (LinearMap.range (totalYActiveDirect (n := n))) :=
      (LinearEquiv.finrank_eq E).symm
    _ = 2 * n * (n - 1) := rank_totalYActiveDirect

theorem rank_totalWPulledActive
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (totalWPulledActive (n := n))) =
      2 * n * (n - 1) := by
  let E :=
    rangeCompEquivOfInjective
      (totalWActiveDirect (n := n))
      (totalWActiveProjection (n := n)).dualMap
      (LinearMap.dualMap_injective_of_surjective
        (totalWActiveProjection_surjective (n := n)))
  calc
    Module.finrank F
        (LinearMap.range (totalWPulledActive (n := n))) =
        Module.finrank F
          (LinearMap.range (totalWActiveDirect (n := n))) :=
      (LinearEquiv.finrank_eq E).symm
    _ = 2 * n * (n - 1) := rank_totalWActiveDirect

noncomputable def pairFst
    {n : Nat} [NeZero n] :
    (CyclicCube n × CyclicCube n) →ₗ[F] CyclicCube n :=
  LinearMap.fst F (CyclicCube n) (CyclicCube n)

theorem pairFst_surjective
    {n : Nat} [NeZero n] :
    Function.Surjective (pairFst (n := n)) := by
  intro x
  exact ⟨(x, 0), rfl⟩

theorem productionYZ_eq_fstDual_singleK
    {n : Nat} [NeZero n] :
    TotalEEEEBlockP2.totalEEEEYZBaseCross (n := n) =
      (pairFst (n := n)).dualMap.comp
        (diamondTailSingleKCross (n := n)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro q
  rfl

theorem productionWZ_eq_fstDual_singleI
    {n : Nat} [NeZero n] :
    TotalEEEEBlockP2.totalEEEEWZBaseCross (n := n) =
      (pairFst (n := n)).dualMap.comp
        (diamondTailSingleICross (n := n)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro q
  rfl

end RankComponents

end TotalEEEERankInternal

theorem rank_totalEEEEYBaseCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (TotalEEEEBlockP2.totalEEEEYBaseCross (n := n))) =
      2 * n * (n - 1) := by
  rw [← TotalEEEERankInternal.totalYPulledActive_eq_production]
  exact TotalEEEERankInternal.rank_totalYPulledActive

theorem rank_totalEEEEWBaseCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (TotalEEEEBlockP2.totalEEEEWBaseCross (n := n))) =
      2 * n * (n - 1) := by
  rw [← TotalEEEERankInternal.totalWPulledActive_eq_production]
  exact TotalEEEERankInternal.rank_totalWPulledActive

theorem rank_totalEEEEYZBaseCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (TotalEEEEBlockP2.totalEEEEYZBaseCross (n := n))) =
      n ^ 2 * (n - 1) := by
  rw [TotalEEEERankInternal.productionYZ_eq_fstDual_singleK]
  let E :=
    TotalEEEERankInternal.rangeCompEquivOfInjective
      (diamondTailSingleKCross (n := n))
      (TotalEEEERankInternal.pairFst (n := n)).dualMap
      (LinearMap.dualMap_injective_of_surjective
        (TotalEEEERankInternal.pairFst_surjective (n := n)))
  exact
    (LinearEquiv.finrank_eq E).symm.trans
      rank_diamondTailSingleKCross

theorem rank_totalEEEEWZBaseCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (TotalEEEEBlockP2.totalEEEEWZBaseCross (n := n))) =
      n ^ 2 * (n - 1) := by
  rw [TotalEEEERankInternal.productionWZ_eq_fstDual_singleI]
  let E :=
    TotalEEEERankInternal.rangeCompEquivOfInjective
      (diamondTailSingleICross (n := n))
      (TotalEEEERankInternal.pairFst (n := n)).dualMap
      (LinearMap.dualMap_injective_of_surjective
        (TotalEEEERankInternal.pairFst_surjective (n := n)))
  exact
    (LinearEquiv.finrank_eq E).symm.trans
      rank_diamondTailSingleICross

namespace TotalEEEERankAssembly

private local instance cubePairGroup
    {n : Nat} :
    AddCommGroup (CyclicCube n × CyclicCube n) :=
  inferInstance

private local instance cubePairModule
    {n : Nat} :
    Module F (CyclicCube n × CyclicCube n) :=
  inferInstance

private local instance cubePairFinite
    {n : Nat} [NeZero n] :
    FiniteDimensional F (CyclicCube n × CyclicCube n) :=
  inferInstance

private local instance cubeFourGroup
    {n : Nat} :
    AddCommGroup
      ((CyclicCube n × CyclicCube n) ×
        (CyclicCube n × CyclicCube n)) :=
  inferInstance

private local instance cubeFourModule
    {n : Nat} :
    Module F
      ((CyclicCube n × CyclicCube n) ×
        (CyclicCube n × CyclicCube n)) :=
  inferInstance

private local instance cubeFourFinite
    {n : Nat} [NeZero n] :
    FiniteDimensional F
      ((CyclicCube n × CyclicCube n) ×
        (CyclicCube n × CyclicCube n)) :=
  inferInstance

private local instance scalarAmbientGroup
    {n : Nat} :
    AddCommGroup (DiamondEEEELeftAmbient n) :=
  inferInstance

private local instance scalarAmbientModule
    {n : Nat} :
    Module F (DiamondEEEELeftAmbient n) :=
  inferInstance

private local instance scalarAmbientFinite
    {n : Nat} [NeZero n] :
    FiniteDimensional F (DiamondEEEELeftAmbient n) :=
  inferInstance

private local instance scalarLeftGroup
    {n : Nat} [NeZero n] :
    AddCommGroup (DiamondEEEELeftSource n) :=
  (DiamondEEEELeftSource n).addCommGroup

private local instance scalarLeftFinite
    {n : Nat} [NeZero n] :
    FiniteDimensional F (DiamondEEEELeftSource n) :=
  FiniteDimensional.of_injective
    (DiamondEEEELeftSource n).subtype Subtype.val_injective

private local instance yTailLeftGroup
    {n b : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEInternal.TotalEEEEYTailLeft n b) :=
  (TotalEEEEInternal.TotalEEEEYTailLeft n b).addCommGroup

private local instance yTailLeftFinite
    {n b : Nat} [NeZero n] :
    FiniteDimensional F (TotalEEEEInternal.TotalEEEEYTailLeft n b) :=
  FiniteDimensional.of_injective
    (TotalEEEEInternal.TotalEEEEYTailLeft n b).subtype
      Subtype.val_injective

private local instance wTailLeftGroup
    {n d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEInternal.TotalEEEEWTailLeft n d) :=
  (TotalEEEEInternal.TotalEEEEWTailLeft n d).addCommGroup

private local instance wTailLeftFinite
    {n d : Nat} [NeZero n] :
    FiniteDimensional F (TotalEEEEInternal.TotalEEEEWTailLeft n d) :=
  FiniteDimensional.of_injective
    (TotalEEEEInternal.TotalEEEEWTailLeft n d).subtype
      Subtype.val_injective

private local instance zTailLeftGroup
    {n c : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEInternal.TotalEEEEZTailLeft n c) :=
  (TotalEEEEInternal.TotalEEEEZTailLeft n c).addCommGroup

private local instance zTailLeftFinite
    {n c : Nat} [NeZero n] :
    FiniteDimensional F (TotalEEEEInternal.TotalEEEEZTailLeft n c) :=
  FiniteDimensional.of_injective
    (TotalEEEEInternal.TotalEEEEZTailLeft n c).subtype
      Subtype.val_injective

private local instance yzTailLeftGroup
    {n b c : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEInternal.TotalEEEEYZTailLeft n b c) :=
  (TotalEEEEInternal.TotalEEEEYZTailLeft n b c).addCommGroup

private local instance yzTailLeftFinite
    {n b c : Nat} [NeZero n] :
    FiniteDimensional F (TotalEEEEInternal.TotalEEEEYZTailLeft n b c) :=
  FiniteDimensional.of_injective
    (TotalEEEEInternal.TotalEEEEYZTailLeft n b c).subtype
      Subtype.val_injective

private local instance wzTailLeftGroup
    {n c d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEInternal.TotalEEEEWZTailLeft n c d) :=
  (TotalEEEEInternal.TotalEEEEWZTailLeft n c d).addCommGroup

private local instance wzTailLeftFinite
    {n c d : Nat} [NeZero n] :
    FiniteDimensional F (TotalEEEEInternal.TotalEEEEWZTailLeft n c d) :=
  FiniteDimensional.of_injective
    (TotalEEEEInternal.TotalEEEEWZTailLeft n c d).subtype
      Subtype.val_injective

private local instance ywTailLeftGroup
    {n b d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEInternal.TotalEEEEYWLeftZero n b d) :=
  (TotalEEEEInternal.TotalEEEEYWLeftZero n b d).addCommGroup

private local instance ywTailLeftFinite
    {n b d : Nat} [NeZero n] :
    FiniteDimensional F (TotalEEEEInternal.TotalEEEEYWLeftZero n b d) :=
  FiniteDimensional.of_injective
    (TotalEEEEInternal.TotalEEEEYWLeftZero n b d).subtype
      Subtype.val_injective

private local instance ywzTailLeftGroup
    {n b c d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d) :=
  (TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d).addCommGroup

private local instance ywzTailLeftFinite
    {n b c d : Nat} [NeZero n] :
    FiniteDimensional F
      (TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d) :=
  FiniteDimensional.of_injective
    (TotalEEEEInternal.TotalEEEEYWZLeftZero n b c d).subtype
      Subtype.val_injective

private local instance bottomCubeFinite
    {n : Nat} [NeZero n] :
    FiniteDimensional F (↥(⊥ : Submodule F (CyclicCube n))) :=
  FiniteDimensional.of_injective
    (⊥ : Submodule F (CyclicCube n)).subtype Subtype.val_injective

private local instance wBottomTailGroup
    {n d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEInternal.TotalEEEEWBottomTail n d) :=
  (TotalEEEEInternal.TotalEEEEWBottomTail n d).addCommGroup

private local instance wBottomTailFinite
    {n d : Nat} [NeZero n] :
    FiniteDimensional F (TotalEEEEInternal.TotalEEEEWBottomTail n d) :=
  FiniteDimensional.of_injective
    (TotalEEEEInternal.TotalEEEEWBottomTail n d).subtype
      Subtype.val_injective

private local instance zwBottomTailGroup
    {n c d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEInternal.TotalEEEEZWBottomTail n c d) :=
  (TotalEEEEInternal.TotalEEEEZWBottomTail n c d).addCommGroup

private local instance zwBottomTailFinite
    {n c d : Nat} [NeZero n] :
    FiniteDimensional F
      (TotalEEEEInternal.TotalEEEEZWBottomTail n c d) :=
  FiniteDimensional.of_injective
    (TotalEEEEInternal.TotalEEEEZWBottomTail n c d).subtype
      Subtype.val_injective

private local instance scalarRightGroup
    {n : Nat} [NeZero n] :
    AddCommGroup (DiamondEEEERightSource n) :=
  (DiamondEEEERightSource n).addCommGroup

private local instance yRightBaseGroup
    {n : Nat} [NeZero n] :
    AddCommGroup (TotalEEEERightInternal.YRightBase n) :=
  inferInstance

private local instance wRightBaseGroup
    {n : Nat} [NeZero n] :
    AddCommGroup (TotalEEEERightInternal.WRightBase n) :=
  inferInstance

private local instance yTailRightGroup
    {n b : Nat} [NeZero n] :
    AddCommGroup
      (DiamondEvenAxisValueTailZero n b
        (TotalEEEERightInternal.YRightBase n)) :=
  (DiamondEvenAxisValueTailZero n b
    (TotalEEEERightInternal.YRightBase n)).addCommGroup

private local instance wTailRightGroup
    {n d : Nat} [NeZero n] :
    AddCommGroup
      (DiamondEvenAxisValueTailZero n d
        (TotalEEEERightInternal.WRightBase n)) :=
  (DiamondEvenAxisValueTailZero n d
    (TotalEEEERightInternal.WRightBase n)).addCommGroup

private local instance zTailRightGroup
    {n c : Nat} [NeZero n] :
    AddCommGroup
      (DiamondEvenAxisValueTailZero n c
        (DiamondEEOERightAmbient n)) :=
  (DiamondEvenAxisValueTailZero n c
    (DiamondEEOERightAmbient n)).addCommGroup

private local instance yzTailRightGroup
    {n b c : Nat} [NeZero n] :
    AddCommGroup
      (DiamondMixedTailZero n b c
        (CyclicCube n × CyclicCube n)) :=
  (DiamondMixedTailZero n b c
    (CyclicCube n × CyclicCube n)).addCommGroup

private local instance wzTailRightGroup
    {n c d : Nat} [NeZero n] :
    AddCommGroup
      (DiamondMixedTailZero n c d
        (CyclicCube n × CyclicCube n)) :=
  (DiamondMixedTailZero n c d
    (CyclicCube n × CyclicCube n)).addCommGroup

private local instance ywTailRightGroup
    {n b d : Nat} [NeZero n] :
    AddCommGroup
      (DiamondMixedTailZero n b d
        (TotalEEEERightInternal.YWRightBase n)) :=
  (DiamondMixedTailZero n b d
    (TotalEEEERightInternal.YWRightBase n)).addCommGroup

private local instance ywzTailRightGroup
    {n b c d : Nat} [NeZero n] :
    AddCommGroup
      (DiamondEvenAxisValueTailZero n b
        (DiamondEvenAxisValueTailZero n c
          (DiamondEvenAxisValueTailZero n d (CyclicCube n)))) :=
  (DiamondEvenAxisValueTailZero n b
    (DiamondEvenAxisValueTailZero n c
      (DiamondEvenAxisValueTailZero n d (CyclicCube n)))).addCommGroup

private theorem diamondCrossProd_apply_local
    {U₁ U₂ V₁ V₂ : Type*}
    [AddCommGroup U₁] [Module F U₁]
    [AddCommGroup U₂] [Module F U₂]
    [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂]
    (f : U₁ →ₗ[F] Module.Dual F V₁)
    (g : U₂ →ₗ[F] Module.Dual F V₂)
    (u : U₁ × U₂) (v : V₁ × V₂) :
    diamondCrossProd f g u v =
      f u.1 v.1 + g u.2 v.2 :=
  rfl

set_option maxHeartbeats 30000000 in
-- Elaborating the exact eight-sector block-map equality needs this budget.
private theorem diamondEEEETotalBlockCross_eq_rank_product
    {n b c d : Nat} [NeZero n] :
    TotalEEEEBlockP2.diamondEEEETotalBlockCross
        (n := n) (b := b) (c := c) (d := d) =
      diamondCrossProd
        (diamondEEEECross (n := n))
        (diamondCrossProd
          (diamondTailAmplify
            (n := n) (k := b)
            (TotalEEEEBlockP2.totalEEEEYBaseCross (n := n)))
          (diamondCrossProd
            (diamondTailAmplify
              (n := n) (k := d)
              (TotalEEEEBlockP2.totalEEEEWBaseCross (n := n)))
            (diamondCrossProd
              (diamondTailAmplify
                (n := n) (k := c)
                (diamondTailAllEvenZCross (n := n)))
              (diamondCrossProd
                (diamondMixedTailAmplify
                  (n := n) (k := b) (l := c)
                  (TotalEEEEBlockP2.totalEEEEYZBaseCross (n := n)))
                (diamondCrossProd
                  (diamondMixedTailAmplify
                    (n := n) (k := c) (l := d)
                    (TotalEEEEBlockP2.totalEEEEWZBaseCross (n := n)))
                  (diamondCrossProd
                    (diamondMixedTailAmplify
                      (n := n) (k := b) (l := d)
                      (0 :
                        (⊥ : Submodule F (CyclicCube n)) →ₗ[F]
                          Module.Dual F
                            (TotalEEEERightInternal.YWRightBase n)))
                    (diamondTailAmplify (n := n) (k := b)
                      (diamondTailAmplify (n := n) (k := c)
                        (diamondTailAmplify (n := n) (k := d)
                          (0 :
                            (⊥ : Submodule F (CyclicCube n)) →ₗ[F]
                              Module.Dual F (CyclicCube n))))))))))) := by
  have hyPhase
      (x : TotalEEEEInternal.TotalEEEEYLeftBase n)
      (q : TotalEEEERightInternal.YRightBase n) :
      TotalEEEEBlockP2.totalEEEEYBaseCross x q =
        TotalEEEEPhase.totalEEEEYBasePhase x q :=
    rfl
  have hwPhase
      (x : TotalEEEEInternal.TotalEEEEWLeftBase n)
      (q : TotalEEEERightInternal.WRightBase n) :
      TotalEEEEBlockP2.totalEEEEWBaseCross x q =
        TotalEEEEPhase.totalEEEEWBasePhase x q :=
    rfl
  have hyzPhase
      (x : CyclicCube n)
      (q : CyclicCube n × CyclicCube n) :
      TotalEEEEBlockP2.totalEEEEYZBaseCross x q =
        TotalEEEEPhase.totalEEEEYZBasePhase x q :=
    rfl
  have hwzPhase
      (x : CyclicCube n)
      (q : CyclicCube n × CyclicCube n) :
      TotalEEEEBlockP2.totalEEEEWZBaseCross x q =
        TotalEEEEPhase.totalEEEEWZBasePhase x q :=
    rfl
  apply LinearMap.ext
  intro l
  apply LinearMap.ext
  intro q
  rw [TotalEEEEBlockP2.diamondEEEETotalBlockCross_apply]
  simp only [diamondCrossProd_apply_local,
    diamondTailAmplify_apply, diamondMixedTailAmplify]
  unfold TotalEEEEPhase.totalEEEECoordinatePhase
  simp_rw [hyPhase, hwPhase, hyzPhase, hwzPhase]
  simp only [LinearMap.zero_apply,
    TotalEEEEPhase.totalEEEEYWBasePhase,
    TotalEEEEPhase.totalEEEEYWZBasePhase]
  ac_rfl

private theorem finrank_range_zero
    {U V : Type}
    [AddCommMonoid U] [Module F U]
    [AddCommMonoid V] [Module F V] :
    Module.finrank F
        (LinearMap.range (0 : U →ₗ[F] V)) = 0 := by
  rw [LinearMap.range_zero]
  exact finrank_bot F V

set_option maxHeartbeats 30000000 in
-- Rewriting the exact nested product ranges and tail ranks needs this budget.
theorem totalBlockCross_addition_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (TotalEEEEBlockP2.diamondEEEETotalBlockCross
            (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) * (3 * n ^ 2 + 4) +
        ((n ^ (b - 1) - 2) * (2 * n * (n - 1)) +
          ((n ^ (d - 1) - 2) * (2 * n * (n - 1)) +
            ((n ^ (c - 1) - 2) *
                ((n - 1) * (3 * n ^ 2 + n)) +
              (((n ^ (b - 1) - 2) * (n ^ (c - 1) - 2)) *
                  (n ^ 2 * (n - 1)) +
                (((n ^ (c - 1) - 2) * (n ^ (d - 1) - 2)) *
                    (n ^ 2 * (n - 1)) +
                  (0 + 0)))))) := by
  rw [diamondEEEETotalBlockCross_eq_rank_product]
  simp only [finrank_range_diamondCrossProd]
  simp only [
    finrank_range_diamondTailAmplify (n := n) (k := b)
      hn2 hn hb2,
    finrank_range_diamondTailAmplify (n := n) (k := d)
      hn2 hn hd2,
    finrank_range_diamondTailAmplify (n := n) (k := c)
      hn2 hn hc2,
    finrank_range_diamondMixedTailAmplify
      (n := n) (k := b) (l := c) hn2 hn hb2 hc2,
    finrank_range_diamondMixedTailAmplify
      (n := n) (k := c) (l := d) hn2 hn hc2 hd2,
    finrank_range_diamondMixedTailAmplify
      (n := n) (k := b) (l := d) hn2 hn hb2 hd2]
  rw [finrank_diamondEvenAxisTailZero hn2 hn hb2,
    finrank_diamondEvenAxisTailZero hn2 hn hc2,
    finrank_diamondEvenAxisTailZero hn2 hn hd2,
    rank_diamondTailAllEvenZCross,
    rank_totalEEEEYBaseCross,
    rank_totalEEEEWBaseCross,
    rank_totalEEEEYZBaseCross,
    rank_totalEEEEWZBaseCross,
    rank_diamondEvenP_cross_EEEE_scalar hn2 hn]
  rw [finrank_range_zero, finrank_range_zero]
  simp only [Nat.mul_zero]

private local instance totalLeftGroup
    {n b c d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEELeftSourceTarget n b c d) :=
  inferInstance

private local instance totalRightGroup
    {n b c d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEERightReachableTarget n b c d) :=
  inferInstance

noncomputable def literalRangeTransport
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    LinearMap.range
        (diamondEvenPCross
          (n := n) (b := b) (c := c) (d := d)) ≃ₗ[F]
      LinearMap.range
        (TotalEEEEBlockP2.diamondEEEETotalBlockCross
          (n := n) (b := b) (c := c) (d := d)) :=
  BWSymmetryInternal.rangeTransportEquiv
    (L := DiamondEvenPLeft n b c d)
    (R := DiamondEvenPReachableA n b c d)
    (L' := TotalEEEELeftSourceTarget n b c d)
    (R' := TotalEEEERightReachableTarget n b c d)
    (diamondEvenPCross
      (n := n) (b := b) (c := c) (d := d))
    (TotalEEEEBlockP2.diamondEEEETotalBlockCross
      (n := n) (b := b) (c := c) (d := d))
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
    (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2)
    (TotalEEEEBlockP2.diamondEvenPCross_EEEE_phase
      hn hb2 hc2 hd2)

end TotalEEEERankAssembly

theorem rank_diamondEEEETotalBlockCross_addition_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (TotalEEEEBlockP2.diamondEEEETotalBlockCross
            (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) * (3 * n ^ 2 + 4) +
        ((n ^ (b - 1) - 2) * (2 * n * (n - 1)) +
          ((n ^ (d - 1) - 2) * (2 * n * (n - 1)) +
            ((n ^ (c - 1) - 2) *
                ((n - 1) * (3 * n ^ 2 + n)) +
              (((n ^ (b - 1) - 2) * (n ^ (c - 1) - 2)) *
                  (n ^ 2 * (n - 1)) +
                (((n ^ (c - 1) - 2) * (n ^ (d - 1) - 2)) *
                    (n ^ 2 * (n - 1)) +
                  (0 + 0)))))) :=
  TotalEEEERankAssembly.totalBlockCross_addition_first
    hn2 hn hb2 hc2 hd2

set_option maxHeartbeats 30000000 in
-- Normalizing the exact natural-number sector sum needs this budget.
theorem rank_diamondEEEETotalBlockCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (TotalEEEEBlockP2.diamondEEEETotalBlockCross
            (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) *
        (n ^ 2 * (n ^ (d - 1) - 2) * (n ^ (c - 1) - 2) +
          n ^ 2 * (n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) +
          (3 * n ^ 2 + n) * (n ^ (c - 1) - 2) +
          2 * n * (n ^ (d - 1) - 2) +
          2 * n * (n ^ (b - 1) - 2) +
          3 * n ^ 2 + 4) := by
  rw [rank_diamondEEEETotalBlockCross_addition_first
    hn2 hn hb2 hc2 hd2]
  ring

noncomputable def diamondEvenPCross_EEEE_rangeEquiv
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    LinearMap.range
        (diamondEvenPCross
          (n := n) (b := b) (c := c) (d := d)) ≃ₗ[F]
      LinearMap.range
        (TotalEEEEBlockP2.diamondEEEETotalBlockCross
          (n := n) (b := b) (c := c) (d := d)) :=
  TotalEEEERankAssembly.literalRangeTransport
    hn hb2 hc2 hd2

theorem rank_diamondEvenPCross_EEEE
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) *
        (n ^ 2 * (n ^ (d - 1) - 2) * (n ^ (c - 1) - 2) +
          n ^ 2 * (n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) +
          (3 * n ^ 2 + n) * (n ^ (c - 1) - 2) +
          2 * n * (n ^ (d - 1) - 2) +
          2 * n * (n ^ (b - 1) - 2) +
          3 * n ^ 2 + 4) := by
  calc
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := b) (c := c) (d := d))) =
        Module.finrank F
          (LinearMap.range
            (TotalEEEEBlockP2.diamondEEEETotalBlockCross
              (n := n) (b := b) (c := c) (d := d))) :=
      LinearEquiv.finrank_eq
        (diamondEvenPCross_EEEE_rangeEquiv hn hb2 hc2 hd2)
    _ = (n - 1) *
        (n ^ 2 * (n ^ (d - 1) - 2) * (n ^ (c - 1) - 2) +
          n ^ 2 * (n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) +
          (3 * n ^ 2 + n) * (n ^ (c - 1) - 2) +
          2 * n * (n ^ (d - 1) - 2) +
          2 * n * (n ^ (b - 1) - 2) +
          3 * n ^ 2 + 4) :=
      rank_diamondEEEETotalBlockCross hn2 hn hb2 hc2 hd2

end

end Core4loop.SquareDiagonal.EvenP
