import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Factors
import Core4loop.CompleteGraph.EvenAllLarge.AggregateRank

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.EEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.CompleteGraph.CubeCompat
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.GPolarRankPrep
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

attribute [local instance] Fintype.ofFinite

/- The scalar multiplier source intentionally kept its deterministic section
helpers private.  This owner must expose the same literal section without
changing that source file, so the following owner-local tactic delta-expands
only those six imported implementation constants by their exact suffix. -/
private def scalarMultiplierSectionPrivateSuffixes : Array String := #[
  ".scalarAddedCoeffMap", ".scalarBFreeRead", ".scalarWFreeRead",
  ".bFreeLambda", ".wFreeLambda", ".rStarPrimitive", ".pStarPrimitive",
  ".kappaCoeff", ".kappaTransposeCoeff", ".rOrbit", ".pOrbit"]

open Lean Meta Elab Tactic in
elab "unfoldScalarMultiplierSections" : tactic =>
  liftMetaTactic fun goal => do
    let mut current := goal
    for _ in List.range 16 do
      let target ← current.getType
      let candidate := target.getUsedConstants.find? fun decl =>
        scalarMultiplierSectionPrivateSuffixes.any fun suffix =>
          decl.toString.endsWith suffix
      match candidate with
      | none => pure ()
      | some decl => current := ← Lean.Meta.unfoldTarget current decl
    return [current]

/-! ## Literal Kappa coefficients -/

noncomputable def k4ScalarKappaBCoeff
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n where
  toFun B := fun i j k => B i j k + B (i + 1) j (k - 1)
  map_add' _ _ := by
    funext i j k
    simp only [Pi.add_apply]
    abel
  map_smul' a B := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add]

noncomputable def k4ScalarKappaWCoeff
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n where
  toFun W := fun i j k => W i j k + W (i - 1) j (k + 1)
  map_add' _ _ := by
    funext i j k
    simp only [Pi.add_apply]
    abel
  map_smul' a W := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add]

theorem k4CubeKappa_eq_cubeDot_k4ScalarKappaBCoeff
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappa B W = cubeDot (k4ScalarKappaBCoeff B) W := by
  unfold k4CubeKappa cubeDot k4ScalarKappaBCoeff
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.refl (I n))
      (Equiv.prodCongr (Equiv.refl (I n)) (Equiv.addRight (1 : I n)))
  apply Fintype.sum_equiv e
  intro q
  simp [e]

theorem k4CubeKappa_eq_cubeDot_k4ScalarKappaWCoeff
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappa B W = cubeDot B (k4ScalarKappaWCoeff W) := by
  unfold k4CubeKappa cubeDot k4ScalarKappaWCoeff
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.addRight (1 : I n))
      (Equiv.refl (I n × I n))
  apply Fintype.sum_equiv e
  intro q
  simp [e]

private theorem cubeDot_comm_local
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot X Y = cubeDot Y X := by
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  exact mul_comm _ _

/-! ## Exact annihilator/range certificates -/

theorem mem_ker_k4RHeadCross_iff_kappaBCoeff_mem_range_RStar
    {n : Nat} [NeZero n] (B : CyclicCube n) :
    B ∈ LinearMap.ker (k4RHeadCross (n := n)) ↔
      k4ScalarKappaBCoeff B ∈
        LinearMap.range (cubeDiffRStar (n := n)) := by
  constructor
  · intro hB
    let phi : Module.Dual F (CyclicCube n) :=
      EEEEInternal.cubeDotDual (k4ScalarKappaBCoeff B)
    have hvanish : ∀ W : CyclicCube n,
        cubeDiffR W ∈ LinearMap.range
            (0 : CyclicCube n →ₗ[F] CyclicCube n) →
          phi W = 0 := by
      intro W hW
      have hdiff : cubeDiffR W = 0 := by
        rcases hW with ⟨X, hX⟩
        simpa using hX.symm
      let WK : LinearMap.ker (cubeDiffR (n := n)) :=
        ⟨W, LinearMap.mem_ker.mpr hdiff⟩
      have hcross := LinearMap.congr_fun (LinearMap.mem_ker.mp hB) WK
      change k4CubeKappa B W = 0 at hcross
      simpa [phi, EEEEInternal.cubeDotDual,
        k4CubeKappa_eq_cubeDot_k4ScalarKappaBCoeff] using hcross
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        cubeDiffR (0 : CyclicCube n →ₗ[F] CyclicCube n) phi hvanish with
      ⟨psi, hfactor, _⟩
    rcases EEEEInternal.dual_exists_cubeDot psi with ⟨lambda, hlambda⟩
    refine ⟨lambda, ?_⟩
    apply EEEEInternal.cubeDot_left_ext
    intro W
    calc
      cubeDot (cubeDiffRStar lambda) W = cubeDot lambda (cubeDiffR W) :=
        cubeDiffR_pairing_adjoint lambda W
      _ = psi (cubeDiffR W) := (hlambda _).symm
      _ = phi W := LinearMap.congr_fun hfactor W |>.symm
      _ = cubeDot (k4ScalarKappaBCoeff B) W := rfl
  · rintro ⟨lambda, hlambda⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro W
    change k4CubeKappa B W.1 = 0
    rw [k4CubeKappa_eq_cubeDot_k4ScalarKappaBCoeff, ← hlambda,
      cubeDiffR_pairing_adjoint]
    rw [LinearMap.mem_ker.mp W.2]
    simp [cubeDot]

theorem mem_ker_k4PHeadCross_flip_iff_kappaWCoeff_mem_range_PStar
    {n : Nat} [NeZero n] (W : CyclicCube n) :
    W ∈ LinearMap.ker (k4PHeadCross (n := n)).flip ↔
      k4ScalarKappaWCoeff W ∈
        LinearMap.range (cubeDiffPStar (n := n)) := by
  constructor
  · intro hW
    let phi : Module.Dual F (CyclicCube n) :=
      EEEEInternal.cubeDotDual (k4ScalarKappaWCoeff W)
    have hvanish : ∀ B : CyclicCube n,
        cubeDiffP B ∈ LinearMap.range
            (0 : CyclicCube n →ₗ[F] CyclicCube n) →
          phi B = 0 := by
      intro B hB
      have hdiff : cubeDiffP B = 0 := by
        rcases hB with ⟨X, hX⟩
        simpa using hX.symm
      let BK : LinearMap.ker (cubeDiffP (n := n)) :=
        ⟨B, LinearMap.mem_ker.mpr hdiff⟩
      have hcross := LinearMap.congr_fun (LinearMap.mem_ker.mp hW) BK
      change k4CubeKappa B W = 0 at hcross
      rw [k4CubeKappa_eq_cubeDot_k4ScalarKappaWCoeff,
        cubeDot_comm_local] at hcross
      simpa [phi, EEEEInternal.cubeDotDual] using hcross
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        cubeDiffP (0 : CyclicCube n →ₗ[F] CyclicCube n) phi hvanish with
      ⟨psi, hfactor, _⟩
    rcases EEEEInternal.dual_exists_cubeDot psi with ⟨lambda, hlambda⟩
    refine ⟨lambda, ?_⟩
    apply EEEEInternal.cubeDot_left_ext
    intro B
    calc
      cubeDot (cubeDiffPStar lambda) B = cubeDot lambda (cubeDiffP B) :=
        cubeDiffP_pairing_adjoint lambda B
      _ = psi (cubeDiffP B) := (hlambda _).symm
      _ = phi B := LinearMap.congr_fun hfactor B |>.symm
      _ = cubeDot (k4ScalarKappaWCoeff W) B := rfl
  · rintro ⟨lambda, hlambda⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro B
    change k4CubeKappa B.1 W = 0
    rw [k4CubeKappa_eq_cubeDot_k4ScalarKappaWCoeff]
    rw [← hlambda, cubeDot_comm_local, cubeDiffP_pairing_adjoint]
    rw [LinearMap.mem_ker.mp B.2]
    simp [cubeDot]

/-! ## Deterministic orbit-prefix sections -/

private noncomputable def scalarROrbit
    {n : Nat} [NeZero n] (K : CyclicCube n) (i s : I n) : Profile n :=
  fun t => K i t (s - t)

private noncomputable def scalarPOrbit
    {n : Nat} [NeZero n] (K : CyclicCube n) (s k : I n) : Profile n :=
  fun t => K (s - t) t k

private noncomputable def scalarRStarPrimitive
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n where
  toFun K := fun i j k => explicitCyclicPrefix (scalarROrbit K i (j + k)) j
  map_add' K K' := by
    funext i j k
    simp only [scalarROrbit, Pi.add_apply, explicitCyclicPrefix, finPrefix,
      Finset.sum_add_distrib]
  map_smul' a K := by
    funext i j k
    simp only [scalarROrbit, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      explicitCyclicPrefix, finPrefix, ← Finset.mul_sum]

private noncomputable def scalarPStarPrimitive
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n where
  toFun K := fun i j k => explicitCyclicPrefix (scalarPOrbit K (i + j) k) j
  map_add' K K' := by
    funext i j k
    simp only [scalarPOrbit, Pi.add_apply, explicitCyclicPrefix, finPrefix,
      Finset.sum_add_distrib]
  map_smul' a K := by
    funext i j k
    simp only [scalarPOrbit, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      explicitCyclicPrefix, finPrefix, ← Finset.mul_sum]

private theorem scalarRStarPrimitive_rightInverse_of_orbit_zero
    {n : Nat} [NeZero n] (K : CyclicCube n)
    (hzero : ∀ i s : I n, ∑ t : I n, scalarROrbit K i s t = 0) :
    cubeDiffRStar (scalarRStarPrimitive K) = K := by
  funext i j k
  rw [EEOEInternal.cubeDiffRStar_apply]
  change
    explicitCyclicPrefix (scalarROrbit K i (j + k)) j +
        explicitCyclicPrefix (scalarROrbit K i (j + 1 + (k - 1))) (j + 1) =
      K i j k
  have hs : j + 1 + (k - 1) = j + k := by abel
  rw [hs]
  let u : ZeroSumProfile n :=
    ⟨scalarROrbit K i (j + k),
      LinearMap.mem_ker.mpr (hzero i (j + k))⟩
  have hdiff := congrFun (cycDiff_explicitCyclicPrimitive u) j
  change
    explicitCyclicPrefix (scalarROrbit K i (j + k)) j +
        explicitCyclicPrefix (scalarROrbit K i (j + k)) (j + 1) =
      scalarROrbit K i (j + k) j at hdiff
  rw [hdiff]
  simp only [scalarROrbit]
  congr 3
  abel

private theorem scalarPStarPrimitive_rightInverse_of_orbit_zero
    {n : Nat} [NeZero n] (K : CyclicCube n)
    (hzero : ∀ s k : I n, ∑ t : I n, scalarPOrbit K s k t = 0) :
    cubeDiffPStar (scalarPStarPrimitive K) = K := by
  funext i j k
  rw [EEOEInternal.cubeDiffPStar_apply]
  change
    explicitCyclicPrefix (scalarPOrbit K (i + j) k) j +
        explicitCyclicPrefix (scalarPOrbit K ((i - 1) + (j + 1)) k) (j + 1) =
      K i j k
  have hs : (i - 1) + (j + 1) = i + j := by abel
  rw [hs]
  let u : ZeroSumProfile n :=
    ⟨scalarPOrbit K (i + j) k,
      LinearMap.mem_ker.mpr (hzero (i + j) k)⟩
  have hdiff := congrFun (cycDiff_explicitCyclicPrimitive u) j
  change
    explicitCyclicPrefix (scalarPOrbit K (i + j) k) j +
        explicitCyclicPrefix (scalarPOrbit K (i + j) k) (j + 1) =
      scalarPOrbit K (i + j) k j at hdiff
  rw [hdiff]
  simp only [scalarPOrbit]
  congr 3
  abel

private theorem scalarROrbit_zero_of_mem_range
    {n : Nat} [NeZero n] (K : CyclicCube n)
    (hK : K ∈ LinearMap.range (cubeDiffRStar (n := n)))
    (i s : I n) :
    ∑ t : I n, scalarROrbit K i s t = 0 := by
  rcases hK with ⟨lambda, rfl⟩
  let f : Profile n := fun t => lambda i t (s - t)
  change ∑ t : I n, cubeDiffRStar lambda i t (s - t) = 0
  simp only [EEOEInternal.cubeDiffRStar_apply]
  have hf (t : I n) :
      lambda i (t + 1) (s - t - 1) = f (t + 1) := by
    dsimp only [f]
    apply congrArg (fun x => lambda i (t + 1) x)
    abel
  simp_rw [hf]
  change ∑ t : I n, (f t + f (t + 1)) = 0
  rw [Finset.sum_add_distrib]
  have hshift : (∑ t : I n, f (t + 1)) = ∑ t : I n, f t := by
    simpa using (Equiv.sum_comp (Equiv.addRight (1 : I n)) f)
  rw [hshift]
  exact F_add_self _

private theorem scalarPOrbit_zero_of_mem_range
    {n : Nat} [NeZero n] (K : CyclicCube n)
    (hK : K ∈ LinearMap.range (cubeDiffPStar (n := n)))
    (s k : I n) :
    ∑ t : I n, scalarPOrbit K s k t = 0 := by
  rcases hK with ⟨lambda, rfl⟩
  let f : Profile n := fun t => lambda (s - t) t k
  change ∑ t : I n, cubeDiffPStar lambda (s - t) t k = 0
  simp only [EEOEInternal.cubeDiffPStar_apply]
  have hf (t : I n) :
      lambda (s - t - 1) (t + 1) k = f (t + 1) := by
    dsimp only [f]
    apply congrArg (fun x => lambda x (t + 1) k)
    abel
  simp_rw [hf]
  change ∑ t : I n, (f t + f (t + 1)) = 0
  rw [Finset.sum_add_distrib]
  have hshift : (∑ t : I n, f (t + 1)) = ∑ t : I n, f t := by
    simpa using (Equiv.sum_comp (Equiv.addRight (1 : I n)) f)
  rw [hshift]
  exact F_add_self _

noncomputable def k4ScalarBFreeSection
    {n : Nat} [NeZero n] :
    K4BFreeHeadRadical n →ₗ[F] CyclicCube n :=
  scalarRStarPrimitive.comp
    (k4ScalarKappaBCoeff.comp (K4BFreeHeadRadical n).subtype)

noncomputable def k4ScalarWFreeSection
    {n : Nat} [NeZero n] :
    K4WFreeHeadRadical n →ₗ[F] CyclicCube n :=
  scalarPStarPrimitive.comp
    (k4ScalarKappaWCoeff.comp (K4WFreeHeadRadical n).subtype)

theorem cubeDiffRStar_k4ScalarBFreeSection
    {n : Nat} [NeZero n] (B : K4BFreeHeadRadical n) :
    cubeDiffRStar (k4ScalarBFreeSection B) =
      k4ScalarKappaBCoeff B.1 := by
  apply scalarRStarPrimitive_rightInverse_of_orbit_zero
  exact fun i s => scalarROrbit_zero_of_mem_range _
    ((mem_ker_k4RHeadCross_iff_kappaBCoeff_mem_range_RStar B.1).mp B.2) i s

theorem cubeDiffPStar_k4ScalarWFreeSection
    {n : Nat} [NeZero n] (W : K4WFreeHeadRadical n) :
    cubeDiffPStar (k4ScalarWFreeSection W) =
      k4ScalarKappaWCoeff W.1 := by
  apply scalarPStarPrimitive_rightInverse_of_orbit_zero
  exact fun s k => scalarPOrbit_zero_of_mem_range _
    ((mem_ker_k4PHeadCross_flip_iff_kappaWCoeff_mem_range_PStar W.1).mp W.2) s k

/-! ## Public bridges to the literal source reads -/

theorem actualAddedBRead_pureBFree
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (B : K4BFreeHeadRadical n) :
    actualAddedBRead hn2 hn hb2 hc2 hd2 (pureBFree B) =
      cubeDiffJStar (k4ScalarBFreeSection B) := by
  funext i j k
  dsimp [actualAddedBRead, actualAddedOnly, scalarCoeffMap,
    pureBFree, k4ScalarBFreeSection, scalarRStarPrimitive,
    k4ScalarKappaBCoeff]
  abel_nf
  simp only [two_smul, EEEEInternal.module_add_self, zero_add]
  unfoldScalarMultiplierSections
  dsimp
  rw [EEOEInternal.cubeDiffJStar_apply]
  congr 2 <;> funext t <;> congr 3 <;> abel

theorem actualAddedWRead_pureWFree
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (W : K4WFreeHeadRadical n) :
    actualAddedWRead hn2 hn hb2 hc2 hd2 (pureWFree W) =
      cubeDiffJStar (k4ScalarWFreeSection W) := by
  funext i j k
  dsimp [actualAddedWRead, actualAddedOnly, scalarCoeffMap,
    pureWFree, k4ScalarWFreeSection, scalarPStarPrimitive,
    k4ScalarKappaWCoeff]
  abel_nf
  simp only [two_smul, EEEEInternal.module_add_self, zero_add]
  unfoldScalarMultiplierSections
  dsimp
  rw [EEOEInternal.cubeDiffJStar_apply]
  congr 2 <;> funext t <;> congr 3 <;> abel

/-! ## Free-head radical ranks -/

private theorem finrank_range_k4RHeadCross_local
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.range (k4RHeadCross (n := n))) =
      n * (n - 1) := by
  have htransport :=
    BWSymmetryInternal.rankTransport
      (k4RHeadCross (n := n))
      (TotalEEEERankInternal.freeToJKernelI (n := n))
      ((EEEEInternal.prShear (n := n)).trans (k4TR (n := n)))
      (k4RKerToJKernel (n := n))
      (by
        intro B W
        exact k4Kappa_rker_base_transport B W)
  exact htransport.symm.trans TotalEEEERankInternal.rank_freeToJKernelI

private theorem finrank_range_k4PHeadCross_flip_local
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (k4PHeadCross (n := n)).flip) =
      n * (n - 1) := by
  have htransport :=
    BWSymmetryInternal.rankTransport
      (k4PHeadCross (n := n)).flip
      (TotalEEEERankInternal.freeToJKernelK (n := n))
      ((EEEEInternal.prShear (n := n)).trans (k4TP (n := n)))
      (k4PKerToJKernel (n := n))
      (by
        intro W B
        exact k4Kappa_pker_base_transport B W)
  exact htransport.symm.trans TotalEEEERankInternal.rank_freeToJKernelK

private theorem freeHead_rank_arithmetic
    {n r : Nat} (hn : 0 < n)
    (h : n * (n - 1) + r = n ^ 3) :
    r = n ^ 3 - n ^ 2 + n := by
  have hmul : n * (n - 1) = n ^ 2 - n := by
    rw [Nat.mul_sub_left_distrib]
    simp [pow_two]
  have hn_sq : n ≤ n ^ 2 := by nlinarith
  have hsq_cube : n ^ 2 ≤ n ^ 3 := by nlinarith
  rw [hmul] at h
  omega

theorem finrank_K4BFreeHeadRadical
    {n : Nat} [NeZero n] :
    Module.finrank F (K4BFreeHeadRadical n) =
      n ^ 3 - n ^ 2 + n := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (k4RHeadCross (n := n))
  have hambient : Module.finrank F (CyclicCube n) = n ^ 3 := by
    simp [CyclicCube, Module.finrank_pi_fintype, I, ZMod.card,
      pow_succ, mul_assoc]
  rw [finrank_range_k4RHeadCross_local, hambient] at h
  exact freeHead_rank_arithmetic (NeZero.pos n) h

theorem finrank_K4WFreeHeadRadical
    {n : Nat} [NeZero n] :
    Module.finrank F (K4WFreeHeadRadical n) =
      n ^ 3 - n ^ 2 + n := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (k4PHeadCross (n := n)).flip
  have hambient : Module.finrank F (CyclicCube n) = n ^ 3 := by
    simp [CyclicCube, Module.finrank_pi_fintype, I, ZMod.card,
      pow_succ, mul_assoc]
  rw [finrank_range_k4PHeadCross_flip_local, hambient] at h
  exact freeHead_rank_arithmetic (NeZero.pos n) h

end


end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
