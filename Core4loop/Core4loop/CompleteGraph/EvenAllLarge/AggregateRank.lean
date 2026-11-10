import Core4loop.CompleteGraph.EvenAllLarge.AggregateCoordinates
import Core4loop.CompleteGraph.EvenAllLarge.KappaBaseTransport

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.CompleteGraph.CubeCompat
open Core4loop.CompleteGraph.EvenP.GPolarRankPrep

noncomputable section

attribute [local instance] Fintype.ofFinite

/-! ## R0: ambient kappa rank -/

private noncomputable def k4KappaCoeff
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n where
  toFun B := fun i j k => B i j k + B (i + 1) j (k - 1)
  map_add' B B' := by
    funext i j k
    simp only [Pi.add_apply]
    abel
  map_smul' r B := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add]

private theorem k4CubeKappa_eq_cubeDot_coeff
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappa B W = cubeDot (k4KappaCoeff B) W := by
  unfold k4CubeKappa cubeDot k4KappaCoeff
  change
    (∑ q : I n × I n × I n,
      (B q.1 q.2.1 q.2.2 * W q.1 q.2.1 q.2.2 +
        B (q.1 + 1) q.2.1 q.2.2 * W q.1 q.2.1 (q.2.2 + 1))) =
      ∑ q : I n × I n × I n,
        (B q.1 q.2.1 q.2.2 + B (q.1 + 1) q.2.1 (q.2.2 - 1)) *
          W q.1 q.2.1 q.2.2
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.refl (I n))
      (Equiv.prodCongr (Equiv.refl (I n)) (Equiv.addRight (1 : I n)))
  apply Fintype.sum_equiv e
  intro q
  simp [e]

private noncomputable def k4KappaIKShear
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun i j k => f i j (k - i)
  invFun g := fun i j k => g i j (k + i)
  left_inv f := by
    funext i j k
    simp only
    congr 3
    abel
  right_inv g := by
    funext i j k
    simp only
    congr 3
    abel
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem k4KappaIKShear_coeff
    {n : Nat} [NeZero n] (B : CyclicCube n) :
    k4KappaIKShear (k4KappaCoeff B) =
      cubeDiffI (k4KappaIKShear B) := by
  funext i j k
  rw [EEOEInternal.cubeDiffI_apply]
  change
    B i j (k - i) + B (i + 1) j ((k - i) - 1) =
      B i j (k - i) + B (i + 1) j (k - (i + 1))
  have hindex : (k - i) - 1 = k - (i + 1) := by abel
  rw [hindex]

private theorem cubeDot_k4KappaIKShear
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot (k4KappaIKShear X) (k4KappaIKShear Y) = cubeDot X Y := by
  unfold cubeDot k4KappaIKShear
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    { toFun := fun q => (q.1, q.2.1, q.2.2 + q.1)
      invFun := fun q => (q.1, q.2.1, q.2.2 - q.1)
      left_inv := by
        intro q
        rcases q with ⟨i, j, k⟩
        simp only [Prod.mk.injEq, true_and]
        abel
      right_inv := by
        intro q
        rcases q with ⟨i, j, k⟩
        simp only [Prod.mk.injEq, true_and]
        abel }
  symm
  apply Fintype.sum_equiv e
  intro q
  simp [e]

theorem finrank_range_k4CubeKappaLinear
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (k4CubeKappaLinear (n := n))) =
      n ^ 2 * (n - 1) := by
  have htransport :
      Module.finrank F
          (LinearMap.range (diamondTailSingleICross (n := n))) =
        Module.finrank F
          (LinearMap.range (k4CubeKappaLinear (n := n))) :=
    BWSymmetryInternal.rankTransport
      (k4CubeKappaLinear (n := n))
      (diamondTailSingleICross (n := n))
      (k4KappaIKShear (n := n))
      (k4KappaIKShear (n := n))
      (by
        intro B W
        change cubeDot (cubeDiffI (k4KappaIKShear B))
            (k4KappaIKShear W) = k4CubeKappa B W
        rw [← k4KappaIKShear_coeff]
        rw [cubeDot_k4KappaIKShear]
        exact (k4CubeKappa_eq_cubeDot_coeff B W).symm)
  exact htransport.symm.trans rank_diamondTailSingleICross

/-! ## R1: the two restricted pointed-coordinate equivalences -/

private abbrev K4BAggregateCoords
    (n c : Nat) [NeZero n] :=
  ((LinearMap.ker (cubeDiffP (n := n))) × CyclicCube n) ×
    DiamondEvenAxisValueTailZero n c (CyclicCube n)

private abbrev K4WAggregateCoords
    (n c : Nat) [NeZero n] :=
  (CyclicCube n × LinearMap.ker (cubeDiffR (n := n))) ×
    DiamondEvenAxisValueTailZero n c (CyclicCube n)

private noncomputable def k4BAggregateCoordEquiv
    {n c : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) :
    K4BAggregateLeft n c ≃ₗ[F] K4BAggregateCoords n c where
  toFun B :=
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let x := E B.1
    ((⟨x.1.1, by
        have hB := LinearMap.mem_ker.mp B.2
        rw [k4BAggregateConstraint_apply] at hB
        simpa only [k4AggregatePDiff,
          pointedSrcEvenValueEquiv_apply_sigma] using hB⟩,
      x.1.2), x.2)
  invFun x :=
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let y : PointedEvenValueCoords
        (PVec n c) (CyclicCube n) (zeroVec : PVec n c) :=
      ((x.1.1.1, x.1.2), x.2)
    ⟨E.symm y, by
      apply LinearMap.mem_ker.mpr
      rw [k4BAggregateConstraint_apply]
      change cubeDiffP (∑ zt, E.symm y zt) = 0
      have hsum : (∑ zt, E.symm y zt) = x.1.1.1 := by
        rw [← pointedSrcEvenValueEquiv_apply_sigma
          (zeroVec : PVec n c) (even_card_PVec hn hc2)]
        change (E (E.symm y)).1.1 = x.1.1.1
        rw [E.apply_symm_apply]
      rw [hsum]
      exact x.1.1.2⟩
  left_inv B := by
    apply Subtype.ext
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    apply E.injective
    change E (E.symm (((E B.1).1.1, (E B.1).1.2), (E B.1).2)) = E B.1
    rw [E.apply_symm_apply]
  right_inv x := by
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let y : PointedEvenValueCoords
        (PVec n c) (CyclicCube n) (zeroVec : PVec n c) :=
      ((x.1.1.1, x.1.2), x.2)
    have h := E.apply_symm_apply y
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun z => z.1.1) h
      · exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h
  map_add' B B' := by
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    have h := E.map_add B.1 B'.1
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun z => z.1.1) h
      · exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h
  map_smul' r B := by
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    have h := E.map_smul r B.1
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun z => z.1.1) h
      · exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h

private noncomputable def k4WAggregateCoordEquiv
    {n c : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) :
    K4WAggregateLeft n c ≃ₗ[F] K4WAggregateCoords n c where
  toFun W :=
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let y := E W.1
    ((y.1.1, ⟨y.1.2, by
        have hW := LinearMap.mem_ker.mp W.2
        rw [k4WAggregateConstraint_apply] at hW
        rw [TotalEEEERightInternal.axisDualHead_eq_totalSum
          (CyclicCube n) hn hc2 W.1]
        simpa only [k4AggregateRDiff] using hW⟩), y.2)
  invFun x :=
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let y : PointedEvenValueCoords
        (PVec n c) (CyclicCube n) (zeroVec : PVec n c) :=
      ((x.1.1, x.1.2.1), x.2)
    ⟨E.symm y, by
      apply LinearMap.mem_ker.mpr
      rw [k4WAggregateConstraint_apply]
      change cubeDiffR (∑ zt, E.symm y zt) = 0
      have hsum := TotalEEEERightInternal.axisDualHead_eq_totalSum
        (CyclicCube n) hn hc2 (E.symm y)
      change (E (E.symm y)).1.2 = (∑ zt, E.symm y zt) at hsum
      rw [E.apply_symm_apply] at hsum
      rw [← hsum]
      exact x.1.2.2⟩
  left_inv W := by
    apply Subtype.ext
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    apply E.injective
    change E (E.symm (((E W.1).1.1, (E W.1).1.2), (E W.1).2)) = E W.1
    rw [E.apply_symm_apply]
  right_inv x := by
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let y : PointedEvenValueCoords
        (PVec n c) (CyclicCube n) (zeroVec : PVec n c) :=
      ((x.1.1, x.1.2.1), x.2)
    have h := E.apply_symm_apply y
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z => z.1.1) h
      · apply Subtype.ext
        exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h
  map_add' W W' := by
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    have h := E.map_add W.1 W'.1
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z => z.1.1) h
      · apply Subtype.ext
        exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h
  map_smul' r W := by
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    have h := E.map_smul r W.1
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z => z.1.1) h
      · apply Subtype.ext
        exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h

/-! ## R2: the literal three-block aggregate model -/

private noncomputable def k4PBaseCross
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffP (n := n)) →ₗ[F]
      Module.Dual F (CyclicCube n) :=
  (k4CubeKappaLinear (n := n)).comp
    (LinearMap.ker (cubeDiffP (n := n))).subtype

private noncomputable def k4RBaseCross
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F]
      Module.Dual F (LinearMap.ker (cubeDiffR (n := n))) :=
  (LinearMap.dualMap
      (LinearMap.ker (cubeDiffR (n := n))).subtype).comp
    (k4CubeKappaLinear (n := n))

@[simp] private theorem k4PBaseCross_apply
    {n : Nat} [NeZero n]
    (B : LinearMap.ker (cubeDiffP (n := n)))
    (W : CyclicCube n) :
    k4PBaseCross B W = k4CubeKappa B.1 W := rfl

@[simp] private theorem k4RBaseCross_apply
    {n : Nat} [NeZero n]
    (B : CyclicCube n)
    (W : LinearMap.ker (cubeDiffR (n := n))) :
    k4RBaseCross B W = k4CubeKappa B W.1 := rfl

private noncomputable def k4AggregateCrossModel
    {n c : Nat} [NeZero n] :
    K4BAggregateCoords n c →ₗ[F]
      Module.Dual F (K4WAggregateCoords n c) :=
  diamondCrossProd
    (diamondCrossProd
      (k4PBaseCross (n := n))
      (k4RBaseCross (n := n)))
    (diamondTailAmplify
      (n := n) (k := c) (k4CubeKappaLinear (n := n)))

private theorem k4AggregateCrossModel_phase
    {n c : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c)
    (B : K4BAggregateLeft n c)
    (W : K4WAggregateLeft n c) :
    k4AggregateCrossModel
        (k4BAggregateCoordEquiv hn hc2 B)
        (k4WAggregateCoordEquiv hn hc2 W) =
      k4ZAggregateCross B W := by
  let x := diamondEvenAxisSrcCoordEquiv
    (n := n) (k := c) (CyclicCube n) hn hc2 B.1
  let y := diamondEvenAxisDualCoordEquiv
    (n := n) (k := c) (CyclicCube n) hn hc2 W.1
  change
    (k4CubeKappa x.1.1 y.1.1 +
        k4CubeKappa x.1.2 y.1.2) +
      (∑ t, k4CubeKappa (x.2.1 t) (y.2.1 t)) =
        k4AggregateKappaScalar B.1 W.1
  rw [k4AggregateKappaScalar]
  exact (pointedEvenValue_pairing
    (zeroVec : PVec n c) (even_card_PVec hn hc2)
    (k4CubeKappaLinear (n := n)) B.1 W.1).symm

/-! ## R3: owner-local rectangular hyperbolic rank -/

private noncomputable def k4OwnerCrossPolar
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V) :
    (U × V) →ₗ[F] Module.Dual F (U × V) where
  toFun x :=
    { toFun := fun y => L x.1 y.2 + L y.1 x.2
      map_add' := by
        intro y z
        simp only [Prod.fst_add, Prod.snd_add, map_add,
          LinearMap.add_apply]
        abel
      map_smul' := by
        intro r y
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul,
          RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul]
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simp only [Prod.fst_add, Prod.snd_add, map_add,
      LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    abel
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul,
      LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk]
    ring

@[simp] private theorem k4OwnerCrossPolar_apply
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V)
    (x y : U × V) :
    k4OwnerCrossPolar L x y =
      L x.1 y.2 + L y.1 x.2 := rfl

private theorem k4OwnerCrossPolar_mem_ker_iff
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V)
    (x : U × V) :
    x ∈ LinearMap.ker (k4OwnerCrossPolar L) ↔
      x.1 ∈ LinearMap.ker L ∧
        x.2 ∈ LinearMap.ker L.flip := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    constructor
    · rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro v
      have hpoint := LinearMap.congr_fun hx (0, v)
      simpa [k4OwnerCrossPolar_apply] using hpoint
    · rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro u
      have hpoint := LinearMap.congr_fun hx (u, 0)
      simpa [k4OwnerCrossPolar_apply] using hpoint
  · rintro ⟨hu, hv⟩
    apply LinearMap.ext
    intro y
    rw [k4OwnerCrossPolar_apply]
    have hu0 := LinearMap.mem_ker.mp hu
    have hv0 := LinearMap.mem_ker.mp hv
    rw [LinearMap.congr_fun hu0 y.2]
    change 0 + L.flip x.2 y.1 = 0
    rw [LinearMap.congr_fun hv0 y.1]
    simp

private noncomputable def k4OwnerCrossPolarKerEquiv
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V) :
    LinearMap.ker (k4OwnerCrossPolar L) ≃ₗ[F]
      LinearMap.ker L × LinearMap.ker L.flip where
  toFun x :=
    (⟨x.1.1,
        (k4OwnerCrossPolar_mem_ker_iff L x.1).mp x.2 |>.1⟩,
      ⟨x.1.2,
        (k4OwnerCrossPolar_mem_ker_iff L x.1).mp x.2 |>.2⟩)
  invFun x :=
    ⟨(x.1.1, x.2.1),
      (k4OwnerCrossPolar_mem_ker_iff
        L (x.1.1, x.2.1)).mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    ext <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem k4Owner_finrank_range_flip
    {U V : Type*}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (L : U →ₗ[F] Module.Dual F V) :
    Module.finrank F (LinearMap.range L.flip) =
      Module.finrank F (LinearMap.range L) := by
  change
    Module.finrank F
        (LinearMap.range
          (L.dualMap.comp
            (Module.evalEquiv F V).toLinearMap)) =
      Module.finrank F (LinearMap.range L)
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (Module.evalEquiv F V))]
  exact LinearMap.finrank_range_dualMap_eq_finrank_range L

private theorem k4Owner_finrank_ker_crossPolar
    {U V : Type*}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (L : U →ₗ[F] Module.Dual F V) :
    Module.finrank F (LinearMap.ker (k4OwnerCrossPolar L)) =
      Module.finrank F (LinearMap.ker L) +
        Module.finrank F (LinearMap.ker L.flip) := by
  rw [LinearEquiv.finrank_eq (k4OwnerCrossPolarKerEquiv L),
    Module.finrank_prod]

private theorem k4Owner_finrank_range_crossPolar
    {U V : Type*}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (L : U →ₗ[F] Module.Dual F V) :
    Module.finrank F (LinearMap.range (k4OwnerCrossPolar L)) =
      2 * Module.finrank F (LinearMap.range L) := by
  have hpolar :=
    LinearMap.finrank_range_add_finrank_ker (k4OwnerCrossPolar L)
  have hleft := LinearMap.finrank_range_add_finrank_ker L
  have hright := LinearMap.finrank_range_add_finrank_ker L.flip
  rw [k4Owner_finrank_ker_crossPolar,
    Module.finrank_prod] at hpolar
  rw [k4Owner_finrank_range_flip L] at hright
  omega

/-! ## R4: base, tail, and half-cross ranks -/

private theorem finrank_range_k4PBaseCross
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.range (k4PBaseCross (n := n))) =
      n * (n - 1) := by
  have htransport :=
    BWSymmetryInternal.rankTransport
      (k4PBaseCross (n := n))
      (TotalEEEERankInternal.freeToJKernelK (n := n)).flip
      (k4PKerToJKernel (n := n))
      ((EEEEInternal.prShear (n := n)).trans (k4TP (n := n)))
      (by
        intro B W
        exact k4Kappa_pker_base_transport B W)
  calc
    Module.finrank F (LinearMap.range (k4PBaseCross (n := n))) =
        Module.finrank F
          (LinearMap.range
            (TotalEEEERankInternal.freeToJKernelK (n := n)).flip) :=
      htransport.symm
    _ = Module.finrank F
          (LinearMap.range
            (TotalEEEERankInternal.freeToJKernelK (n := n))) :=
      k4Owner_finrank_range_flip
        (TotalEEEERankInternal.freeToJKernelK (n := n))
    _ = n * (n - 1) := TotalEEEERankInternal.rank_freeToJKernelK

private theorem finrank_range_k4RBaseCross
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.range (k4RBaseCross (n := n))) =
      n * (n - 1) := by
  have htransport :=
    BWSymmetryInternal.rankTransport
      (k4RBaseCross (n := n))
      (TotalEEEERankInternal.freeToJKernelI (n := n))
      ((EEEEInternal.prShear (n := n)).trans (k4TR (n := n)))
      (k4RKerToJKernel (n := n))
      (by
        intro B W
        exact k4Kappa_rker_base_transport B W)
  exact htransport.symm.trans TotalEEEERankInternal.rank_freeToJKernelI

private theorem finrank_range_k4AggregateTailCross
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    Module.finrank F
        (LinearMap.range
          (diamondTailAmplify
            (n := n) (k := c) (k4CubeKappaLinear (n := n)))) =
      (n ^ (c - 1) - 2) * (n ^ 2 * (n - 1)) := by
  rw [finrank_range_diamondTailAmplify hn2 hn hc2,
    finrank_diamondEvenAxisTailZero hn2 hn hc2,
    finrank_range_k4CubeKappaLinear]

private theorem k4AggregateRank_nat_identity
    {n c : Nat} (hn2 : 2 ≤ n) (hc2 : 2 ≤ c) :
    (n ^ (c - 1) - 2) * n ^ 2 * (n - 1) +
        n * (n - 1) + n * (n - 1) =
      n * (n - 1) * (n ^ c - 2 * (n - 1)) := by
  have hq2 : 2 ≤ n ^ (c - 1) := by
    have hcpos : 0 < c - 1 := by omega
    exact hn2.trans (Nat.le_pow hcpos)
  have hc : c = (c - 1) + 1 := by omega
  have hpow : n ^ c = n * n ^ (c - 1) := by
    calc
      n ^ c = n ^ ((c - 1) + 1) := congrArg (n ^ ·) hc
      _ = n ^ (c - 1) * n := pow_succ n (c - 1)
      _ = n * n ^ (c - 1) := Nat.mul_comm _ _
  have hsubq : n ^ (c - 1) - 2 + 2 = n ^ (c - 1) := by omega
  have hsafety : 2 * (n - 1) ≤ n ^ c := by
    calc
      2 * (n - 1) ≤ 2 * n :=
        Nat.mul_le_mul_left 2 (Nat.sub_le n 1)
      _ = n * 2 := by ring
      _ ≤ n * n ^ (c - 1) := Nat.mul_le_mul_left n hq2
      _ = n ^ c := hpow.symm
  have htarget :
      n ^ c - 2 * (n - 1) = n * (n ^ (c - 1) - 2) + 2 := by
    have htwo : n * 2 = 2 + 2 * (n - 1) := by omega
    apply Nat.sub_eq_iff_eq_add hsafety |>.2
    rw [hpow]
    calc
      n * n ^ (c - 1) = n * ((n ^ (c - 1) - 2) + 2) := by
        rw [hsubq]
      _ = n * (n ^ (c - 1) - 2) + 2 + 2 * (n - 1) := by
        rw [Nat.mul_add, htwo]
        omega
  rw [htarget]
  ring

private theorem finrank_range_k4AggregateCrossModel
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    Module.finrank F
        (LinearMap.range (k4AggregateCrossModel (n := n) (c := c))) =
      n * (n - 1) * (n ^ c - 2 * (n - 1)) := by
  change
    Module.finrank F
        (LinearMap.range
          (diamondCrossProd
            (diamondCrossProd
              (k4PBaseCross (n := n))
              (k4RBaseCross (n := n)))
            (diamondTailAmplify
              (n := n) (k := c) (k4CubeKappaLinear (n := n))))) = _
  rw [finrank_range_diamondCrossProd,
    finrank_range_diamondCrossProd,
    finrank_range_k4PBaseCross,
    finrank_range_k4RBaseCross,
    finrank_range_k4AggregateTailCross hn2 hn hc2]
  have h := k4AggregateRank_nat_identity hn2 hc2
  calc
    n * (n - 1) + n * (n - 1) +
          (n ^ (c - 1) - 2) * (n ^ 2 * (n - 1)) =
        (n ^ (c - 1) - 2) * n ^ 2 * (n - 1) +
          n * (n - 1) + n * (n - 1) := by ring
    _ = n * (n - 1) * (n ^ c - 2 * (n - 1)) := h

theorem finrank_range_k4ZAggregateCross
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    Module.finrank F
        (LinearMap.range (k4ZAggregateCross (n := n) (c := c))) =
      n * (n - 1) * (n ^ c - 2 * (n - 1)) := by
  have htransport :=
    BWSymmetryInternal.rankTransport
      (k4ZAggregateCross (n := n) (c := c))
      (k4AggregateCrossModel (n := n) (c := c))
      (k4BAggregateCoordEquiv hn hc2)
      (k4WAggregateCoordEquiv hn hc2)
      (k4AggregateCrossModel_phase hn hc2)
  exact htransport.symm.trans
    (finrank_range_k4AggregateCrossModel hn2 hn hc2)

/-! ## R5: hyperbolic doubling -/

private theorem k4AggregateHyperbolicPolar_eq_ownerCrossPolar
    {n c : Nat} [NeZero n] :
    k4AggregateHyperbolicPolar (n := n) (c := c) =
      k4OwnerCrossPolar (k4ZAggregateCross (n := n) (c := c)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

theorem finrank_range_k4AggregateHyperbolicPolar
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    Module.finrank F
        (LinearMap.range
          (k4AggregateHyperbolicPolar (n := n) (c := c))) =
      2 * (n * (n - 1) * (n ^ c - 2 * (n - 1))) := by
  rw [k4AggregateHyperbolicPolar_eq_ownerCrossPolar,
    k4Owner_finrank_range_crossPolar,
    finrank_range_k4ZAggregateCross hn2 hn hc2]

/-! ## R6-R7: transport to the literal K4 source -/

private theorem finrank_range_k4EvenPGPolar_eq_aggregateHyperbolic
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (k4EvenPGPolar (n := n) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.range
          (k4AggregateHyperbolicPolar (n := n) (c := c))) := by
  let A := k4EvenPAggregate hn hb2 hc hd2
  let H := k4AggregateHyperbolicPolar (n := n) (c := c)
  have hA : Function.Surjective A :=
    k4EvenPAggregate_surjective hn hb2 hc hd2
  have hdual : Function.Injective A.dualMap :=
    LinearMap.dualMap_injective_of_surjective hA
  have hright : LinearMap.range (H.comp A) = LinearMap.range H := by
    exact LinearMap.range_comp_of_range_eq_top H
      (LinearMap.range_eq_top.mpr hA)
  have hleft := LinearEquiv.finrank_eq
    (TotalEEEERankInternal.rangeCompEquivOfInjective
      (H.comp A) A.dualMap hdual)
  have hrightFin :
      Module.finrank F (LinearMap.range (H.comp A)) =
        Module.finrank F (LinearMap.range H) := by
    rw [hright]
  rw [k4EvenPGPolar_factor_through_aggregate hn hb2 hc hd2]
  exact hleft.symm.trans (by
    simpa only [H] using hrightFin)

theorem finrank_range_k4EvenPGPolar
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (k4EvenPGPolar (n := n) (b := b) (c := c) (d := d))) =
      2 * (n * (n - 1) * (n ^ c - 2 * (n - 1))) := by
  rw [finrank_range_k4EvenPGPolar_eq_aggregateHyperbolic
    hn hb2 (by omega : 0 < c) hd2]
  exact finrank_range_k4AggregateHyperbolicPolar hn2 hn hc2

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
