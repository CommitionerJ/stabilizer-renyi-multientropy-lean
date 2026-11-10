import Core4loop.SquareDiagonal.DirectWitt.OddScalarWitt
import Core4loop.QuadraticSignSum

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

noncomputable section

attribute [local instance] Fintype.ofFinite

/-- The actual polar map of `diamondOddScalarQ`, expressed through the
surjective odd-scalar Witt quotient. -/
noncomputable def diamondOddScalarPolarMap
    {n : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddScalarSource n →ₗ[F]
      Module.Dual F (DiamondOddScalarSource n) where
  toFun x :=
    { toFun := fun y =>
        (diamondOddScalarWittMap hn x).2
            (diamondOddScalarWittMap hn y).1 +
          (diamondOddScalarWittMap hn y).2
            (diamondOddScalarWittMap hn x).1
      map_add' := by
        intro y z
        simp only [map_add, Prod.fst_add, Prod.snd_add,
          LinearMap.add_apply]
        ring
      map_smul' := by
        intro r y
        simp only [map_smul, Prod.smul_fst, Prod.smul_snd,
          LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simp only [map_add, Prod.fst_add, Prod.snd_add,
      LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    abel
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd,
      LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk]
    ring

/-- The true radical of the odd-scalar quadratic phase. -/
abbrev DiamondOddScalarTrueRadical
    {n : Nat} [NeZero n] (hn : Odd n) :=
  LinearMap.ker (diamondOddScalarPolarMap hn)

private theorem diamondOddHighFreqPairing_comm
    {n : Nat} [NeZero n]
    (X Y : DiamondOddHighFreq n) :
    oddHighFreqPairing X Y = oddHighFreqPairing Y X := by
  simp only [oddHighFreqPairing_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- The displayed linear map is the actual polar map of the odd-scalar
quadratic phase. -/
theorem diamondOddScalarPolarMap_apply
    {n : Nat} [NeZero n] (hn : Odd n)
    (x y : DiamondOddScalarSource n) :
    diamondOddScalarPolarMap hn x y =
      diamondOddScalarQ (x + y) +
      diamondOddScalarQ x +
      diamondOddScalarQ y := by
  rw [← diamondOddScalarWittMap_phase hn (x + y),
    ← diamondOddScalarWittMap_phase hn x,
    ← diamondOddScalarWittMap_phase hn y]
  simp only [diamondOddScalarPolarMap, LinearMap.coe_mk, AddHom.coe_mk,
    map_add, Prod.fst_add, Prod.snd_add, diamondOddScalarWittCoreQ,
    LinearMap.add_apply]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

private theorem diamondOddScalarQ_add
    {n : Nat} [NeZero n] (hn : Odd n)
    (x y : DiamondOddScalarSource n) :
    diamondOddScalarQ (x + y) =
      diamondOddScalarQ x + diamondOddScalarQ y +
        diamondOddScalarPolarMap hn x y := by
  rw [diamondOddScalarPolarMap_apply]
  rw [show
    diamondOddScalarQ x + diamondOddScalarQ y +
        (diamondOddScalarQ (x + y) +
          diamondOddScalarQ x + diamondOddScalarQ y) =
      diamondOddScalarQ (x + y) +
        (diamondOddScalarQ x + diamondOddScalarQ x) +
        (diamondOddScalarQ y + diamondOddScalarQ y) by abel,
    F_add_self, F_add_self, add_zero, add_zero]

/-- The kernel of the source-compatible Witt map is exactly the true
radical of the odd-scalar phase. -/
theorem ker_diamondOddScalarWittMap_eq_trueRadical
    {n : Nat} [NeZero n] (hn : Odd n) :
    LinearMap.ker (diamondOddScalarWittMap (n := n) hn) =
      DiamondOddScalarTrueRadical hn := by
  ext x
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    have hmap :
        diamondOddScalarWittMap hn x = 0 :=
      LinearMap.mem_ker.mp hx
    simp only [diamondOddScalarPolarMap, LinearMap.coe_mk, AddHom.coe_mk,
      hmap, Prod.fst_zero, Prod.snd_zero, LinearMap.zero_apply,
      map_zero, zero_add]
  · intro hx
    have hpolar :
        diamondOddScalarPolarMap hn x = 0 :=
      LinearMap.mem_ker.mp hx
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · have hleft :
          ∀ H : DiamondOddHighFreq n,
            oddHighFreqPairing H
                (diamondOddScalarWittMap hn x).1 = 0 := by
        intro H
        rcases diamondOddScalarWittMap_surjective hn
            (0, oddHighFreqPairing H) with ⟨y, hy⟩
        have happ :=
          congrArg
            (fun L : Module.Dual F (DiamondOddScalarSource n) => L y)
            hpolar
        simpa only [diamondOddScalarPolarMap, LinearMap.coe_mk,
          AddHom.coe_mk, hy, Prod.fst_zero, Prod.snd_zero,
          LinearMap.zero_apply, map_zero, zero_add, add_zero] using happ
      have hpair :
          oddHighFreqPairing
              (diamondOddScalarWittMap hn x).1 = 0 := by
        apply LinearMap.ext
        intro H
        rw [diamondOddHighFreqPairing_comm]
        exact hleft H
      have hinj : Function.Injective
          (oddHighFreqPairing (n := n)) :=
        LinearMap.ker_eq_bot.mp (ker_oddHighFreqPairing hn)
      apply hinj
      simpa using hpair
    · apply LinearMap.ext
      intro H
      rcases diamondOddScalarWittMap_surjective hn
          (H, 0) with ⟨y, hy⟩
      have happ :=
        congrArg
          (fun L : Module.Dual F (DiamondOddScalarSource n) => L y)
          hpolar
      simpa only [diamondOddScalarPolarMap, LinearMap.coe_mk,
        AddHom.coe_mk, hy, Prod.fst_zero, Prod.snd_zero,
        LinearMap.zero_apply, map_zero, zero_add, add_zero] using happ

/-- The odd-scalar quadratic phase vanishes on its true radical. -/
theorem diamondOddScalarQ_eq_zero_of_mem_trueRadical
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarTrueRadical hn) :
    diamondOddScalarQ x.1 = 0 := by
  have hxker :
      x.1 ∈ LinearMap.ker
        (diamondOddScalarWittMap (n := n) hn) := by
    rw [ker_diamondOddScalarWittMap_eq_trueRadical hn]
    exact x.2
  rw [← diamondOddScalarWittMap_phase hn x.1,
    LinearMap.mem_ker.mp hxker]
  rfl

private theorem diamondOddScalarHighX_surjective
    {n : Nat} [NeZero n] (hn : Odd n) :
    Function.Surjective (diamondOddScalarHighX (n := n) hn) := by
  intro H
  rcases diamondOddScalarWittMap_surjective hn
      (H, 0) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa [diamondOddScalarWittMap_apply] using congrArg Prod.fst hx

private abbrev DiamondOddScalarLagrangian
    {n : Nat} [NeZero n] (hn : Odd n) :=
  LinearMap.ker (diamondOddScalarHighX (n := n) hn)

private theorem diamondOddScalarLagrangian_q_zero
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarLagrangian hn) :
    diamondOddScalarQ x.1 = 0 := by
  rw [← diamondOddScalarWittMap_phase hn x.1,
    diamondOddScalarWittMap_apply]
  change
    oddHighFreqPairing (diamondOddScalarHighY hn x.1)
      (diamondOddScalarHighX hn x.1) = 0
  rw [LinearMap.mem_ker.mp x.2, map_zero]

private theorem diamondOddScalarLagrangian_selfDual
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarSource n) :
    ((diamondOddScalarPolarMap hn x).comp
        (DiamondOddScalarLagrangian hn).subtype = 0 ↔
      x ∈ DiamondOddScalarLagrangian hn) := by
  have hinj : Function.Injective
      (oddHighFreqPairing (n := n)) :=
    LinearMap.ker_eq_bot.mp (ker_oddHighFreqPairing hn)
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    apply hinj
    apply LinearMap.ext
    intro H
    rcases diamondOddScalarWittMap_surjective hn
        (0, oddHighFreqPairing H) with ⟨y, hy⟩
    have hyL : y ∈ DiamondOddScalarLagrangian hn := by
      apply LinearMap.mem_ker.mpr
      simpa [diamondOddScalarWittMap_apply] using congrArg Prod.fst hy
    have happ :=
      congrArg
        (fun T : Module.Dual F (DiamondOddScalarLagrangian hn) =>
          T ⟨y, hyL⟩)
        hx
    rw [diamondOddHighFreqPairing_comm]
    simpa only [diamondOddScalarPolarMap, LinearMap.comp_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_subtype, hy,
      Prod.fst_zero, Prod.snd_zero, LinearMap.zero_apply,
      map_zero, zero_add, add_zero] using happ
  · intro hx
    apply LinearMap.ext
    intro y
    have hxX :
        diamondOddScalarHighX hn x = 0 :=
      LinearMap.mem_ker.mp hx
    have hyX :
        diamondOddScalarHighX hn y.1 = 0 :=
      LinearMap.mem_ker.mp y.2
    simp [diamondOddScalarPolarMap, diamondOddScalarWittMap_apply, hxX, hyX]

private theorem finrank_diamondOddScalarLagrangian
    {n : Nat} [NeZero n] (hn : Odd n) :
    Module.finrank F (DiamondOddScalarLagrangian hn) =
      Module.finrank F
          (LinearMap.ker
            (diamondOddScalarWittMap (n := n) hn)) +
        n * (n - 1) ^ 2 := by
  have hX :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondOddScalarHighX (n := n) hn)
  have hW :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondOddScalarWittMap (n := n) hn)
  have hXtop :
      LinearMap.range
        (diamondOddScalarHighX (n := n) hn) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (diamondOddScalarHighX_surjective hn)
  have hWtop :
      LinearMap.range
        (diamondOddScalarWittMap (n := n) hn) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (diamondOddScalarWittMap_surjective hn)
  rw [hXtop, finrank_top, finrank_DiamondOddHighFreq] at hX
  rw [hWtop, finrank_top, Module.finrank_prod,
    Subspace.dual_finrank_eq, finrank_DiamondOddHighFreq] at hW
  change
    Module.finrank F
        (LinearMap.ker
          (diamondOddScalarHighX (n := n) hn)) =
      Module.finrank F
          (LinearMap.ker
            (diamondOddScalarWittMap (n := n) hn)) +
        n * (n - 1) ^ 2
  omega

/-- The actual polar rank is twice the odd high-frequency dimension. -/
theorem finrank_range_diamondOddScalarPolarMap
    {n : Nat} [NeZero n] (hn : Odd n) :
    Module.finrank F
        (LinearMap.range (diamondOddScalarPolarMap hn)) =
      2 * (n * (n - 1) ^ 2) := by
  have hP :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondOddScalarPolarMap hn)
  have hW :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondOddScalarWittMap (n := n) hn)
  have hWtop :
      LinearMap.range
        (diamondOddScalarWittMap (n := n) hn) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (diamondOddScalarWittMap_surjective hn)
  have hker :=
    ker_diamondOddScalarWittMap_eq_trueRadical hn
  change
    LinearMap.ker
        (diamondOddScalarWittMap (n := n) hn) =
      LinearMap.ker (diamondOddScalarPolarMap hn) at hker
  rw [← hker] at hP
  rw [hWtop, finrank_top, Module.finrank_prod,
    Subspace.dual_finrank_eq, finrank_DiamondOddHighFreq] at hW
  omega

/-- Exact positive odd-scalar signed sum, with the exponent retained in the
additive kernel-plus-high-frequency form used downstream. -/
theorem sum_bitSign_diamondOddScalarQ_eq_pow
    {n : Nat} [NeZero n] (hn : Odd n) :
    (∑ x : DiamondOddScalarSource n,
        bitSign (diamondOddScalarQ x)) =
      (2 : Int) ^
        (Module.finrank F
            (LinearMap.ker
              (diamondOddScalarWittMap (n := n) hn)) +
          n * (n - 1) ^ 2) := by
  calc
    (∑ x : DiamondOddScalarSource n,
        bitSign (diamondOddScalarQ x)) =
        (2 : Int) ^
          Module.finrank F (DiamondOddScalarLagrangian hn) := by
      exact
        sum_bitSign_eq_pow_finrank_of_selfDual_isotropic
          (q := diamondOddScalarQ)
          (polar := diamondOddScalarPolarMap hn)
          (hq_add := diamondOddScalarQ_add hn)
          (L := DiamondOddScalarLagrangian hn)
          (hq_zero := diamondOddScalarLagrangian_q_zero hn)
          (hself := diamondOddScalarLagrangian_selfDual hn)
    _ = (2 : Int) ^
        (Module.finrank F
            (LinearMap.ker
              (diamondOddScalarWittMap (n := n) hn)) +
          n * (n - 1) ^ 2) := by
      rw [finrank_diamondOddScalarLagrangian hn]

end

end Core4loop.SquareDiagonal.DirectWitt
