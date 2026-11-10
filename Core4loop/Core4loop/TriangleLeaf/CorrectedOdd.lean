/-
# Triangle-plus-leaf: corrected odd branch

This module evaluates the exact compatible residual for odd replica count and
then assembles the logical-level-7 raw `DeltaNF = 2^X` theorem.  It does not
use proper-support, Gamma, catalogue, or universal-assembly results.
-/

import Core4loop.TriangleLeaf.CompatibleResidualBReadFiber
import Core4loop.TriangleLeaf.BReadOddClosed
import Core4loop.TriangleLeaf.BReadTailMaps
import Core4loop.TriangleLeaf.VisibleClosed
import Core4loop.TriangleLeaf.LeafProfileKernelSplitDims
import Core4loop.ZeroSumSpaces.ProfileMRange
import Core4loop.TriangleLeaf.AfterWResidual
import Core4loop.TriangleLeaf.CorrectedExponent

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-- The explicit dimension of one leaf-profile kernel in index/difference
coordinates.  This is kept local to the odd-route scratch audit. -/
private def oddBReadProfileRankNat (n a d : ℕ) : ℕ :=
  (n ^ d - (n - 1)) * (n ^ (a - 1) - 1)
    + n ^ (a - 1) * (n - 1)

private theorem kCdCvElimExpNat_eq_oddBReadProfileRank_mul
    {n a b d : ℕ} (ha : 0 < a) :
    kCdCvElimExpNat n a b d =
      n ^ (b + 1) * oddBReadProfileRankNat n a d := by
  have hab : a + b = (a - 1) + (b + 1) := by omega
  unfold kCdCvElimExpNat oddBReadProfileRankNat
  rw [hab, Nat.pow_add, Nat.pow_add]
  ring

private theorem intToNat_leafProfileSplit_eq_oddBReadProfileRankNat
    {n a d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    Int.toNat (LeafProfileDimZ a d n - PassiveVisibleDimZ d n) =
      oddBReadProfileRankNat n a d := by
  rw [intToNat_leafProfileKernelDim_eq_finrank
    (n := n) (a := a) (d := d) ha hd]
  exact finrank_LeafProfileKernel_explicit (n := n) (a := a) (d := d) hd

private theorem finrank_leafBProfileKernelIndexDiffCoord
    {n a c d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (LeafBProfileKernelIndexDiffCoord n a c d hd) =
      n ^ (c + 1) * oddBReadProfileRankNat n a d := by
  calc
    Module.finrank F (LeafBProfileKernelIndexDiffCoord n a c d hd)
        =
        Module.finrank F (I n → ZVec n c → LeafProfileKernel n a d) := by
          exact (LinearEquiv.finrank_eq
            (leafBProfileKernelCoordEquivIndexDiff
              (n := n) (a := a) (c := c) (d := d) hd)).symm
    _ =
        Fintype.card (I n) * Fintype.card (ZVec n c) *
          Module.finrank F (LeafProfileKernel n a d) := by
          simp [Module.finrank_pi_fintype, Nat.mul_assoc]
    _ = n ^ (c + 1) * oddBReadProfileRankNat n a d := by
          rw [finrank_LeafProfileKernel_explicit
            (n := n) (a := a) (d := d) hd]
          have hI : Fintype.card (I n) = n := by
            simp [I, ZMod.card]
          have hZ : Fintype.card (ZVec n c) = n ^ c := by
            exact card_vec n c
          rw [hI, hZ]
          change
            n * n ^ c *
                ((n ^ d - (n - 1)) * (n ^ (a - 1) - 1)
                  + n ^ (a - 1) * (n - 1))
              =
            n ^ (c + 1) * oddBReadProfileRankNat n a d
          rw [pow_succ]
          unfold oddBReadProfileRankNat
          ring

private theorem intCast_oddBReadProfileRankNat
    {n a d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    (oddBReadProfileRankNat n a d : ℤ) =
      LeafProfileDimZ a d n - PassiveVisibleDimZ d n := by
  calc
    (oddBReadProfileRankNat n a d : ℤ)
        =
        (Module.finrank F (LeafProfileKernel n a d) : ℤ) := by
          rw [finrank_LeafProfileKernel_explicit
            (n := n) (a := a) (d := d) hd]
          rfl
    _ = LeafProfileDimZ a d n - PassiveVisibleDimZ d n :=
      intCast_finrank_ker_leafSigmaQuot_eq
        (n := n) (a := a) (d := d) ha hd

private theorem intCast_oddBReadTailUnitNat
    {n b c : ℕ} [NeZero n] (hb : 0 < b) :
    (n * (n ^ b + n ^ c - (n - 1)) : ℕ) =
      LeafTailUnitZ b c n := by
  have hn1 : 1 ≤ n := one_le_of_neZero
  have hnb : n ≤ n ^ b := Nat.le_pow hb
  have hle : n - 1 ≤ n ^ b + n ^ c := by omega
  unfold LeafTailUnitZ nPowZ mZ
  rw [Nat.cast_mul, Nat.cast_sub hle]
  simp only [Nat.cast_add, Nat.cast_pow]
  have hpred : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [hpred]

private theorem intToNat_BReadTailMainZ_eq_explicit
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    Int.toNat (BReadTailMainZ a b c d n) =
      oddBReadProfileRankNat n a d *
        (n * (n ^ b + n ^ c - (n - 1))) := by
  have hprofile :=
    intCast_oddBReadProfileRankNat (n := n) (a := a) (d := d) ha hd
  have htail :=
    intCast_oddBReadTailUnitNat (n := n) (b := b) (c := c) hb
  have hcast :
      BReadTailMainZ a b c d n =
        ((oddBReadProfileRankNat n a d *
          (n * (n ^ b + n ^ c - (n - 1))) : ℕ) : ℤ) := by
    unfold BReadTailMainZ
    rw [← hprofile, ← htail]
    norm_num
  rw [hcast]
  exact Int.toNat_natCast _

private theorem kCdCv_add_oddKernelExp_eq_BReadTailMain
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    kCdCvElimExpNat n a b d
        + n * (n ^ c - (n - 1)) * oddBReadProfileRankNat n a d
      =
    Int.toNat (BReadTailMainZ a b c d n) := by
  rw [kCdCvElimExpNat_eq_oddBReadProfileRank_mul
    (n := n) (a := a) (b := b) (d := d) ha]
  rw [intToNat_BReadTailMainZ_eq_explicit
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hd]
  have hnc : n - 1 ≤ n ^ c := by
    have hnle : n ≤ n ^ c := Nat.le_pow hc
    omega
  have hsum :
      n ^ b + (n ^ c - (n - 1)) =
        n ^ b + n ^ c - (n - 1) := by
    omega
  rw [pow_succ]
  calc
    n ^ b * n * oddBReadProfileRankNat n a d
          + n * (n ^ c - (n - 1)) * oddBReadProfileRankNat n a d
        =
        n * (n ^ b + (n ^ c - (n - 1))) *
          oddBReadProfileRankNat n a d := by ring
    _ =
        n * (n ^ b + n ^ c - (n - 1)) *
          oddBReadProfileRankNat n a d := by rw [hsum]
    _ =
        oddBReadProfileRankNat n a d *
          (n * (n ^ b + n ^ c - (n - 1))) := by ring

/-- Aggregate the actual `ZVec` source fibers by their `vecSum`. -/
private noncomputable def oddBReadAggMap
    (n c : ℕ) [NeZero n] (E : Type*) [AddCommGroup E] [Module F E] :
    (I n → ZVec n c → E) →ₗ[F] (I n → I n → E) where
  toFun X := fun s t =>
    ∑ z : ZVec n c, if vecSum z = t then X s z else 0
  map_add' X Y := by
    funext s t
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = t <;> simp [hz]
  map_smul' r X := by
    funext s t
    simp only [Pi.smul_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = t <;> simp [hz]

private theorem oddBReadAggMap_surjective
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (E : Type*) [AddCommGroup E] [Module F E] :
    Function.Surjective (oddBReadAggMap n c E) := by
  classical
  intro G
  let X : I n → ZVec n c → E := fun s z =>
    if z = vecSumRep (n := n) (k := c) hc (vecSum z) then
      G s (vecSum z)
    else
      0
  refine ⟨X, ?_⟩
  funext s t
  change
    (∑ z : ZVec n c, if vecSum z = t then X s z else 0) = G s t
  rw [Finset.sum_eq_single (vecSumRep (n := n) (k := c) hc t)]
  · simp [X, vecSum_vecSumRep]
  · intro z _ hz
    by_cases hsum : vecSum z = t
    · have hrep :
          vecSumRep (n := n) (k := c) hc (vecSum z) =
            vecSumRep (n := n) (k := c) hc t := by rw [hsum]
      simp [X, hsum, hz]
    · simp [hsum]
  · simp

/-- Reindex a two-dimensional grid by its diagonal `r = s + t`. -/
private noncomputable def oddBReadDiagonalEquiv
    (n : ℕ) [NeZero n] (E : Type*) [AddCommGroup E] [Module F E] :
    (I n → I n → E) ≃ₗ[F] (I n → I n → E) where
  toFun G := fun r s => G s (r - s)
  invFun K := fun s t => K (s + t) s
  left_inv G := by
    funext s t
    change G s (s + t - s) = G s t
    congr 2
    abel
  right_inv K := by
    funext r s
    change K (s + (r - s)) s = K r s
    congr 2
    abel
  map_add' G H := by
    funext r s
    rfl
  map_smul' x G := by
    funext r s
    rfl

/-- Apply the repository cyclic-difference map independently on every
diagonal, with the zero-sum codomain made explicit. -/
private noncomputable def oddBReadDiagonalCycDiffMap
    (n : ℕ) [NeZero n] (E : Type*) [AddCommGroup E] [Module F E] :
    (I n → I n → E) →ₗ[F] (I n → ZeroSumProfileM n E) where
  toFun K := fun r => cycDiffToZeroSumM (n := n) E (K r)
  map_add' K L := by
    funext r
    exact (cycDiffToZeroSumM (n := n) E).map_add (K r) (L r)
  map_smul' x K := by
    funext r
    exact (cycDiffToZeroSumM (n := n) E).map_smul x (K r)

private noncomputable def oddBReadDiagonalMap
    (n : ℕ) [NeZero n] (E : Type*) [AddCommGroup E] [Module F E] :
    (I n → I n → E) →ₗ[F] (I n → ZeroSumProfileM n E) :=
  (oddBReadDiagonalCycDiffMap n E).comp
    (oddBReadDiagonalEquiv n E).toLinearMap

private theorem oddBReadDiagonalMap_apply
    {n : ℕ} [NeZero n] (E : Type*) [AddCommGroup E] [Module F E]
    (G : I n → I n → E) (r s : I n) :
    ((oddBReadDiagonalMap n E G) r).1 s =
      G s (r - s) + G (s + 1) (r - (s + 1)) := by
  rfl

private theorem oddBReadDiagonalMap_surjective
    {n : ℕ} [NeZero n] (E : Type*) [AddCommGroup E] [Module F E]
    [FiniteDimensional F E] :
    Function.Surjective (oddBReadDiagonalMap n E) := by
  intro U
  let K : I n → I n → E := fun r =>
    cycPrimitiveM (n := n) E (U r)
  refine ⟨(oddBReadDiagonalEquiv n E).symm K, ?_⟩
  funext r
  apply Subtype.ext
  change
    cycDiff (n := n) E
        ((oddBReadDiagonalEquiv n E
          ((oddBReadDiagonalEquiv n E).symm K)) r)
      =
    (U r).1
  rw [(oddBReadDiagonalEquiv n E).apply_symm_apply]
  exact congrArg Subtype.val (cycDiff_cycPrimitiveM (n := n) E (U r))

private noncomputable def oddBReadCyclicSourceMap
    (n c : ℕ) [NeZero n] (E : Type*) [AddCommGroup E] [Module F E] :
    (I n → ZVec n c → E) →ₗ[F] (I n → ZeroSumProfileM n E) :=
  (oddBReadDiagonalMap n E).comp (oddBReadAggMap n c E)

private theorem oddBReadCyclicSourceMap_surjective
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (E : Type*) [AddCommGroup E] [Module F E] [FiniteDimensional F E] :
    Function.Surjective (oddBReadCyclicSourceMap n c E) :=
  (oddBReadDiagonalMap_surjective E).comp
    (oddBReadAggMap_surjective hc E)

private theorem finrank_oddBReadCyclicTarget
    {n : ℕ} [NeZero n]
    (E : Type*) [AddCommGroup E] [Module F E] [FiniteDimensional F E] :
    Module.finrank F (I n → ZeroSumProfileM n E) =
      n * (n - 1) * Module.finrank F E := by
  calc
    Module.finrank F (I n → ZeroSumProfileM n E)
        =
        Fintype.card (I n) *
          Module.finrank F (ZeroSumProfileM n E) := by
            simp [Module.finrank_pi_fintype]
    _ = n * ((n - 1) * Module.finrank F E) := by
          rw [finrank_ZeroSumProfileM]
          simp [I, ZMod.card]
    _ = n * (n - 1) * Module.finrank F E := by ring

private theorem finrank_oddBReadCyclicSource
    {n c : ℕ} [NeZero n]
    (E : Type*) [AddCommGroup E] [Module F E] [FiniteDimensional F E] :
    Module.finrank F (I n → ZVec n c → E) =
      n ^ (c + 1) * Module.finrank F E := by
  calc
    Module.finrank F (I n → ZVec n c → E)
        =
        Fintype.card (I n) * Fintype.card (ZVec n c) *
          Module.finrank F E := by
            simp [Module.finrank_pi_fintype, Nat.mul_assoc]
    _ = n * n ^ c * Module.finrank F E := by
          rw [show Fintype.card (I n) = n by simp [I, ZMod.card]]
          rw [card_vec]
    _ = n ^ (c + 1) * Module.finrank F E := by
          rw [pow_succ]
          ring

private theorem finrank_range_oddBReadCyclicSourceMap
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (E : Type*) [AddCommGroup E] [Module F E] [FiniteDimensional F E] :
    Module.finrank F
        (LinearMap.range (oddBReadCyclicSourceMap n c E))
      =
      n * (n - 1) * Module.finrank F E := by
  rw [LinearMap.range_eq_top.mpr (oddBReadCyclicSourceMap_surjective hc E)]
  rw [finrank_top]
  exact finrank_oddBReadCyclicTarget E

set_option synthInstance.maxHeartbeats 200000 in
private theorem finrank_ker_oddBReadCyclicSourceMap
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (E : Type*) [AddCommGroup E] [Module F E] [FiniteDimensional F E] :
    Module.finrank F
        (LinearMap.ker (oddBReadCyclicSourceMap n c E))
      =
      n * (n ^ c - (n - 1)) * Module.finrank F E := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (oddBReadCyclicSourceMap n c E)
  rw [finrank_range_oddBReadCyclicSourceMap hc E,
    finrank_oddBReadCyclicSource E] at hnull
  have hle : n - 1 ≤ n ^ c := by
    have hnle : n ≤ n ^ c := Nat.le_pow hc
    omega
  have hsplit :
      n ^ (c + 1) * Module.finrank F E =
        n * (n - 1) * Module.finrank F E
          + n * (n ^ c - (n - 1)) * Module.finrank F E := by
    have hcSplit : n ^ c = (n - 1) + (n ^ c - (n - 1)) := by omega
    calc
      n ^ (c + 1) * Module.finrank F E
          = n * n ^ c * Module.finrank F E := by
              rw [pow_succ]
              ring
      _ =
          n * ((n - 1) + (n ^ c - (n - 1))) *
            Module.finrank F E := by rw [← hcSplit]
      _ =
          n * (n - 1) * Module.finrank F E
            + n * (n ^ c - (n - 1)) * Module.finrank F E := by ring
  rw [hsplit] at hnull
  exact Nat.add_left_cancel hnull

/-- The cyclic normal form on the actual `XB` source coordinates. -/
private noncomputable def oddBReadCyclicXBMap
    {n a c d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
      (I n → ZeroSumProfileM n (LeafProfileKernel n a d)) :=
  (oddBReadCyclicSourceMap n c (LeafProfileKernel n a d)).comp
    (leafBProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd).symm.toLinearMap

private theorem oddBReadCyclicXBMap_surjective
    {n a c d : ℕ} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    Function.Surjective
      (oddBReadCyclicXBMap (n := n) (a := a) (c := c) (d := d) hd) :=
  (oddBReadCyclicSourceMap_surjective
      (E := LeafProfileKernel n a d) hc).comp
    (leafBProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd).symm.surjective

private noncomputable def ker_oddBReadCyclicXBMapEquiv
    {n a c d : ℕ} [NeZero n] (hd : 0 < d) :
    LinearMap.ker
        (oddBReadCyclicXBMap
          (n := n) (a := a) (c := c) (d := d) hd)
      ≃ₗ[F]
    LinearMap.ker
        (oddBReadCyclicSourceMap n c (LeafProfileKernel n a d)) where
  toFun X :=
    ⟨(leafBProfileKernelCoordEquivIndexDiff
        (n := n) (a := a) (c := c) (d := d) hd).symm X.1, X.2⟩
  invFun X :=
    ⟨leafBProfileKernelCoordEquivIndexDiff
        (n := n) (a := a) (c := c) (d := d) hd X.1, by
      simpa [oddBReadCyclicXBMap] using X.2⟩
  left_inv X := by
    apply Subtype.ext
    exact (leafBProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd).apply_symm_apply X.1
  right_inv X := by
    apply Subtype.ext
    exact (leafBProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd).symm_apply_apply X.1
  map_add' X Y := by
    ext
    simp
  map_smul' r X := by
    ext
    simp

private theorem finrank_ker_oddBReadCyclicXBMap
    {n a c d : ℕ} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker
          (oddBReadCyclicXBMap
            (n := n) (a := a) (c := c) (d := d) hd))
      =
      n * (n ^ c - (n - 1)) * oddBReadProfileRankNat n a d := by
  rw [LinearEquiv.finrank_eq
    (ker_oddBReadCyclicXBMapEquiv
      (n := n) (a := a) (c := c) (d := d) hd)]
  rw [finrank_ker_oddBReadCyclicSourceMap
    (E := LeafProfileKernel n a d) hc]
  rw [finrank_LeafProfileKernel_explicit
    (n := n) (a := a) (d := d) hd]
  rfl

/-!
## Actual B-read factorization through the odd cyclic normal form

The following coordinate definitions touch the production
`leafBReadTailReadMap` directly.  They package exactly the two coefficient
reads occurring there; no new source or Fourier wrapper is introduced.
-/

private def oddBReadKernelAt
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (U : I n → ZeroSumProfileM n (LeafProfileKernel n a d))
    (y : YVec n b) (t : I n) :
    LeafProfileKernel n a d :=
  (U (vecSum y + t)).1 (vecSum y)

private def oddBReadLocalCdCoeff
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (K : LeafProfileKernel n a d) (p : PVec n a) (s : I n) : F :=
  (∑ ω : PassiveVisibleIndex n d hd,
      if s = vecSum ω.1 then
        ((leafProfileKernelEquivIndexDiff
          (n := n) (a := a) (d := d) hd K).1 ω).1 p
      else 0)
    +
  (((leafProfileKernelEquivIndexDiff
    (n := n) (a := a) (d := d) hd K).2 p).1 s)

private def oddBReadLocalCvCoeff
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (K : LeafProfileKernel n a d)
    (ω : PassiveVisibleIndex n d hd) (p : PVec n a) : F :=
  ((leafProfileKernelEquivIndexDiff
      (n := n) (a := a) (d := d) hd K).1 ω).1 p
    +
  (((leafProfileKernelEquivIndexDiff
      (n := n) (a := a) (d := d) hd K).2 p).1 (vecSum ω.1))

private def oddBReadEncode
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : I n → ZeroSumProfileM n (LeafProfileKernel n a d)) :
    LeafBReadTarget n a b c d hd :=
  (fun ips =>
      oddBReadLocalCdCoeff hd
          (oddBReadKernelAt hd U ips.1.1 ips.1.2)
          ips.2.1 ips.2.2.1
        +
      oddBReadLocalCdCoeff hd
          (oddBReadKernelAt hd U ips.1.1 ips.1.2)
          ips.2.1 0,
   fun ips =>
      oddBReadLocalCvCoeff hd
          (oddBReadKernelAt hd U ips.1.2.1 ips.1.2.2)
          ips.1.1 ips.2.1
        +
      oddBReadLocalCvCoeff hd
          (oddBReadKernelAt hd U ips.1.2.1 ips.1.2.2)
          ips.1.1 (zeroVec : PVec n a))

private theorem oddBReadKernelAt_cyclicSourceMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X : I n → ZVec n c → LeafProfileKernel n a d)
    (y : YVec n b) (t : I n) :
    oddBReadKernelAt hd
        (oddBReadCyclicSourceMap n c (LeafProfileKernel n a d) X) y t
      =
    oddBReadAggMap n c (LeafProfileKernel n a d) X (vecSum y) t
      +
    oddBReadAggMap n c (LeafProfileKernel n a d) X (vecSum y + 1) (t - 1) := by
  change
    ((oddBReadDiagonalMap n (LeafProfileKernel n a d))
        (oddBReadAggMap n c (LeafProfileKernel n a d) X)
        (vecSum y + t)).1 (vecSum y)
      =
    _
  rw [oddBReadDiagonalMap_apply]
  congr 2 <;> abel

private theorem oddBReadAggMap_eq_sum_if
    {n c : ℕ} [NeZero n]
    (E : Type*) [AddCommGroup E] [Module F E]
    (X : I n → ZVec n c → E) (s t : I n) :
    oddBReadAggMap n c E X s t =
      ∑ z : ZVec n c, if t = vecSum z then X s z else 0 := by
  unfold oddBReadAggMap
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases h : vecSum z = t
  · simp [h]
  · simp [h, Ne.symm h]

private theorem oddBReadAggMap_sub_one_eq_sum_if
    {n c : ℕ} [NeZero n]
    (E : Type*) [AddCommGroup E] [Module F E]
    (X : I n → ZVec n c → E) (s t : I n) :
    oddBReadAggMap n c E X s (t - 1) =
      ∑ z : ZVec n c, if t = vecSum z + 1 then X s z else 0 := by
  unfold oddBReadAggMap
  refine Finset.sum_congr rfl ?_
  intro z _
  have hiff : vecSum z = t - 1 ↔ t = vecSum z + 1 := by
    constructor <;> intro h
    · rw [h]
      abel
    · rw [h]
      abel
  simp only [hiff]

private theorem oddBReadKernelAt_cyclicSourceMap_eq_two_sums
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X : I n → ZVec n c → LeafProfileKernel n a d)
    (y : YVec n b) (t : I n) :
    oddBReadKernelAt hd
        (oddBReadCyclicSourceMap n c (LeafProfileKernel n a d) X) y t
      =
      (∑ z : ZVec n c,
        if t = vecSum z then X (vecSum y) z else 0)
      +
      (∑ z : ZVec n c,
        if t = vecSum z + 1 then X (vecSum y + 1) z else 0) := by
  rw [oddBReadKernelAt_cyclicSourceMap]
  rw [oddBReadAggMap_eq_sum_if, oddBReadAggMap_sub_one_eq_sum_if]

private theorem leafProfileKernelEquivIndexDiff_sum_fst_apply
    {ι : Type*} [Fintype ι] {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (f : ι → LeafProfileKernel n a d)
    (ω : PassiveVisibleIndex n d hd) (p : PVec n a) :
    ((leafProfileKernelEquivIndexDiff hd (∑ i, f i)).1 ω).1 p =
      ∑ i, ((leafProfileKernelEquivIndexDiff hd (f i)).1 ω).1 p := by
  have h := map_sum (leafProfileKernelEquivIndexDiff hd) f Finset.univ
  have h1 := congrArg Prod.fst h
  have h2 := congrFun h1 ω
  have h3 := congrArg Subtype.val h2
  have h4 := congrFun h3 p
  simpa only [Finset.sum_apply, Prod.fst_sum, Submodule.coe_sum] using h4

private theorem leafProfileKernelEquivIndexDiff_sum_snd_apply
    {ι : Type*} [Fintype ι] {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (f : ι → LeafProfileKernel n a d) (p : PVec n a) (s : I n) :
    ((leafProfileKernelEquivIndexDiff hd (∑ i, f i)).2 p).1 s =
      ∑ i, ((leafProfileKernelEquivIndexDiff hd (f i)).2 p).1 s := by
  have h := map_sum (leafProfileKernelEquivIndexDiff hd) f Finset.univ
  have h1 := congrArg Prod.snd h
  have h2 := congrFun h1 p
  have h3 := congrArg Subtype.val h2
  have h4 := congrFun h3 s
  simpa only [Finset.sum_apply, Prod.snd_sum, Submodule.coe_sum] using h4

private theorem leafProfileKernelEquivIndexDiff_ite_fst_apply
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (P : Prop) [Decidable P] (K : LeafProfileKernel n a d)
    (ω : PassiveVisibleIndex n d hd) (p : PVec n a) :
    ((leafProfileKernelEquivIndexDiff hd
        (if P then K else 0)).1 ω).1 p =
      if P then ((leafProfileKernelEquivIndexDiff hd K).1 ω).1 p else 0 := by
  by_cases h : P <;> simp [h]

private theorem leafProfileKernelEquivIndexDiff_ite_snd_apply
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (P : Prop) [Decidable P] (K : LeafProfileKernel n a d)
    (p : PVec n a) (s : I n) :
    ((leafProfileKernelEquivIndexDiff hd
        (if P then K else 0)).2 p).1 s =
      if P then ((leafProfileKernelEquivIndexDiff hd K).2 p).1 s else 0 := by
  by_cases h : P <;> simp [h]

private theorem sum_ite_add_zero_local
    {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (f g : ι → F) :
    (∑ i, if P i then f i + g i else 0) =
      (∑ i, if P i then f i else 0) +
      ∑ i, if P i then g i else 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : P i <;> simp [h]

private theorem sum_ite_sum_ite_comm_local
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → Prop) [DecidablePred P]
    (Q : κ → Prop) [DecidablePred Q]
    (f : ι → κ → F) :
    (∑ i, if P i then (∑ k, if Q k then f i k else 0) else 0)
      =
    ∑ k, if Q k then (∑ i, if P i then f i k else 0) else 0 := by
  calc
    (∑ i, if P i then (∑ k, if Q k then f i k else 0) else 0)
        =
        ∑ i, ∑ k, if P i then (if Q k then f i k else 0) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          by_cases hi : P i <;> simp [hi]
    _ =
        ∑ k, ∑ i, if P i then (if Q k then f i k else 0) else 0 := by
          rw [Finset.sum_comm]
    _ =
        ∑ k, if Q k then (∑ i, if P i then f i k else 0) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro k _
          by_cases hk : Q k
          · simp [hk]
          · simp [hk]

private theorem sum_WVec_eq_visible_add_excluded
    {n d : ℕ} [NeZero n] (hd : 0 < d) (f : WVec n d → F) :
    (∑ w, f w) =
      (∑ ω : PassiveVisibleIndex n d hd, f ω.1)
        + ∑ e : PassiveExcludedIndex n d hd, f e.1 := by
  classical
  let p : WVec n d → Prop := passiveExcludedPred (n := n) (d := d) hd
  have hs :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (WVec n d))) (p := p) f).symm
  rw [add_comm] at hs
  calc
    (∑ w, f w) =
        (∑ w ∈ (Finset.univ : Finset (WVec n d)) with ¬ p w, f w)
          +
        (∑ w ∈ (Finset.univ : Finset (WVec n d)) with p w, f w) := by
          simpa using hs
    _ =
        (∑ w : {w : WVec n d // ¬ p w}, f w.1)
          +
        (∑ w : {w : WVec n d // p w}, f w.1) := by
          congr 1
          · simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (WVec n d)))
                (p := fun w : WVec n d => ¬ p w) (f := f)).symm
          · simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (WVec n d)))
                (p := p) (f := f)).symm
    _ =
        (∑ ω : PassiveVisibleIndex n d hd, f ω.1)
          +
        ∑ e : PassiveExcludedIndex n d hd, f e.1 := by
          congr 1
          let ev := passiveVisibleIndexEquivComplement
            (n := n) (d := d) hd
          simpa [p, ev] using
            (Equiv.sum_comp ev (fun w => f w.1)).symm

private theorem sum_passiveVisible_comp_vecSum_of_odd
    {n d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (f : I n → F) :
    (∑ ω : PassiveVisibleIndex n d hd, f (vecSum ω.1)) = f 0 := by
  classical
  have hall := sum_vecSum_eq_card_tail_mul (n := n) (d := d) hd f
  rw [natCast_card_vec_eq_one_of_odd
    (n := n) (k := d - 1) hn, one_mul] at hall
  have hs := sum_WVec_eq_visible_add_excluded
    (n := n) (d := d) hd (fun w => f (vecSum w))
  have he :
      (∑ e : PassiveExcludedIndex n d hd, f (vecSum e.1))
        =
      ∑ u : NonzeroI n, f u.1 := by
    rw [← Equiv.sum_comp
      (passiveExcludedEquivNonzero (n := n) (d := d) hd)
      (fun e : PassiveExcludedIndex n d hd => f (vecSum e.1))]
    change
      (∑ u : NonzeroI n,
        f (vecSum (vecSumRep (n := n) (k := d) hd u.1)))
        =
      _
    simp_rw [vecSum_vecSumRep (n := n) (k := d) hd]
  rw [hall, he, sum_I_eq_value_zero_add_sum_nonzero] at hs
  exact add_right_cancel hs.symm

private theorem sum_passiveVisible_if_vecSum_eq_of_odd
    {n d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (u : I n) (x : F) :
    (∑ ω : PassiveVisibleIndex n d hd,
      if u = vecSum ω.1 then x else 0)
      =
    if u = 0 then x else 0 := by
  simpa using
    sum_passiveVisible_comp_vecSum_of_odd hd hn
      (fun s : I n => if u = s then x else 0)

private def oddBReadPassiveFiberSum
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (v : PassiveVisibleIndex n d hd → F) (u : I n) : F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    if u = vecSum ω.1 then v ω else 0

private def oddBReadPassivePsi
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (v : PassiveVisibleIndex n d hd → F)
    (ω : PassiveVisibleIndex n d hd) : F :=
  v ω
    + oddBReadPassiveFiberSum hd v (vecSum ω.1)
    + ∑ ω', v ω'

private noncomputable def oddBReadPassivePsiLinearMap
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    (PassiveVisibleIndex n d hd → F) →ₗ[F]
      (PassiveVisibleIndex n d hd → F) where
  toFun := oddBReadPassivePsi hd
  map_add' v w := by
    funext ω
    unfold oddBReadPassivePsi oddBReadPassiveFiberSum
    simp only [Pi.add_apply]
    rw [sum_ite_add_zero_local, Finset.sum_add_distrib]
    ring
  map_smul' r v := by
    funext ω
    unfold oddBReadPassivePsi oddBReadPassiveFiberSum
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    have hf :
        (∑ x : PassiveVisibleIndex n d hd,
          if vecSum ω.1 = vecSum x.1 then r * v x else 0)
          =
        r * ∑ x : PassiveVisibleIndex n d hd,
          if vecSum ω.1 = vecSum x.1 then v x else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : vecSum ω.1 = vecSum x.1 <;> simp [h]
    rw [hf, ← Finset.mul_sum]
    ring

private theorem sum_oddBReadPassiveFiberSum
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (v : PassiveVisibleIndex n d hd → F) :
    (∑ u : I n, oddBReadPassiveFiberSum hd v u) = ∑ ω, v ω := by
  classical
  unfold oddBReadPassiveFiberSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro ω _
  rw [Finset.sum_eq_single (vecSum ω.1)]
  · simp
  · intro u _ hu
    simp [hu]
  · simp

private theorem oddBReadPassivePsi_eq_zero_imp
    {n d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (v : PassiveVisibleIndex n d hd → F)
    (hψ : oddBReadPassivePsi hd v = 0) :
    v = 0 := by
  classical
  let A : I n → F := oddBReadPassiveFiberSum hd v
  let S : F := ∑ ω, v ω
  have hv (ω : PassiveVisibleIndex n d hd) :
      v ω = A (vecSum ω.1) + S := by
    have hω := congrFun hψ ω
    change v ω + A (vecSum ω.1) + S = 0 at hω
    calc
      v ω = v ω + 0 := by simp
      _ = v ω + (v ω + A (vecSum ω.1) + S) := by rw [hω]
      _ = (v ω + v ω) + (A (vecSum ω.1) + S) := by abel
      _ = A (vecSum ω.1) + S := by rw [F_add_self, zero_add]
  have hA (u : I n) :
      A u = if u = 0 then A u + S else 0 := by
    calc
      A u =
          ∑ ω : PassiveVisibleIndex n d hd,
            if u = vecSum ω.1 then v ω else 0 := rfl
      _ =
          ∑ ω : PassiveVisibleIndex n d hd,
            if u = vecSum ω.1 then A (vecSum ω.1) + S else 0 := by
              refine Finset.sum_congr rfl ?_
              intro ω _
              rw [hv ω]
      _ =
          ∑ ω : PassiveVisibleIndex n d hd,
            if u = vecSum ω.1 then A u + S else 0 := by
              refine Finset.sum_congr rfl ?_
              intro ω _
              by_cases h : u = vecSum ω.1
              · simp [h]
              · simp [h]
      _ = if u = 0 then A u + S else 0 :=
        sum_passiveVisible_if_vecSum_eq_of_odd hd hn u (A u + S)
  have hS : S = 0 := by
    have h0 := hA 0
    simp at h0
    have hcancel : A 0 + 0 = A 0 + S := by simpa using h0
    exact add_left_cancel hcancel.symm
  have hA_ne (u : NonzeroI n) : A u.1 = 0 := by
    simpa [u.2] using hA u.1
  have hA0 : A 0 = 0 := by
    have hsumA :
        (∑ u : I n, A u) = S := by
      exact sum_oddBReadPassiveFiberSum hd v
    rw [sum_I_eq_value_zero_add_sum_nonzero] at hsumA
    have htail : (∑ u : NonzeroI n, A u.1) = 0 := by
      exact Finset.sum_eq_zero (fun u _ => hA_ne u)
    rw [htail, add_zero, hS] at hsumA
    exact hsumA
  funext ω
  change v ω = 0
  rw [hv ω, hS, add_zero]
  by_cases hs : vecSum ω.1 = 0
  · rw [hs, hA0]
  · exact hA_ne ⟨vecSum ω.1, hs⟩

private theorem eq_of_add_eq_zero_F_local {x y : F}
    (h : x + y = 0) : x = y := by
  calc
    x = x + 0 := by simp
    _ = x + (x + y) := by rw [h]
    _ = (x + x) + y := by abel
    _ = y := by rw [F_add_self, zero_add]

private theorem oddBReadLocal_reads_eq_zero_imp
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (K : LeafProfileKernel n a d)
    (hCd : ∀ (p : PVec n a) (u : NonzeroI n),
      oddBReadLocalCdCoeff hd K p u.1
        + oddBReadLocalCdCoeff hd K p 0 = 0)
    (hCv : ∀ (ω : PassiveVisibleIndex n d hd)
        (p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}),
      oddBReadLocalCvCoeff hd K ω p.1
        + oddBReadLocalCvCoeff hd K ω (zeroVec : PVec n a) = 0) :
    K = 0 := by
  classical
  let J :=
    leafProfileKernelEquivIndexDiff (n := n) (a := a) (d := d) hd
  let V : PVec n a → PassiveVisibleIndex n d hd → F :=
    fun p ω => ((J K).1 ω).1 p
  let D : PVec n a → I n → F :=
    fun p u => ((J K).2 p).1 u
  let A : PVec n a → I n → F :=
    fun p => oddBReadPassiveFiberSum hd (V p)
  let S : PVec n a → F := fun p => ∑ ω, V p ω
  have hR (p : PVec n a) (u : I n) :
      oddBReadLocalCdCoeff hd K p u =
        oddBReadLocalCdCoeff hd K p 0 := by
    by_cases hu : u = 0
    · rw [hu]
    · exact eq_of_add_eq_zero_F_local (hCd p ⟨u, hu⟩)
  have hDsum (p : PVec n a) : (∑ u : I n, D p u) = 0 := by
    have hmem := LinearMap.mem_ker.mp ((J K).2 p).2
    change (∑ u : I n, D p u) = 0 at hmem
    exact hmem
  have hRsum (p : PVec n a) :
      (∑ u : I n, oddBReadLocalCdCoeff hd K p u) = S p := by
    calc
      (∑ u : I n, oddBReadLocalCdCoeff hd K p u)
          = (∑ u : I n, (A p u + D p u)) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              rfl
      _ = (∑ u : I n, A p u) + ∑ u : I n, D p u := by
            rw [Finset.sum_add_distrib]
      _ = (∑ u : I n, A p u) := by rw [hDsum, add_zero]
      _ = S p := sum_oddBReadPassiveFiberSum hd (V p)
  have hncast : ((n : ℕ) : F) = 1 := natCast_odd_eq_one_F hn
  have hRvalue (p : PVec n a) (u : I n) :
      oddBReadLocalCdCoeff hd K p u = S p := by
    rw [hR p u]
    calc
      oddBReadLocalCdCoeff hd K p 0
          =
          ∑ _u : I n, oddBReadLocalCdCoeff hd K p 0 := by
            simp [Finset.sum_const, nsmul_eq_mul, I, ZMod.card, hncast]
      _ =
          ∑ u' : I n, oddBReadLocalCdCoeff hd K p u' := by
            refine Finset.sum_congr rfl ?_
            intro u' _
            exact (hR p u').symm
      _ = S p := hRsum p
  have hD (p : PVec n a) (u : I n) :
      D p u = A p u + S p := by
    have hlocal :
        A p u + D p u = S p := by
      simpa [oddBReadLocalCdCoeff, A, D] using hRvalue p u
    calc
      D p u = 0 + D p u := by simp
      _ = (A p u + A p u) + D p u := by rw [F_add_self]
      _ = A p u + (A p u + D p u) := by abel
      _ = A p u + S p := by rw [hlocal]
  have hTψ (p : PVec n a) (ω : PassiveVisibleIndex n d hd) :
      oddBReadLocalCvCoeff hd K ω p =
        oddBReadPassivePsi hd (V p) ω := by
    unfold oddBReadLocalCvCoeff oddBReadPassivePsi
    change V p ω + D p (vecSum ω.1) =
      V p ω + A p (vecSum ω.1) + S p
    rw [hD]
    ring
  have hTeq (p : PVec n a) (ω : PassiveVisibleIndex n d hd) :
      oddBReadLocalCvCoeff hd K ω p =
        oddBReadLocalCvCoeff hd K ω (zeroVec : PVec n a) := by
    by_cases hp : p = (zeroVec : PVec n a)
    · rw [hp]
    · exact eq_of_add_eq_zero_F_local (hCv ω ⟨p, hp⟩)
  have hψeq (p : PVec n a) :
      oddBReadPassivePsi hd (V p) =
        oddBReadPassivePsi hd (V (zeroVec : PVec n a)) := by
    funext ω
    rw [← hTψ p ω, ← hTψ (zeroVec : PVec n a) ω, hTeq p ω]
  have hVconst (p : PVec n a) :
      V p = V (zeroVec : PVec n a) := by
    let q := V p + V (zeroVec : PVec n a)
    have hq : oddBReadPassivePsi hd q = 0 := by
      change
        oddBReadPassivePsiLinearMap hd
            (V p + V (zeroVec : PVec n a)) = 0
      rw [map_add]
      funext ω
      change
        oddBReadPassivePsi hd (V p) ω
          + oddBReadPassivePsi hd (V (zeroVec : PVec n a)) ω = 0
      rw [congrFun (hψeq p) ω]
      exact F_add_self _
    have hq0 := oddBReadPassivePsi_eq_zero_imp hd hn q hq
    funext ω
    have hω := congrFun hq0 ω
    change V p ω + V (zeroVec : PVec n a) ω = 0 at hω
    exact eq_of_add_eq_zero_F_local hω
  have hpow : ((n ^ (a - 1) : ℕ) : F) = 1 :=
    natCast_odd_eq_one_F
      (Odd.pow (a := n) (n := a - 1) hn)
  have hVzero (p : PVec n a) (ω : PassiveVisibleIndex n d hd) :
      V p ω = 0 := by
    rw [hVconst p]
    have hmem := LinearMap.mem_ker.mp ((J K).1 ω).2
    change (∑ q : PVec n a, V q ω) = 0 at hmem
    have hconst :
        (∑ q : PVec n a, V q ω) =
          ∑ _q : PVec n a, V (zeroVec : PVec n a) ω := by
      refine Finset.sum_congr rfl ?_
      intro q _
      exact congrFun (hVconst q) ω
    rw [hconst] at hmem
    have hsumconst :
        (∑ _q : PVec n a, V (zeroVec : PVec n a) ω) =
          (Fintype.card (PVec n a) : F) *
            V (zeroVec : PVec n a) ω := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hsumconst] at hmem
    simpa [PVec, card_vec, hpow, one_mul] using hmem
  have hDzero (p : PVec n a) (u : I n) : D p u = 0 := by
    rw [hD]
    simp [A, S, oddBReadPassiveFiberSum, hVzero]
  apply J.injective
  rw [map_zero]
  apply Prod.ext
  · funext ω
    apply Subtype.ext
    funext p
    exact hVzero p ω
  · funext p
    apply Subtype.ext
    funext u
    exact hDzero p u

private theorem oddBReadEncode_eq_zero_iff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) (hn : Odd n)
    (U : I n → ZeroSumProfileM n (LeafProfileKernel n a d)) :
    oddBReadEncode
        (n := n) (a := a) (b := b) (c := c) (d := d) hd U = 0
      ↔
    U = 0 := by
  classical
  constructor
  · intro hEncode
    funext r
    apply Subtype.ext
    funext s
    let y : YVec n b := vecSumRep (n := n) (k := b) hb s
    let t : I n := r - s
    let K : LeafProfileKernel n a d := oddBReadKernelAt hd U y t
    have hCdLocal (p : PVec n a) (u : NonzeroI n) :
        oddBReadLocalCdCoeff hd K p u.1
          + oddBReadLocalCdCoeff hd K p 0 = 0 := by
      have hpoint :=
        congrFun (congrArg Prod.fst hEncode) ((y, t), (p, u))
      simpa [oddBReadEncode, K] using hpoint
    have hCvLocal (ω : PassiveVisibleIndex n d hd)
        (p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}) :
        oddBReadLocalCvCoeff hd K ω p.1
          + oddBReadLocalCvCoeff hd K ω (zeroVec : PVec n a) = 0 := by
      have hpoint :=
        congrFun (congrArg Prod.snd hEncode) ((ω, (y, t)), p)
      simpa [oddBReadEncode, K] using hpoint
    have hK : K = 0 :=
      oddBReadLocal_reads_eq_zero_imp hd hn K hCdLocal hCvLocal
    have hy : vecSum y = s := by
      exact vecSum_vecSumRep (n := n) (k := b) hb s
    have hindex : vecSum y + t = r := by
      rw [hy]
      dsimp [t]
      abel
    change (U r).1 s = 0
    have hKapply : K = (U r).1 s := by
      unfold K oddBReadKernelAt
      rw [hindex, hy]
    rw [← hKapply, hK]
  · intro hU
    subst U
    apply Prod.ext
    · funext ips
      simp [oddBReadEncode, oddBReadKernelAt, oddBReadLocalCdCoeff]
    · funext ips
      simp [oddBReadEncode, oddBReadKernelAt, oddBReadLocalCvCoeff]

private theorem oddBRead_tailRead_cd_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (X : I n → ZVec n c → LeafProfileKernel n a d)
    (y : YVec n b) (t : I n) (p : PVec n a) (u : NonzeroI n) :
    ((leafBReadTailReadMap hd :
        LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
          LeafBReadTarget n a b c d hd)
      (leafBProfileKernelCoordEquivIndexDiff
        (n := n) (a := a) (c := c) (d := d) hd X)).1
        ((y, t), (p, u))
      =
    (oddBReadEncode
      (n := n) (a := a) (b := b) (c := c) (d := d) hd
      (oddBReadCyclicSourceMap n c (LeafProfileKernel n a d) X)).1
        ((y, t), (p, u)) := by
  classical
  change
    qLeafProfileKernelTotalCdCoeffRead hd
        (0 : LeafVisibleKernel n b c d)
        (leafBProfileKernelCoordEquivIndexDiff hd X) ((y, t), (p, u))
      =
    _
  unfold qLeafProfileKernelTotalCdCoeffRead
    leafDiffFamilyCoeffRead leafDiffCoeffRead
    qLeafProfileKernelTotalCdCoeff
    qLeafProfileKernelRemainderCdCoeff
    qLeafScalarCanonicalProfileBlockCdCoeff
    oddBReadEncode oddBReadLocalCdCoeff
  simp_rw [oddBReadKernelAt_cyclicSourceMap_eq_two_sums
    (n := n) (a := a) (b := b) (c := c) (d := d) hd X]
  have htail : ((n ^ (d - 1) : ℕ) : F) = 1 :=
    natCast_odd_eq_one_F
      (Odd.pow (a := n) (n := d - 1) hn)
  simp only [map_add]
  simp [leafVisibleKernelEquivCoord_zero, htail,
    leafBProfileKernelCoordEquivIndexDiff, Prod.fst_sum, Prod.snd_sum,
    Submodule.coe_sum, Finset.sum_apply,
    leafProfileKernelEquivIndexDiff_ite_fst_apply,
    leafProfileKernelEquivIndexDiff_ite_snd_apply]
  simp_rw [sum_ite_add_zero_local]
  have huu :
      (∑ z : ZVec n c, if t = vecSum z then
        (∑ ω : PassiveVisibleIndex n d hd,
          if u.1 = vecSum ω.1 then
            ((leafProfileKernelEquivIndexDiff hd
              (X (vecSum y) z)).1 ω).1 p
          else 0)
        else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        if u.1 = vecSum ω.1 then
          (∑ z : ZVec n c, if t = vecSum z then
            ((leafProfileKernelEquivIndexDiff hd
              (X (vecSum y) z)).1 ω).1 p
          else 0)
        else 0 :=
    sum_ite_sum_ite_comm_local
      (P := fun z : ZVec n c => t = vecSum z)
      (Q := fun ω : PassiveVisibleIndex n d hd => u.1 = vecSum ω.1)
      (f := fun z ω =>
        ((leafProfileKernelEquivIndexDiff hd
          (X (vecSum y) z)).1 ω).1 p)
  have hsu :
      (∑ z : ZVec n c, if t = vecSum z + 1 then
        (∑ ω : PassiveVisibleIndex n d hd,
          if u.1 = vecSum ω.1 then
            ((leafProfileKernelEquivIndexDiff hd
              (X (vecSum y + 1) z)).1 ω).1 p
          else 0)
        else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        if u.1 = vecSum ω.1 then
          (∑ z : ZVec n c, if t = vecSum z + 1 then
            ((leafProfileKernelEquivIndexDiff hd
              (X (vecSum y + 1) z)).1 ω).1 p
          else 0)
        else 0 :=
    sum_ite_sum_ite_comm_local
      (P := fun z : ZVec n c => t = vecSum z + 1)
      (Q := fun ω : PassiveVisibleIndex n d hd => u.1 = vecSum ω.1)
      (f := fun z ω =>
        ((leafProfileKernelEquivIndexDiff hd
          (X (vecSum y + 1) z)).1 ω).1 p)
  have hu0 :
      (∑ z : ZVec n c, if t = vecSum z then
        (∑ ω : PassiveVisibleIndex n d hd,
          if (0 : I n) = vecSum ω.1 then
            ((leafProfileKernelEquivIndexDiff hd
              (X (vecSum y) z)).1 ω).1 p
          else 0)
        else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        if (0 : I n) = vecSum ω.1 then
          (∑ z : ZVec n c, if t = vecSum z then
            ((leafProfileKernelEquivIndexDiff hd
              (X (vecSum y) z)).1 ω).1 p
          else 0)
        else 0 :=
    sum_ite_sum_ite_comm_local
      (P := fun z : ZVec n c => t = vecSum z)
      (Q := fun ω : PassiveVisibleIndex n d hd => (0 : I n) = vecSum ω.1)
      (f := fun z ω =>
        ((leafProfileKernelEquivIndexDiff hd
          (X (vecSum y) z)).1 ω).1 p)
  have hs0 :
      (∑ z : ZVec n c, if t = vecSum z + 1 then
        (∑ ω : PassiveVisibleIndex n d hd,
          if (0 : I n) = vecSum ω.1 then
            ((leafProfileKernelEquivIndexDiff hd
              (X (vecSum y + 1) z)).1 ω).1 p
          else 0)
        else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        if (0 : I n) = vecSum ω.1 then
          (∑ z : ZVec n c, if t = vecSum z + 1 then
            ((leafProfileKernelEquivIndexDiff hd
              (X (vecSum y + 1) z)).1 ω).1 p
          else 0)
        else 0 :=
    sum_ite_sum_ite_comm_local
      (P := fun z : ZVec n c => t = vecSum z + 1)
      (Q := fun ω : PassiveVisibleIndex n d hd => (0 : I n) = vecSum ω.1)
      (f := fun z ω =>
        ((leafProfileKernelEquivIndexDiff hd
          (X (vecSum y + 1) z)).1 ω).1 p)
  rw [huu, hsu, hu0, hs0]
  ring

private theorem oddBRead_tailRead_cv_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X : I n → ZVec n c → LeafProfileKernel n a d)
    (ω : PassiveVisibleIndex n d hd)
    (y : YVec n b) (t : I n)
    (p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}) :
    ((leafBReadTailReadMap hd :
        LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
          LeafBReadTarget n a b c d hd)
      (leafBProfileKernelCoordEquivIndexDiff
        (n := n) (a := a) (c := c) (d := d) hd X)).2
        ((ω, (y, t)), p)
      =
    (oddBReadEncode
      (n := n) (a := a) (b := b) (c := c) (d := d) hd
      (oddBReadCyclicSourceMap n c (LeafProfileKernel n a d) X)).2
        ((ω, (y, t)), p) := by
  classical
  change
    qLeafProfileKernelTotalCvCoeffRead hd
        (0 : LeafVisibleKernel n b c d)
        (leafBProfileKernelCoordEquivIndexDiff hd X) ((ω, (y, t)), p)
      =
    _
  unfold qLeafProfileKernelTotalCvCoeffRead
    leafScalarFamilyCoeffRead
    qLeafProfileKernelTotalCvCoeff
    qLeafProfileKernelRemainderCvCoeff
    qLeafProfileKernelRemainderCvCoeffLeft
    qLeafProfileKernelRemainderCvCoeffRight
    qLeafProfileKernelProfileCvCoeff
    qLeafProfileKernelProfileCvCoeffLeft
    qLeafProfileKernelProfileCvCoeffRight
    qLeafProfileKernelVisibleScalarCvCoeff
    qLeafProfileKernelVisibleScalarCvCoeffLeft
    qLeafProfileKernelVisibleScalarCvCoeffRight
    oddBReadEncode oddBReadLocalCvCoeff
  simp_rw [oddBReadKernelAt_cyclicSourceMap_eq_two_sums
    (n := n) (a := a) (b := b) (c := c) (d := d) hd X]
  simp only [map_add]
  simp [leafVisibleKernelEquivCoord_zero,
    leafBProfileKernelCoordEquivIndexDiff, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_apply,
    leafProfileKernelEquivIndexDiff_ite_fst_apply,
    leafProfileKernelEquivIndexDiff_ite_snd_apply]
  ring

private theorem leafBReadTailReadMap_factor_oddBReadEncode
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    (leafBReadTailReadMap hd :
        LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
          LeafBReadTarget n a b c d hd) XB
      =
    oddBReadEncode hd
      (oddBReadCyclicXBMap
        (n := n) (a := a) (c := c) (d := d) hd XB) := by
  let e :=
    leafBProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd
  let X : I n → ZVec n c → LeafProfileKernel n a d := e.symm XB
  have hXB : e X = XB := e.apply_symm_apply XB
  rw [← hXB]
  apply Prod.ext
  · funext ips
    rcases ips with ⟨⟨y, t⟩, ⟨p, u⟩⟩
    simpa [oddBReadCyclicXBMap, X, e] using
      oddBRead_tailRead_cd_apply
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hd hn X y t p u
  · funext ips
    rcases ips with ⟨⟨ω, y, t⟩, p⟩
    simpa [oddBReadCyclicXBMap, X, e] using
      oddBRead_tailRead_cv_apply
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hd X ω y t p

private theorem ker_leafBReadTailReadMap_eq_oddBReadCyclicXBMap
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) (hn : Odd n) :
    LinearMap.ker
        (leafBReadTailReadMap hd :
          LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
            LeafBReadTarget n a b c d hd)
      =
    LinearMap.ker
      (oddBReadCyclicXBMap
        (n := n) (a := a) (c := c) (d := d) hd) := by
  ext XB
  simp only [LinearMap.mem_ker]
  constructor
  · intro hread
    apply (oddBReadEncode_eq_zero_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hd hn _).1
    rw [← leafBReadTailReadMap_factor_oddBReadEncode
      (n := n) (a := a) (b := b) (c := c) (d := d) hd hn XB]
    exact hread
  · intro hcyc
    rw [leafBReadTailReadMap_factor_oddBReadEncode
      (n := n) (a := a) (b := b) (c := c) (d := d) hd hn XB]
    exact (oddBReadEncode_eq_zero_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hd hn _).2 hcyc

private theorem finrank_ker_leafBReadTailReadMap_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n) :
    Module.finrank F
        (LinearMap.ker
          (leafBReadTailReadMap hd :
            LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
              LeafBReadTarget n a b c d hd))
      =
    n * (n ^ c - (n - 1)) * oddBReadProfileRankNat n a d := by
  rw [ker_leafBReadTailReadMap_eq_oddBReadCyclicXBMap hb hd hn]
  exact finrank_ker_oddBReadCyclicXBMap hc hd

/-!
## Explicit cyclic preimage of the visible target
-/

private def oddBReadLocalVisibleV
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (h : PassiveVisibleIndex n d hd → F)
    (ω : PassiveVisibleIndex n d hd) :
    LeafScalarProfileKernel n a := by
  classical
  refine ⟨fun p : PVec n a =>
    if p = (zeroVec : PVec n a) then 0 else h ω, ?_⟩
  rw [LinearMap.mem_ker]
  change
    (∑ p : PVec n a,
      if p = (zeroVec : PVec n a) then 0 else h ω) = 0
  have hcardP : ((Fintype.card (PVec n a) : ℕ) : F) = 1 := by
    simpa [PVec, card_vec] using
      natCast_odd_eq_one_F
        (Odd.pow (a := n) (n := a - 1) hn)
  have hpoint :
      (∑ p : PVec n a,
        if p = (zeroVec : PVec n a) then h ω else 0) = h ω := by
    rw [Finset.sum_eq_single (zeroVec : PVec n a)]
    · simp
    · intro p _ hp
      simp [hp]
    · simp
  calc
    (∑ p : PVec n a,
      if p = (zeroVec : PVec n a) then 0 else h ω)
        =
      (∑ _p : PVec n a, h ω)
        +
      ∑ p : PVec n a,
        if p = (zeroVec : PVec n a) then h ω else 0 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro p _
          by_cases hp : p = (zeroVec : PVec n a)
          · simp [hp, F_add_self]
          · simp [hp]
    _ = h ω + h ω := by
          rw [hpoint]
          have hconst :
              (∑ _p : PVec n a, h ω) =
                (Fintype.card (PVec n a) : F) * h ω := by
            simp [Finset.sum_const, nsmul_eq_mul]
          rw [hconst, hcardP, one_mul]
    _ = 0 := F_add_self _

private def oddBReadLocalVisibleD
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (h : PassiveVisibleIndex n d hd → F)
    (_p : PVec n a) : ZeroSumProfile n := by
  classical
  refine ⟨fun u =>
    oddBReadPassiveFiberSum hd h u + ∑ ω, h ω, ?_⟩
  change
    (∑ u : I n,
      (oddBReadPassiveFiberSum hd h u + ∑ ω, h ω)) = 0
  rw [Finset.sum_add_distrib, sum_oddBReadPassiveFiberSum]
  have hncast : ((n : ℕ) : F) = 1 := natCast_odd_eq_one_F hn
  simp [Finset.sum_const, nsmul_eq_mul, I, ZMod.card, hncast, F_add_self]

private noncomputable def oddBReadLocalVisibleBuild
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (h : PassiveVisibleIndex n d hd → F) :
    LeafProfileKernel n a d :=
  (leafProfileKernelEquivIndexDiff
    (n := n) (a := a) (d := d) hd).symm
    (fun ω => oddBReadLocalVisibleV hd hn h ω,
      fun p => oddBReadLocalVisibleD hd hn h p)

private theorem oddBReadLocalVisibleBuild_fst_apply
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (h : PassiveVisibleIndex n d hd → F)
    (ω : PassiveVisibleIndex n d hd) (p : PVec n a) :
    ((leafProfileKernelEquivIndexDiff hd
      (oddBReadLocalVisibleBuild hd hn h)).1 ω).1 p
      =
    if p = (zeroVec : PVec n a) then 0 else h ω := by
  rw [oddBReadLocalVisibleBuild,
    (leafProfileKernelEquivIndexDiff hd).apply_symm_apply]
  rfl

private theorem oddBReadLocalVisibleBuild_snd_apply
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (h : PassiveVisibleIndex n d hd → F)
    (p : PVec n a) (u : I n) :
    ((leafProfileKernelEquivIndexDiff hd
      (oddBReadLocalVisibleBuild hd hn h)).2 p).1 u
      =
    oddBReadPassiveFiberSum hd h u + ∑ ω, h ω := by
  rw [oddBReadLocalVisibleBuild,
    (leafProfileKernelEquivIndexDiff hd).apply_symm_apply]
  rfl

private noncomputable def oddBReadLocalVisibleBuildLinearMap
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n) :
    (PassiveVisibleIndex n d hd → F) →ₗ[F]
      LeafProfileKernel n a d where
  toFun := oddBReadLocalVisibleBuild hd hn
  map_add' h k := by
    apply (leafProfileKernelEquivIndexDiff hd).injective
    rw [map_add]
    apply Prod.ext
    · funext ω
      apply Subtype.ext
      funext p
      simp only [Prod.fst_add, Pi.add_apply, Submodule.coe_add]
      simp_rw [oddBReadLocalVisibleBuild_fst_apply]
      by_cases hp : p = (zeroVec : PVec n a) <;> simp [hp]
    · funext p
      apply Subtype.ext
      funext u
      simp only [Prod.snd_add, Pi.add_apply, Submodule.coe_add]
      simp_rw [oddBReadLocalVisibleBuild_snd_apply]
      unfold oddBReadPassiveFiberSum
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      rw [sum_ite_add_zero_local]
      ring
  map_smul' r h := by
    apply (leafProfileKernelEquivIndexDiff hd).injective
    rw [map_smul]
    apply Prod.ext
    · funext ω
      apply Subtype.ext
      funext p
      simp only [Prod.smul_fst, Pi.smul_apply, Submodule.coe_smul,
        RingHom.id_apply]
      simp_rw [oddBReadLocalVisibleBuild_fst_apply]
      by_cases hp : p = (zeroVec : PVec n a) <;> simp [hp]
    · funext p
      apply Subtype.ext
      funext u
      simp only [Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul,
        RingHom.id_apply]
      simp_rw [oddBReadLocalVisibleBuild_snd_apply]
      unfold oddBReadPassiveFiberSum
      simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
      have hf :
          (∑ ω : PassiveVisibleIndex n d hd,
            if u = vecSum ω.1 then r * h ω else 0)
            =
          r * ∑ ω : PassiveVisibleIndex n d hd,
            if u = vecSum ω.1 then h ω else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro ω _
        by_cases hu : u = vecSum ω.1 <;> simp [hu]
      rw [hf, ← Finset.mul_sum]
      ring

private theorem oddBReadLocalVisibleBuild_cd_read
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (h : PassiveVisibleIndex n d hd → F)
    (p : PVec n a) (u : I n) :
    oddBReadLocalCdCoeff hd (oddBReadLocalVisibleBuild hd hn h) p u
        +
      oddBReadLocalCdCoeff hd (oddBReadLocalVisibleBuild hd hn h) p 0
      =
    if p = (zeroVec : PVec n a) then
      oddBReadPassiveFiberSum hd h u
        + oddBReadPassiveFiberSum hd h 0
    else 0 := by
  classical
  unfold oddBReadLocalCdCoeff
  simp_rw [oddBReadLocalVisibleBuild_fst_apply,
    oddBReadLocalVisibleBuild_snd_apply]
  by_cases hp : p = (zeroVec : PVec n a)
  · simp [hp, oddBReadPassiveFiberSum]
    ring_nf
    simp [show (2 : F) = 0 by decide]
  · simp [hp, oddBReadPassiveFiberSum]
    ring_nf
    simp [show (2 : F) = 0 by decide]

private theorem oddBReadLocalVisibleBuild_cv_read
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (h : PassiveVisibleIndex n d hd → F)
    (ω : PassiveVisibleIndex n d hd)
    (p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}) :
    oddBReadLocalCvCoeff hd (oddBReadLocalVisibleBuild hd hn h) ω p.1
        +
      oddBReadLocalCvCoeff hd (oddBReadLocalVisibleBuild hd hn h) ω
        (zeroVec : PVec n a)
      =
    h ω := by
  unfold oddBReadLocalCvCoeff
  simp_rw [oddBReadLocalVisibleBuild_fst_apply,
    oddBReadLocalVisibleBuild_snd_apply]
  simp [p.2]
  ring_nf
  simp [show (2 : F) = 0 by decide]

private def oddBReadVisibleCyc
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (s t : I n) (ω : PassiveVisibleIndex n d hd) : F :=
  (∑ z : ZVec n c,
    if t = vecSum z then
      ((leafVisibleKernelEquivCoord hd H) ω).1.1 s z
    else 0)
  +
  ∑ z : ZVec n c,
    if t = vecSum z + 1 then
      ((leafVisibleKernelEquivCoord hd H) ω).1.1 (s + 1) z
    else 0

private theorem leafBReadVisibleBAdjoint_cv_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd)
    (y : YVec n b) (t : I n)
    (p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}) :
    (leafBReadVisibleBAdjoint hd H).2 ((ω, (y, t)), p)
      =
    oddBReadVisibleCyc hd H (vecSum y) t ω := by
  classical
  unfold leafBReadVisibleBAdjoint
    qLeafProfileKernelTotalBCoeffRead
    qLeafProfileKernelTotalCvCoeffRead
    leafScalarFamilyCoeffRead
    qLeafProfileKernelTotalCvCoeff
    qLeafProfileKernelRemainderCvCoeff
    qLeafProfileKernelRemainderCvCoeffLeft
    qLeafProfileKernelRemainderCvCoeffRight
    qLeafProfileKernelProfileCvCoeff
    qLeafProfileKernelProfileCvCoeffLeft
    qLeafProfileKernelProfileCvCoeffRight
    qLeafProfileKernelVisibleScalarCvCoeff
    qLeafProfileKernelVisibleScalarCvCoeffLeft
    qLeafProfileKernelVisibleScalarCvCoeffRight
    oddBReadVisibleCyc
  simp [p.2, leafBProfileKernelCoordEquivIndexDiff]

private theorem leafBReadVisibleBAdjoint_cd_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (y : YVec n b) (t : I n) (p : PVec n a) (u : NonzeroI n) :
    (leafBReadVisibleBAdjoint hd H).1 ((y, t), (p, u))
      =
    if p = (zeroVec : PVec n a) then
      oddBReadPassiveFiberSum hd
          (oddBReadVisibleCyc hd H (vecSum y) t) u.1
        +
      oddBReadPassiveFiberSum hd
          (oddBReadVisibleCyc hd H (vecSum y) t) 0
    else 0 := by
  classical
  unfold leafBReadVisibleBAdjoint
    qLeafProfileKernelTotalBCoeffRead
    qLeafProfileKernelTotalCdCoeffRead
    leafDiffFamilyCoeffRead leafDiffCoeffRead
    qLeafProfileKernelTotalCdCoeff
    qLeafProfileKernelRemainderCdCoeff
    qLeafScalarCanonicalProfileBlockCdCoeff
    oddBReadPassiveFiberSum oddBReadVisibleCyc
  by_cases hp : p = (zeroVec : PVec n a) <;> simp [hp]

private theorem sum_oddBReadVisibleCyc_diagonal_eq_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (r : I n) (ω : PassiveVisibleIndex n d hd) :
    (∑ s : I n, oddBReadVisibleCyc hd H s (r - s) ω) = 0 := by
  classical
  let f : I n → F := fun s =>
    ∑ z : ZVec n c,
      if r - s = vecSum z then
        ((leafVisibleKernelEquivCoord hd H) ω).1.1 s z
      else 0
  let g : I n → F := fun s =>
    ∑ z : ZVec n c,
      if r - s = vecSum z + 1 then
        ((leafVisibleKernelEquivCoord hd H) ω).1.1 (s + 1) z
      else 0
  have hgf (s : I n) : g s = f (s + 1) := by
    unfold f g
    refine Finset.sum_congr rfl ?_
    intro z _
    have hiff :
        r - s = vecSum z + 1 ↔ r - (s + 1) = vecSum z := by
      constructor <;> intro h
      · calc
          r - (s + 1) = (r - s) - 1 := by abel
          _ = (vecSum z + 1) - 1 := by rw [h]
          _ = vecSum z := by abel
      · calc
          r - s = (r - (s + 1)) + 1 := by abel
          _ = vecSum z + 1 := by rw [h]
    simp only [hiff]
  have hsumg : (∑ s : I n, g s) = ∑ s : I n, f s := by
    simp_rw [hgf]
    exact sum_zmod_add_right (n := n) 1 f
  change (∑ s : I n, (f s + g s)) = 0
  rw [Finset.sum_add_distrib, hsumg, F_add_self]

private noncomputable def oddBReadVisibleCyclicPreimage
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (H : LeafVisibleKernel n b c d) :
    I n → ZeroSumProfileM n (LeafProfileKernel n a d) :=
  fun r => ⟨
    fun s =>
      oddBReadLocalVisibleBuild hd hn
        (oddBReadVisibleCyc hd H s (r - s)),
    by
      unfold ZeroSumProfileM
      rw [LinearMap.mem_ker]
      change
        (∑ s : I n,
          oddBReadLocalVisibleBuild hd hn
            (oddBReadVisibleCyc hd H s (r - s))) = 0
      let L :=
        oddBReadLocalVisibleBuildLinearMap
          (n := n) (a := a) (d := d) hd hn
      change
        (∑ s : I n,
          L (oddBReadVisibleCyc hd H s (r - s))) = 0
      rw [← map_sum]
      have hsum :
          (∑ s : I n,
            oddBReadVisibleCyc hd H s (r - s))
            =
          (0 : PassiveVisibleIndex n d hd → F) := by
        funext ω
        simpa only [Finset.sum_apply, Pi.zero_apply] using
          sum_oddBReadVisibleCyc_diagonal_eq_zero hd H r ω
      rw [hsum, map_zero]
  ⟩

private theorem oddBReadKernelAt_visibleCyclicPreimage
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (H : LeafVisibleKernel n b c d)
    (y : YVec n b) (t : I n) :
    oddBReadKernelAt hd
        (oddBReadVisibleCyclicPreimage
          (n := n) (a := a) (b := b) (c := c) (d := d) hd hn H) y t
      =
    oddBReadLocalVisibleBuild hd hn
      (oddBReadVisibleCyc hd H (vecSum y) t) := by
  unfold oddBReadKernelAt oddBReadVisibleCyclicPreimage
  congr 3
  abel

private theorem oddBReadEncode_visibleCyclicPreimage
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (H : LeafVisibleKernel n b c d) :
    oddBReadEncode hd
        (oddBReadVisibleCyclicPreimage
          (n := n) (a := a) (b := b) (c := c) (d := d) hd hn H)
      =
    leafBReadVisibleBAdjoint hd H := by
  apply Prod.ext
  · funext ips
    rcases ips with ⟨⟨y, t⟩, p, u⟩
    rw [leafBReadVisibleBAdjoint_cd_apply]
    unfold oddBReadEncode
    simp only
    rw [oddBReadKernelAt_visibleCyclicPreimage,
      oddBReadLocalVisibleBuild_cd_read]
  · funext ips
    rcases ips with ⟨⟨ω, y, t⟩, p⟩
    rw [leafBReadVisibleBAdjoint_cv_apply]
    unfold oddBReadEncode
    simp only
    rw [oddBReadKernelAt_visibleCyclicPreimage,
      oddBReadLocalVisibleBuild_cv_read]

private theorem exists_oddBRead_exact_preimage
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (H : LeafVisibleKernel n b c d) :
    ∃ XB0 : LeafBProfileKernelIndexDiffCoord n a c d hd,
      (leafBReadTailReadMap hd :
          LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
            LeafBReadTarget n a b c d hd) XB0
        =
      leafBReadVisibleBAdjoint hd H := by
  obtain ⟨XB0, hXB0⟩ :=
    oddBReadCyclicXBMap_surjective
      (n := n) (a := a) (c := c) (d := d) hc hd
      (oddBReadVisibleCyclicPreimage
        (n := n) (a := a) (b := b) (c := c) (d := d) hd hn H)
  refine ⟨XB0, ?_⟩
  rw [leafBReadTailReadMap_factor_oddBReadEncode hd hn, hXB0]
  exact oddBReadEncode_visibleCyclicPreimage hd hn H

private theorem exists_oddBRead_totalBCoeffCondition
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (H : LeafVisibleKernel n b c d) :
    ∃ XB0 : LeafBProfileKernelIndexDiffCoord n a c d hd,
      TotalBCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0 := by
  obtain ⟨XB0, hXB0⟩ :=
    exists_oddBRead_exact_preimage
      (n := n) (a := a) (b := b) (c := c) (d := d) hc hd hn H
  refine ⟨XB0,
    (TotalBCoeffCondition_iff_zeroH_read_eq_const
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0).2 ?_⟩
  simpa [leafBReadTailReadMap, leafBReadVisibleBAdjoint] using hXB0

private noncomputable def oddBReadLocalCvCoeffLinearMap
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (ω : PassiveVisibleIndex n d hd) (p : PVec n a) :
    LeafProfileKernel n a d →ₗ[F] F where
  toFun K := oddBReadLocalCvCoeff hd K ω p
  map_add' K L := by
    unfold oddBReadLocalCvCoeff
    simp only [map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      Submodule.coe_add]
    ring
  map_smul' r K := by
    unfold oddBReadLocalCvCoeff
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
      Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    ring

private theorem leafBReadKernelScalarBTrace_coord_eq_localCv
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (X : I n → ZVec n c → LeafProfileKernel n a d)
    (ω : PassiveVisibleIndex n d hd) (s : I n) (z : ZVec n c) :
    leafBReadKernelScalarBTrace hd
        (leafBProfileKernelCoordEquivIndexDiff hd X) ω s z
      =
    oddBReadLocalCvCoeff hd (X s z) ω (zeroVec : PVec n a) := by
  rfl

private theorem TAdjScalarFun_leafBReadKernelScalarBTrace_eq_localCvKernelAt
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (ω : PassiveVisibleIndex n d hd)
    (y : YVec n b) (t : I n) :
    Core3loop.TAdjScalarFun
        (b := b) (c := c) (n := n)
        (leafBReadKernelScalarBTrace hd XB ω) y t
      =
    oddBReadLocalCvCoeff hd
      (oddBReadKernelAt hd
        (oddBReadCyclicXBMap
          (n := n) (a := a) (c := c) (d := d) hd XB) y t)
      ω (zeroVec : PVec n a) := by
  classical
  let e :=
    leafBProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd
  let X : I n → ZVec n c → LeafProfileKernel n a d := e.symm XB
  have hXB : e X = XB := e.apply_symm_apply XB
  rw [← hXB]
  unfold Core3loop.TAdjScalarFun Core3loop.BAgg
  dsimp only [e]
  simp_rw [leafBReadKernelScalarBTrace_coord_eq_localCv]
  rw [show
      oddBReadCyclicXBMap hd (e X) =
        oddBReadCyclicSourceMap n c (LeafProfileKernel n a d) X by
      simp [oddBReadCyclicXBMap, e]]
  rw [oddBReadKernelAt_cyclicSourceMap_eq_two_sums]
  change
    (∑ z : ZVec n c,
        if vecSum z = t then
          oddBReadLocalCvCoeff hd (X (vecSum y) z) ω
            (zeroVec : PVec n a)
        else 0)
      +
    (∑ z : ZVec n c,
        if vecSum z = t - 1 then
          oddBReadLocalCvCoeff hd (X (vecSum y + 1) z) ω
            (zeroVec : PVec n a)
        else 0)
      =
    oddBReadLocalCvCoeffLinearMap hd ω (zeroVec : PVec n a)
      ((∑ z : ZVec n c,
          if t = vecSum z then X (vecSum y) z else 0)
        +
       ∑ z : ZVec n c,
          if t = vecSum z + 1 then X (vecSum y + 1) z else 0)
  rw [map_add, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = t
    · rw [if_pos hz, if_pos (Eq.symm hz)]
      rfl
    · rw [if_neg hz, if_neg (fun h => hz h.symm)]
      rw [map_zero]
  · refine Finset.sum_congr rfl ?_
    intro z _
    have hiff : vecSum z = t - 1 ↔ t = vecSum z + 1 := by
      constructor <;> intro h
      · rw [h]
        abel
      · rw [h]
        abel
    by_cases hz : vecSum z = t - 1
    · rw [if_pos hz, if_pos (hiff.mp hz)]
      rfl
    · rw [if_neg hz, if_neg (fun h => hz (hiff.mpr h))]
      rw [map_zero]

private def oddBReadCyclicPhase
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (U : I n → ZeroSumProfileM n (LeafProfileKernel n a d)) : F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    Core3loop.cPairScalar (b := b) (n := n)
      (fun y t =>
        oddBReadLocalCvCoeff hd (oddBReadKernelAt hd U y t)
          ω (zeroVec : PVec n a))
      ((leafVisibleKernelEquivCoord hd H) ω).1.2

private theorem
    qLeafProfileKernelTotalCvConstLinearMap_factor_oddBReadCyclicPhase
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvConstLinearMap hd H XB
      =
    oddBReadCyclicPhase hd H
      (oddBReadCyclicXBMap
        (n := n) (a := a) (c := c) (d := d) hd XB) := by
  rw [qLeafProfileKernelTotalCvConstLinearMap_eq_scalarBTrace_visibleC]
  unfold oddBReadCyclicPhase
  refine Finset.sum_congr rfl ?_
  intro ω _
  rw [Core3loop.qScalar_eq_cPair_TAdjScalarFun]
  congr 1
  funext y t
  exact
    TAdjScalarFun_leafBReadKernelScalarBTrace_eq_localCvKernelAt
      (n := n) (a := a) (b := b) (c := c) (d := d) hd XB ω y t

private theorem oddBRead_phase_kills_read_kernel
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) (hn : Odd n)
    (H : LeafVisibleKernel n b c d) :
    (qLeafProfileKernelTotalCvConstLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H).comp
        (LinearMap.ker
          (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd)).subtype
      =
    0 := by
  apply LinearMap.ext
  rintro ⟨XB, hXB⟩
  change qLeafProfileKernelTotalCvConstLinearMap hd H XB = 0
  rw [qLeafProfileKernelTotalCvConstLinearMap_factor_oddBReadCyclicPhase]
  have hcyc :
      oddBReadCyclicXBMap
          (n := n) (a := a) (c := c) (d := d) hd XB
        =
      0 := by
    rw [← LinearMap.mem_ker]
    rw [← ker_leafBReadTailReadMap_eq_oddBReadCyclicXBMap hb hd hn]
    exact hXB
  rw [hcyc]
  simp [oddBReadCyclicPhase, oddBReadKernelAt,
    oddBReadLocalCvCoeff, Core3loop.cPairScalar]

private theorem oddBReadLocalVisibleBuild_cv_zero
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (h : PassiveVisibleIndex n d hd → F)
    (ω : PassiveVisibleIndex n d hd) :
    oddBReadLocalCvCoeff hd (oddBReadLocalVisibleBuild hd hn h)
        ω (zeroVec : PVec n a)
      =
    oddBReadPassiveFiberSum hd h (vecSum ω.1) + ∑ ω', h ω' := by
  unfold oddBReadLocalCvCoeff
  rw [oddBReadLocalVisibleBuild_fst_apply,
    oddBReadLocalVisibleBuild_snd_apply]
  simp

private theorem oddBReadVisibleCyc_eq_TAdjScalarFun
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (y : YVec n b) (t : I n)
    (ω : PassiveVisibleIndex n d hd) :
    oddBReadVisibleCyc hd H (vecSum y) t ω
      =
    Core3loop.TAdjScalarFun
      (((leafVisibleKernelEquivCoord hd H) ω).1.1) y t := by
  classical
  have hsumY : Core3loop.sumY y = vecSum y := rfl
  have hsumZ : ∀ z : ZVec n c, Core3loop.sumZ z = vecSum z :=
    fun _ => rfl
  unfold oddBReadVisibleCyc Core3loop.TAdjScalarFun Core3loop.BAgg
  simp only [hsumY, hsumZ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro z _
    by_cases h : t = vecSum z
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hz => h hz.symm)]
  · refine Finset.sum_congr rfl ?_
    intro z _
    have hiff :
        t = vecSum z + 1 ↔ vecSum z = t - 1 := by
      constructor <;> intro h
      · rw [h]
        abel
      · rw [h]
        abel
    by_cases h : t = vecSum z + 1
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hz => h (hiff.mpr hz))]

private noncomputable def oddBReadVisibleTotal
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    LeafScalarVisibleKernel n b c :=
  ∑ ω : PassiveVisibleIndex n d hd,
    (leafVisibleKernelEquivCoord hd H) ω

private noncomputable def oddBReadVisibleClass
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (u : I n) :
    LeafScalarVisibleKernel n b c :=
  ∑ ω : PassiveVisibleIndex n d hd,
    if u = vecSum ω.1 then
      (leafVisibleKernelEquivCoord hd H) ω
    else 0

private theorem oddBReadVisibleTotal_bcoef
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (oddBReadVisibleTotal hd H).1.1
      =
    ∑ ω : PassiveVisibleIndex n d hd,
      ((leafVisibleKernelEquivCoord hd H) ω).1.1 := by
  funext s z
  simp [oddBReadVisibleTotal, Prod.fst_sum, Submodule.coe_sum,
    Finset.sum_apply]

private theorem oddBReadVisibleTotal_ccoef
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (oddBReadVisibleTotal hd H).1.2
      =
    ∑ ω : PassiveVisibleIndex n d hd,
      ((leafVisibleKernelEquivCoord hd H) ω).1.2 := by
  funext y t
  simp [oddBReadVisibleTotal, Prod.snd_sum, Submodule.coe_sum,
    Finset.sum_apply]

private theorem oddBReadVisibleClass_bcoef
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (u : I n) :
    (oddBReadVisibleClass hd H u).1.1
      =
    ∑ ω : PassiveVisibleIndex n d hd,
      if u = vecSum ω.1 then
        ((leafVisibleKernelEquivCoord hd H) ω).1.1
      else 0 := by
  unfold oddBReadVisibleClass
  rw [Submodule.coe_sum]
  rw [Prod.fst_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _
  by_cases h : u = vecSum ω.1 <;> simp [h]

private theorem oddBReadVisibleClass_ccoef
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (u : I n) :
    (oddBReadVisibleClass hd H u).1.2
      =
    ∑ ω : PassiveVisibleIndex n d hd,
      if u = vecSum ω.1 then
        ((leafVisibleKernelEquivCoord hd H) ω).1.2
      else 0 := by
  unfold oddBReadVisibleClass
  rw [Submodule.coe_sum]
  rw [Prod.snd_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _
  by_cases h : u = vecSum ω.1 <;> simp [h]

private theorem oddBReadVisibleTotal_TAdj
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (y : YVec n b) (t : I n) :
    Core3loop.TAdjScalarFun
        (oddBReadVisibleTotal hd H).1.1 y t
      =
    ∑ ω : PassiveVisibleIndex n d hd,
      oddBReadVisibleCyc hd H (vecSum y) t ω := by
  rw [oddBReadVisibleTotal_bcoef]
  have hm :=
    map_sum
      (Core3loop.TAdjScalar (b := b) (c := c) (n := n))
      (fun ω : PassiveVisibleIndex n d hd =>
        ((leafVisibleKernelEquivCoord hd H) ω).1.1)
      Finset.univ
  have hp := congrFun (congrFun hm y) t
  calc
    Core3loop.TAdjScalarFun
        (∑ ω : PassiveVisibleIndex n d hd,
          ((leafVisibleKernelEquivCoord hd H) ω).1.1) y t
        =
      (Core3loop.TAdjScalar
        (∑ ω : PassiveVisibleIndex n d hd,
          ((leafVisibleKernelEquivCoord hd H) ω).1.1)) y t := by rfl
    _ =
      (∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.TAdjScalar
          (((leafVisibleKernelEquivCoord hd H) ω).1.1)) y t := hp
    _ =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.TAdjScalarFun
          (((leafVisibleKernelEquivCoord hd H) ω).1.1) y t := by
            simp only [Finset.sum_apply]
            rfl
    _ =
      ∑ ω : PassiveVisibleIndex n d hd,
        oddBReadVisibleCyc hd H (vecSum y) t ω := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          exact
            (oddBReadVisibleCyc_eq_TAdjScalarFun hd H y t ω).symm

private theorem oddBReadVisibleClass_TAdj
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (u : I n)
    (y : YVec n b) (t : I n) :
    Core3loop.TAdjScalarFun
        (oddBReadVisibleClass hd H u).1.1 y t
      =
    oddBReadPassiveFiberSum hd
      (oddBReadVisibleCyc hd H (vecSum y) t) u := by
  rw [oddBReadVisibleClass_bcoef]
  have hm :=
    map_sum
      (Core3loop.TAdjScalar (b := b) (c := c) (n := n))
      (fun ω : PassiveVisibleIndex n d hd =>
        if u = vecSum ω.1 then
          ((leafVisibleKernelEquivCoord hd H) ω).1.1
        else 0)
      Finset.univ
  have hp := congrFun (congrFun hm y) t
  calc
    Core3loop.TAdjScalarFun
        (∑ ω : PassiveVisibleIndex n d hd,
          if u = vecSum ω.1 then
            ((leafVisibleKernelEquivCoord hd H) ω).1.1
          else 0) y t
        =
      (Core3loop.TAdjScalar
        (∑ ω : PassiveVisibleIndex n d hd,
          if u = vecSum ω.1 then
            ((leafVisibleKernelEquivCoord hd H) ω).1.1
          else 0)) y t := by rfl
    _ =
      (∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.TAdjScalar
          (if u = vecSum ω.1 then
            ((leafVisibleKernelEquivCoord hd H) ω).1.1
          else 0)) y t := hp
    _ =
      ∑ ω : PassiveVisibleIndex n d hd,
        if u = vecSum ω.1 then
          Core3loop.TAdjScalarFun
            (((leafVisibleKernelEquivCoord hd H) ω).1.1) y t
        else 0 := by
          simp only [Finset.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hu : u = vecSum ω.1
          · rw [if_pos hu, if_pos hu]
            rfl
          · rw [if_neg hu, if_neg hu, map_zero]
            rfl
    _ =
      oddBReadPassiveFiberSum hd
        (oddBReadVisibleCyc hd H (vecSum y) t) u := by
          unfold oddBReadPassiveFiberSum
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hu : u = vecSum ω.1
          · rw [if_pos hu, if_pos hu]
            exact
              (oddBReadVisibleCyc_eq_TAdjScalarFun hd H y t ω).symm
          · rw [if_neg hu, if_neg hu]

private theorem qScalar_leaf_visible_zero
    {n b c : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (L : LeafScalarVisibleKernel n b c) :
    Core3loop.qScalar (b := b) (c := c) (n := n) L.1.1 L.1.2
      =
    0 := by
  simpa [leafScalarVisibleKernelEquivCore3] using
    Core3loop.qScalar_eq_zero_on_visible_of_odd
      (b := b) (c := c) (n := n) hb hc hn
      (leafScalarVisibleKernelEquivCore3
        (n := n) (b := b) (c := c) L)

private theorem oddBReadLocalVisiblePhase_normal
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd)
    (y : YVec n b) (t : I n) :
    oddBReadLocalCvCoeff hd
        (oddBReadLocalVisibleBuild hd hn
          (oddBReadVisibleCyc hd H (vecSum y) t))
        ω (zeroVec : PVec n a)
      =
    Core3loop.TAdjScalarFun
      ((oddBReadVisibleClass hd H (vecSum ω.1)
          + oddBReadVisibleTotal hd H).1.1) y t := by
  rw [oddBReadLocalVisibleBuild_cv_zero]
  rw [← oddBReadVisibleClass_TAdj hd H (vecSum ω.1) y t]
  rw [← oddBReadVisibleTotal_TAdj hd H y t]
  have hadd :=
    congrFun
      (congrFun
        ((Core3loop.TAdjScalar (b := b) (c := c) (n := n)).map_add
          (oddBReadVisibleClass hd H (vecSum ω.1)).1.1
          (oddBReadVisibleTotal hd H).1.1) y) t
  calc
    Core3loop.TAdjScalarFun
          (oddBReadVisibleClass hd H (vecSum ω.1)).1.1 y t
        +
        Core3loop.TAdjScalarFun
          (oddBReadVisibleTotal hd H).1.1 y t
        =
      (Core3loop.TAdjScalar
        ((oddBReadVisibleClass hd H (vecSum ω.1)).1.1
          + (oddBReadVisibleTotal hd H).1.1)) y t := hadd.symm
    _ =
      Core3loop.TAdjScalarFun
        ((oddBReadVisibleClass hd H (vecSum ω.1)
            + oddBReadVisibleTotal hd H).1.1) y t := by rfl

private theorem oddBReadCyclicPhase_visibleCyclicPreimage_eq_sum_qScalar
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (H : LeafVisibleKernel n b c d) :
    oddBReadCyclicPhase hd H
        (oddBReadVisibleCyclicPreimage
          (n := n) (a := a) (b := b) (c := c) (d := d) hd hn H)
      =
    ∑ ω : PassiveVisibleIndex n d hd,
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (oddBReadVisibleClass hd H (vecSum ω.1)
          + oddBReadVisibleTotal hd H).1.1
        ((leafVisibleKernelEquivCoord hd H) ω).1.2 := by
  unfold oddBReadCyclicPhase
  refine Finset.sum_congr rfl ?_
  intro ω _
  rw [Core3loop.qScalar_eq_cPair_TAdjScalarFun]
  congr 1
  funext y t
  rw [oddBReadKernelAt_visibleCyclicPreimage]
  exact oddBReadLocalVisiblePhase_normal hd hn H ω y t

private theorem sum_qScalar_oddBReadVisibleTotal
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (∑ ω : PassiveVisibleIndex n d hd,
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (oddBReadVisibleTotal hd H).1.1
        ((leafVisibleKernelEquivCoord hd H) ω).1.2)
      =
    Core3loop.qScalar (b := b) (c := c) (n := n)
      (oddBReadVisibleTotal hd H).1.1
      (oddBReadVisibleTotal hd H).1.2 := by
  let L :=
    qScalarRightLinearMap (b := b) (c := c) (n := n)
      (oddBReadVisibleTotal hd H).1.1
  calc
    (∑ ω : PassiveVisibleIndex n d hd,
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (oddBReadVisibleTotal hd H).1.1
        ((leafVisibleKernelEquivCoord hd H) ω).1.2)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        L ((leafVisibleKernelEquivCoord hd H) ω).1.2 := by rfl
    _ =
      L (∑ ω : PassiveVisibleIndex n d hd,
        ((leafVisibleKernelEquivCoord hd H) ω).1.2) :=
        (map_sum L
          (fun ω : PassiveVisibleIndex n d hd =>
            ((leafVisibleKernelEquivCoord hd H) ω).1.2)
          Finset.univ).symm
    _ =
      L (oddBReadVisibleTotal hd H).1.2 := by
        rw [oddBReadVisibleTotal_ccoef]
    _ =
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (oddBReadVisibleTotal hd H).1.1
        (oddBReadVisibleTotal hd H).1.2 := by rfl

private theorem sum_qScalar_oddBReadVisibleClass
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (∑ ω : PassiveVisibleIndex n d hd,
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (oddBReadVisibleClass hd H (vecSum ω.1)).1.1
        ((leafVisibleKernelEquivCoord hd H) ω).1.2)
      =
    ∑ u : I n,
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (oddBReadVisibleClass hd H u).1.1
        (oddBReadVisibleClass hd H u).1.2 := by
  calc
    (∑ ω : PassiveVisibleIndex n d hd,
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (oddBReadVisibleClass hd H (vecSum ω.1)).1.1
        ((leafVisibleKernelEquivCoord hd H) ω).1.2)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        ∑ u : I n,
          if u = vecSum ω.1 then
            Core3loop.qScalar (b := b) (c := c) (n := n)
              (oddBReadVisibleClass hd H u).1.1
              ((leafVisibleKernelEquivCoord hd H) ω).1.2
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ω _
            symm
            rw [Finset.sum_eq_single (vecSum ω.1)]
            · simp
            · intro u _ hu
              simp [hu]
            · simp
    _ =
      ∑ u : I n,
        ∑ ω : PassiveVisibleIndex n d hd,
          if u = vecSum ω.1 then
            Core3loop.qScalar (b := b) (c := c) (n := n)
              (oddBReadVisibleClass hd H u).1.1
              ((leafVisibleKernelEquivCoord hd H) ω).1.2
          else 0 := by rw [Finset.sum_comm]
    _ =
      ∑ u : I n,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          (oddBReadVisibleClass hd H u).1.1
          (oddBReadVisibleClass hd H u).1.2 := by
            refine Finset.sum_congr rfl ?_
            intro u _
            let L :=
              qScalarRightLinearMap (b := b) (c := c) (n := n)
                (oddBReadVisibleClass hd H u).1.1
            calc
              (∑ ω : PassiveVisibleIndex n d hd,
                if u = vecSum ω.1 then
                  Core3loop.qScalar (b := b) (c := c) (n := n)
                    (oddBReadVisibleClass hd H u).1.1
                    ((leafVisibleKernelEquivCoord hd H) ω).1.2
                else 0)
                  =
                ∑ ω : PassiveVisibleIndex n d hd,
                  L (if u = vecSum ω.1 then
                    ((leafVisibleKernelEquivCoord hd H) ω).1.2
                  else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro ω _
                    by_cases hu : u = vecSum ω.1
                    · rw [if_pos hu, if_pos hu]
                      rfl
                    · rw [if_neg hu, if_neg hu, map_zero]
              _ =
                L (∑ ω : PassiveVisibleIndex n d hd,
                  if u = vecSum ω.1 then
                    ((leafVisibleKernelEquivCoord hd H) ω).1.2
                  else 0) :=
                    (map_sum L
                      (fun ω : PassiveVisibleIndex n d hd =>
                        if u = vecSum ω.1 then
                          ((leafVisibleKernelEquivCoord hd H) ω).1.2
                        else 0)
                      Finset.univ).symm
              _ =
                L (oddBReadVisibleClass hd H u).1.2 := by
                  rw [oddBReadVisibleClass_ccoef]
              _ =
                Core3loop.qScalar (b := b) (c := c) (n := n)
                  (oddBReadVisibleClass hd H u).1.1
                  (oddBReadVisibleClass hd H u).1.2 := by rfl

private theorem oddBReadCyclicPhase_visibleCyclicPreimage_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (H : LeafVisibleKernel n b c d) :
    oddBReadCyclicPhase hd H
        (oddBReadVisibleCyclicPreimage
          (n := n) (a := a) (b := b) (c := c) (d := d) hd hn H)
      =
    0 := by
  rw [oddBReadCyclicPhase_visibleCyclicPreimage_eq_sum_qScalar]
  calc
    (∑ ω : PassiveVisibleIndex n d hd,
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (oddBReadVisibleClass hd H (vecSum ω.1)
          + oddBReadVisibleTotal hd H).1.1
        ((leafVisibleKernelEquivCoord hd H) ω).1.2)
        =
      ∑ ω : PassiveVisibleIndex n d hd,
        (Core3loop.qScalar (b := b) (c := c) (n := n)
            (oddBReadVisibleClass hd H (vecSum ω.1)).1.1
            ((leafVisibleKernelEquivCoord hd H) ω).1.2
          +
         Core3loop.qScalar (b := b) (c := c) (n := n)
            (oddBReadVisibleTotal hd H).1.1
            ((leafVisibleKernelEquivCoord hd H) ω).1.2) := by
              refine Finset.sum_congr rfl ?_
              intro ω _
              simpa only [Prod.fst_add, Submodule.coe_add] using
                Core3loop.qScalar_add_left
                  (b := b) (c := c) (n := n)
                  (oddBReadVisibleClass hd H (vecSum ω.1)).1.1
                  (oddBReadVisibleTotal hd H).1.1
                  ((leafVisibleKernelEquivCoord hd H) ω).1.2
    _ =
      (∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          (oddBReadVisibleClass hd H (vecSum ω.1)).1.1
          ((leafVisibleKernelEquivCoord hd H) ω).1.2)
      +
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          (oddBReadVisibleTotal hd H).1.1
          ((leafVisibleKernelEquivCoord hd H) ω).1.2 := by
            rw [Finset.sum_add_distrib]
    _ =
      (∑ u : I n,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          (oddBReadVisibleClass hd H u).1.1
          (oddBReadVisibleClass hd H u).1.2)
      +
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (oddBReadVisibleTotal hd H).1.1
        (oddBReadVisibleTotal hd H).1.2 := by
          rw [sum_qScalar_oddBReadVisibleClass,
            sum_qScalar_oddBReadVisibleTotal]
    _ = 0 := by
      simp_rw [qScalar_leaf_visible_zero hb hc hn]
      simp

private theorem exists_oddBRead_exact_preimage_with_zero_phase
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (H : LeafVisibleKernel n b c d) :
    ∃ XB0 : LeafBProfileKernelIndexDiffCoord n a c d hd,
      TotalBCoeffCondition
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0
        ∧
      qLeafProfileKernelTotalCvConstLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0
        =
      0 := by
  obtain ⟨XB0, hXB0⟩ :=
    oddBReadCyclicXBMap_surjective
      (n := n) (a := a) (c := c) (d := d) hc hd
      (oddBReadVisibleCyclicPreimage
        (n := n) (a := a) (b := b) (c := c) (d := d) hd hn H)
  refine ⟨XB0, ?_, ?_⟩
  · apply
      (TotalBCoeffCondition_iff_zeroH_read_eq_const
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0).2
    change
      (leafBReadTailReadMap hd :
          LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
            LeafBReadTarget n a b c d hd) XB0
        =
      leafBReadVisibleBAdjoint hd H
    rw [leafBReadTailReadMap_factor_oddBReadEncode hd hn, hXB0]
    exact oddBReadEncode_visibleCyclicPreimage hd hn H
  · rw [
      qLeafProfileKernelTotalCvConstLinearMap_factor_oddBReadCyclicPhase,
      hXB0]
    exact
      oddBReadCyclicPhase_visibleCyclicPreimage_eq_zero hb hc hd hn H

/-- The one source-specific certificate still missing after the Round-1 API
and dimension audit.  It deliberately asserts only reachability of the
targets arising from visible `H`; it does not assert surjectivity onto the
whole (redundant) B-read target. -/
private structure OddBReadAffineFiberCertificate
    (n a b c d : ℕ) [NeZero n] (hd : 0 < d) : Prop where
  exact_preimage_with_zero_phase :
    ∀ H : LeafVisibleKernel n b c d,
      ∃ XB0 : LeafBProfileKernelIndexDiffCoord n a c d hd,
        TotalBCoeffCondition
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0
          ∧
        qLeafProfileKernelTotalCvConstLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB0
          =
        0
  phase_kills_read_kernel :
    ∀ H,
      (qLeafProfileKernelTotalCvConstLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H).comp
          (LinearMap.ker
            (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd)).subtype
        =
      0
  finrank_read_kernel :
    Module.finrank F
        (LinearMap.ker
          (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd))
      =
    n * (n ^ c - (n - 1)) * oddBReadProfileRankNat n a d

private theorem oddBReadAffineFiberCertificate_of_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n) :
    OddBReadAffineFiberCertificate n a b c d hd where
  exact_preimage_with_zero_phase H :=
    exists_oddBRead_exact_preimage_with_zero_phase hb hc hd hn H
  phase_kills_read_kernel H :=
    oddBRead_phase_kills_read_kernel hb hd hn H
  finrank_read_kernel :=
    finrank_ker_leafBReadTailReadMap_odd hb hc hd hn

noncomputable local instance instFintypeOddBReadKernel
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype
      (LinearMap.ker
        (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd)) := by
  classical
  exact Fintype.ofFinite _

set_option synthInstance.maxHeartbeats 200000 in
private theorem intCast_card_oddBReadKernel_eq_pow_of_certificate
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (cert : OddBReadAffineFiberCertificate n a b c d hd) :
    (Fintype.card
      (LinearMap.ker
        (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd)) : ℤ)
      =
    (2 : ℤ) ^
      (n * (n ^ c - (n - 1)) * oddBReadProfileRankNat n a d) := by
  rw [← Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  rw [cert.finrank_read_kernel]
  simp [F]

private theorem leafBReadFiberSignValue_eq_card_mul_visibleSign_of_certificate
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (cert : OddBReadAffineFiberCertificate n a b c d hd)
    (H : LeafVisibleKernel n b c d) :
    leafBReadFiberSignValue
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
    (Fintype.card
      (LinearMap.ker
        (qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd)) : ℤ)
      *
    leafVisibleCanonicalBaseSign
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  obtain ⟨XB0, hcondition, hphase⟩ :=
    cert.exact_preimage_with_zero_phase H
  exact
    leafBReadFiberSignValue_eq_card_mul_visibleSign_of_exact_preimage
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hd H XB0 hcondition (cert.phase_kills_read_kernel H) hphase

/-- Logical level 6: the odd compatible residual is the exact B-read
affine-fiber factor times the independently evaluated visible signed sum. -/
theorem leafCompatibleResidualSum_eq_tail_mul_visible_sum_of_odd
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    leafCompatibleResidualSum n a b c d =
      (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n) *
        ∑ H : LeafVisibleKernel n b c d,
          leafVisibleCanonicalBaseSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  let cert : OddBReadAffineFiberCertificate n a b c d hd :=
    oddBReadAffineFiberCertificate_of_odd hb hc hd hn
  rw [leafCompatibleResidualSum_eq_after_XB_BCoeffRead_fiberSignValue
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
  simp_rw [
    leafBReadFiberSignValue_eq_card_mul_visibleSign_of_certificate hd cert]
  rw [intCast_card_oddBReadKernel_eq_pow_of_certificate hd cert]
  calc
    (∑ H : LeafVisibleKernel n b c d,
      (2 : ℤ) ^ kCdCvElimExpNat n a b d *
        ((2 : ℤ) ^
            (n * (n ^ c - (n - 1)) * oddBReadProfileRankNat n a d)
          *
         leafVisibleCanonicalBaseSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H))
        =
      ∑ H : LeafVisibleKernel n b c d,
        (2 : ℤ) ^
          (kCdCvElimExpNat n a b d
            + n * (n ^ c - (n - 1)) * oddBReadProfileRankNat n a d)
          *
        leafVisibleCanonicalBaseSign
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
            refine Finset.sum_congr rfl ?_
            intro H _
            rw [pow_add]
            ring
    _ =
      ∑ H : LeafVisibleKernel n b c d,
        (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n) *
        leafVisibleCanonicalBaseSign
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
            rw [kCdCv_add_oddKernelExp_eq_BReadTailMain
              (n := n) (a := a) (b := b) (c := c) (d := d)
              ha hb hc hd]
    _ =
      (2 : ℤ) ^ Int.toNat (BReadTailMainZ a b c d n) *
        ∑ H : LeafVisibleKernel n b c d,
          leafVisibleCanonicalBaseSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
              rw [Finset.mul_sum]

private theorem BReadTailMainZ_nonneg_odd_route
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    0 ≤ BReadTailMainZ a b c d n := by
  unfold BReadTailMainZ
  rw [← intCast_oddBReadProfileRankNat
    (n := n) (a := a) (d := d) ha hd]
  rw [← intCast_oddBReadTailUnitNat
    (n := n) (b := b) (c := c) hb]
  positivity

private theorem visibleOddExponentProduct_nonneg
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) (hn : Odd n) :
    0 ≤ PassiveVisibleDimZ d n * LeafVisibleUnitZ a b c d n := by
  have hnotEven : ¬ Even n := by
    intro he
    rcases hn with ⟨k, hk⟩
    rcases he with ⟨l, hl⟩
    omega
  have hgeneric : ¬ (Even n ∧ 2 ≤ b ∧ 2 ≤ c) := by
    intro h
    exact hnotEven h.1
  have hpassive : 0 ≤ PassiveVisibleDimZ d n := by
    unfold PassiveVisibleDimZ
    exact nPowZ_sub_mZ_nonneg (n := n) hd
  have hvisible : 0 ≤ LeafVisibleUnitZ a b c d n := by
    rw [LeafVisibleUnitZ_eq_genericScalarVisibleExpZ
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hd hgeneric]
    have hb0 : 0 ≤ nPowZ n b := nPowZ_nonneg n b
    have hc0 : 0 ≤ nPowZ n c := nPowZ_nonneg n c
    have hm0 : 0 ≤ (mZ n) ^ 2 := sq_nonneg (mZ n)
    nlinarith
  exact mul_nonneg hpassive hvisible

/-- Logical level 6: closed signed-sum evaluation of the compatible residual
for odd replica count and arbitrary positive block sizes. -/
theorem leafCompatibleResidualSum_eq_pow_compatible_of_odd
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    leafCompatibleResidualSum n a b c d =
      (2 : ℤ) ^ Int.toNat (CompatibleResidualSplitZ a b c d n) := by
  rw [leafCompatibleResidualSum_eq_tail_mul_visible_sum_of_odd
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hb hc hd hn]
  rw [triangleLeaf_visible_sum_closed_odd
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hb hc hd hn]
  rw [← pow_add]
  congr 1
  have htoNat :=
    Int_toNat_add_of_nonneg
      (BReadTailMainZ_nonneg_odd_route
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hd)
      (visibleOddExponentProduct_nonneg
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hd hn)
  rw [← htoNat]
  exact congrArg Int.toNat
    (BReadTailMainZ_add_visible_eq_CompatibleResidualSplitZ
      (a := a) (b := b) (c := c) (d := d) (n := n))

private theorem CompatibleResidualSplitZ_nonneg_odd_route
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hn : Odd n) :
    0 ≤ CompatibleResidualSplitZ a b c d n := by
  rw [← BReadTailMainZ_add_visible_eq_CompatibleResidualSplitZ
    (a := a) (b := b) (c := c) (d := d) (n := n)]
  exact add_nonneg
    (BReadTailMainZ_nonneg_odd_route
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hd)
    (visibleOddExponentProduct_nonneg
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hd hn)

/-- Logical level 7: raw Triangle-plus-leaf `DeltaNF = 2^X` for odd replica
count and arbitrary positive block sizes. -/
theorem DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_of_odd
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    DeltaNF .triangleLeaf a b c d n =
      (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c d n) := by
  have hnotEven : ¬ Even n := by
    intro he
    rcases hn with ⟨k, hk⟩
    rcases he with ⟨l, hl⟩
    omega
  have hnotExceptional : ¬ TriangleLeafExceptional n a b c d := by
    intro h
    exact hnotEven h.1
  have hresNonneg :
      0 ≤ CompatibleResidualSplitZ a b c d n :=
    CompatibleResidualSplitZ_nonneg_odd_route
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hd hn
  let totalExp : ℕ :=
    n ^ (b + c + d)
      + Module.finrank F
          (LinearMap.ker
            (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
      + Int.toNat (CompatibleResidualSplitZ a b c d n)
  have htotalCast :
      (totalExp : ℤ) = X1CorrectedZ a b c d n := by
    unfold totalExp
    rw [Nat.cast_add, Nat.cast_add]
    rw [Int.toNat_of_nonneg hresNonneg]
    rw [intCast_finrank_ker_KWMap_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
    change
      nPowZ n (b + c + d)
          + TriangleLeafAfterWKernelExpZ a b c d n
          + CompatibleResidualSplitZ a b c d n
        =
      X1CorrectedZ a b c d n
    rw [CompatibleResidualSplitZ_eq_CompatibleResidualExpZ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
    rw [← X1Z_eq_afterW_plus_compatible
      (n := n) (a := a) (b := b) (c := c) (d := d)]
    unfold X1CorrectedZ
    rw [X1PaperOldZ_eq_current_X1Z]
    rw [correctionZ_nonexceptional hnotExceptional, sub_zero]
  have htotalNat :
      totalExp = Int.toNat (X1CorrectedZ a b c d n) := by
    have h := congrArg Int.toNat htotalCast
    simpa using h
  calc
    DeltaNF .triangleLeaf a b c d n
        =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ((2 : ℤ) ^ Module.finrank F
          (LinearMap.ker
            (KWMap (n := n) (a := a) (b := b) (c := c) (d := d))) *
          leafCompatibleResidualSum n a b c d) :=
            DeltaNF_triangleLeaf_after_WDiff
              (n := n) (a := a) (b := b) (c := c) (d := d)
    _ =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ((2 : ℤ) ^ Module.finrank F
          (LinearMap.ker
            (KWMap (n := n) (a := a) (b := b) (c := c) (d := d))) *
          (2 : ℤ) ^
            Int.toNat (CompatibleResidualSplitZ a b c d n)) := by
              rw [leafCompatibleResidualSum_eq_pow_compatible_of_odd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                ha hb hc hd hn]
    _ = (2 : ℤ) ^ totalExp := by
      unfold totalExp
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ = (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c d n) := by
      rw [htotalNat]

end

end TriangleLeaf
end Core4loop
