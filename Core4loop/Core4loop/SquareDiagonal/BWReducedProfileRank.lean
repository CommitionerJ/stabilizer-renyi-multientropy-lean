import Core4loop.SquareDiagonal.BWReducedProfile
import Core4loop.SquareDiagonal.BWQuadraticRank
import Core4loop.TriangleCore.Parity

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

theorem sqdiagThetaZ_ge_base
    {r s t n : ℕ} [NeZero n] :
    mZ n * (2 * (n : ℤ) - 1) ≤ ThetaZ r s t n := by
  unfold ThetaZ
  by_cases h : Even n ∧ 2 ≤ r ∧ 2 ≤ s ∧ 2 ≤ t
  · rw [if_pos h]
    have hn2 : 2 ≤ n := by
      have hnpos : 0 < n := NeZero.pos n
      rcases h.1 with ⟨k, hk⟩
      cases k with
      | zero =>
          omega
      | succ k =>
          cases k with
          | zero =>
              omega
          | succ k =>
              omega
    unfold mZ
    have hn2z : (2 : ℤ) ≤ n := by
      exact_mod_cast hn2
    have hnm1 : 0 ≤ (n : ℤ) - 1 := by omega
    have hnm2 : 0 ≤ (n : ℤ) - 2 := by omega
    have hprod : 0 ≤ ((n : ℤ) - 1) * ((n : ℤ) - 2) :=
      mul_nonneg hnm1 hnm2
    nlinarith
  · rw [if_neg h]

theorem sqdiagSectorExpZ_nonneg_of_positive
    {r s t passive n : ℕ} [NeZero n]
    (hp : 0 < passive) :
    0 ≤ SectorExpZ r s t passive n := by
  unfold SectorExpZ
  exact mul_nonneg (ThetaZ_nonneg (r := r) (s := s) (t := t) (n := n))
    (passiveTransfer_nonneg (n := n) hp)

theorem sqdiagSectorExpZ_ge_base_of_positive
    {r s t passive n : ℕ} [NeZero n]
    (hp : 0 < passive) :
    mZ n * (2 * (n : ℤ) - 1) * (nPowZ n passive - mZ n) ≤
      SectorExpZ r s t passive n := by
  unfold SectorExpZ
  exact
    mul_le_mul_of_nonneg_right
      (sqdiagThetaZ_ge_base (r := r) (s := s) (t := t) (n := n))
      (passiveTransfer_nonneg (n := n) hp)

theorem sqdiag_mZ_add_one_eq_natCast
    {n : ℕ} [NeZero n] :
    mZ n + 1 = (n : ℤ) := by
  unfold mZ
  omega

theorem sqdiag_natCast_le_nPowZ_of_positive
    {n k : ℕ} (hk : 0 < k) :
    (n : ℤ) ≤ nPowZ n k := by
  unfold nPowZ
  exact_mod_cast (Nat.le_pow hk : n ≤ n ^ k)

theorem sqdiag_X3AfterAZ_base_lower_bound_algebra
    {M N A B C D : ℤ}
    (hN : N = M + 1)
    (hM : 0 ≤ M)
    (hA : N ≤ A) (hB : N ≤ B) (hC : N ≤ C) (hD : N ≤ D) :
    0 ≤
      A * C * D + A * B * D + A * B * C -
        M * (C * D + A * D + A * B + B * C + B * D) +
        M ^ 2 * (A + C) +
        M * (2 * N - 1) * (D - M) +
        M * (2 * N - 1) * (B - M) +
        M ^ 3 := by
  let dA : ℤ := A - N
  let dB : ℤ := B - N
  let dC : ℤ := C - N
  let dD : ℤ := D - N
  have hdA : 0 ≤ dA := by dsimp [dA]; omega
  have hdB : 0 ≤ dB := by dsimp [dB]; omega
  have hdC : 0 ≤ dC := by dsimp [dC]; omega
  have hdD : 0 ≤ dD := by dsimp [dD]; omega
  have hdecomp :
      A * C * D + A * B * D + A * B * C -
          M * (C * D + A * D + A * B + B * C + B * D) +
          M ^ 2 * (A + C) +
          M * (2 * N - 1) * (D - M) +
          M * (2 * N - 1) * (B - M) +
          M ^ 3 =
        3 + 2 * dD + 2 * dC + 2 * dB + 3 * dA + 6 * M +
          dC * dD + dB * dD + dB * dC +
          2 * dA * dD + 2 * dA * dC + 2 * dA * dB +
          2 * M * dD + 2 * M * dC + 2 * M * dB + 4 * M * dA +
          5 * M ^ 2 +
          dA * dC * dD + dA * dB * dD + dA * dB * dC +
          M * dA * dD + 2 * M * dA * dC + M * dA * dB +
          M ^ 2 * dD + M ^ 2 * dC + M ^ 2 * dB +
          2 * M ^ 2 * dA + M ^ 3 := by
    dsimp [dA, dB, dC, dD]
    rw [hN]
    ring_nf
  rw [hdecomp]
  positivity

theorem sqdiag_X3AfterAZ_base_lower_bound_nonneg
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    0 ≤
      nPowZ n (a + c + d) +
        nPowZ n (a + b + d) +
        nPowZ n (a + b + c) -
        mZ n * Sigma2_3Z a b c d n +
        (mZ n) ^ 2 * (nPowZ n a + nPowZ n c) +
        mZ n * (2 * (n : ℤ) - 1) * (nPowZ n d - mZ n) +
        mZ n * (2 * (n : ℤ) - 1) * (nPowZ n b - mZ n) +
        OverlapG3Z n := by
  have hbase :=
    sqdiag_X3AfterAZ_base_lower_bound_algebra
      (M := mZ n) (N := (n : ℤ))
      (A := nPowZ n a) (B := nPowZ n b)
      (C := nPowZ n c) (D := nPowZ n d)
      (hN := (sqdiag_mZ_add_one_eq_natCast (n := n)).symm)
      (hM := mZ_nonneg (n := n))
      (hA := sqdiag_natCast_le_nPowZ_of_positive (n := n) ha)
      (hB := sqdiag_natCast_le_nPowZ_of_positive (n := n) hb)
      (hC := sqdiag_natCast_le_nPowZ_of_positive (n := n) hc)
      (hD := sqdiag_natCast_le_nPowZ_of_positive (n := n) hd)
  simpa [Sigma2_3Z, OverlapG3Z, nPowZ_add, mul_assoc, mul_left_comm, mul_comm]
    using hbase

theorem sqdiag_X3AfterAZ_sector_formula
    (a b c d n : ℕ) :
    X3AfterAZ a b c d n =
      nPowZ n (a + c + d) +
        nPowZ n (a + b + d) +
        nPowZ n (a + b + c) -
        mZ n * Sigma2_3Z a b c d n +
        (mZ n) ^ 2 * (nPowZ n a + nPowZ n c) +
        SectorExpZ a b c d n +
        SectorExpZ a c d b n +
        OverlapG3Z n := by
  rw [X3AfterAZ, X3Z_sector_formula]
  unfold Sigma1Z
  ring

theorem sqdiag_X3AfterAZ_sector_tail_nonneg
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    0 ≤ SectorExpZ a b c d n +
        SectorExpZ a c d b n +
        OverlapG3Z n := by
  exact
    add_nonneg
      (add_nonneg
        (sqdiagSectorExpZ_nonneg_of_positive
          (r := a) (s := b) (t := c) (passive := d) (n := n) hd)
        (sqdiagSectorExpZ_nonneg_of_positive
          (r := a) (s := c) (t := d) (passive := b) (n := n) hb))
      (OverlapG3Z_nonneg (n := n))

theorem X3AfterAZ_nonneg_of_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    0 ≤ X3AfterAZ a b c d n := by
  rw [sqdiag_X3AfterAZ_sector_formula]
  have hbase :=
    sqdiag_X3AfterAZ_base_lower_bound_nonneg
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd
  have h123 :=
    sqdiagSectorExpZ_ge_base_of_positive
      (r := a) (s := b) (t := c) (passive := d) (n := n) hd
  have h134 :=
    sqdiagSectorExpZ_ge_base_of_positive
      (r := a) (s := c) (t := d) (passive := b) (n := n) hb
  nlinarith

set_option synthInstance.maxHeartbeats 200000 in
-- The reduced vertical-orthogonal target contains nested kernel submodule instances.
def sqdiagReducedRelationVerticalOrthogonalFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
      Module.finrank F (SquareCombinedKernel n a b c d) +
      Module.finrank F
        (LinearMap.ker
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
    Int.toNat (X3AfterAZ a b c d n)

set_option synthInstance.maxHeartbeats 200000 in
-- Equivalent rank target before adding the reduced root-defect quotient.
def sqdiagReducedRelationVerticalProfileFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F (sqdiagReducedRelationVertical n a b c d) +
      Module.finrank F (SquareCombinedKernel n a b c d) +
      Module.finrank F
        (LinearMap.ker
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
      ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) =
    Int.toNat (X3AfterAZ a b c d n) +
      (n * (n - 1) ^ 2 + (n - 1) ^ 3)

set_option synthInstance.maxHeartbeats 200000 in
-- The pair-presentation target contains the same nested orthogonal submodule instances.
def sqdiagPairPresentationVerticalOrthogonalFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
      Module.finrank F (SquareCombinedKernel n a b c d) +
      Module.finrank F
        (LinearMap.ker
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
      2 * (n - 1) ^ 3 =
    Int.toNat (X3AfterAZ a b c d n) +
      ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))

set_option synthInstance.maxHeartbeats 200000 in
-- A subtraction-free pair rank target that keeps the intersection dimension explicit.
def sqdiagPairPresentationVerticalOrthogonalBalancedFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
      Module.finrank F (SquareCombinedKernel n a b c d) +
      Module.finrank F
        (LinearMap.ker
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
    Int.toNat (X3AfterAZ a b c d n) +
      Module.finrank F (SquareBWIntersection n a b c d)

set_option synthInstance.maxHeartbeats 200000 in
-- The graph-lagrangian target is the clean rank form before reducing to the presentation model.
def sqdiagBWAAdjointGraphLagrangianFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
      n ^ (a + b + d) =
    Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)

set_option synthInstance.maxHeartbeats 200000 in
-- The same target after rank-nullity for the polar map from the graph to the root-zero dual.
def sqdiagBWAAdjointGraphPolarImageFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F (SqdiagBWZAdjointImage n a b c d) +
      Module.finrank F (SquareCombinedKernel n a b c d) +
      Module.finrank F
        (LinearMap.ker
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      n ^ (a + b + d) =
    Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d) +
      Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphPolarToRootZero
            (n := n) (a := a) (b := b) (c := c) (d := d)))

set_option synthInstance.maxHeartbeats 200000 in
-- The adjoint-support form replaces the image/intersection plus kernel by the raw support submodule.
def sqdiagBWZAdjointSupportPolarImageFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F
      (sqdiagBWZAdjointSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d)) +
      Module.finrank F
        (LinearMap.ker
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      n ^ (a + b + d) =
    Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d) +
      Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphPolarToRootZero
            (n := n) (a := a) (b := b) (c := c) (d := d)))

set_option synthInstance.maxHeartbeats 200000 in
-- The polar-image rank target after replacing the polar image by the root-zero A-coeff dual image.
def sqdiagBWZAdjointSupportRootZeroACoeffDualFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F
      (sqdiagBWZAdjointSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d)) +
      Module.finrank F
        (LinearMap.ker
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      n ^ (a + b + d) =
    Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d) +
      Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))

set_option synthInstance.maxHeartbeats 200000 in
-- The same target after eliminating the KC-adjoint kernel by rank-nullity.
def sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F
      (sqdiagBWZAdjointSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d)) +
      n ^ (a + b + d) =
    Int.toNat (X3AfterAZ a b c d n) +
      Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      (n - 1) * n ^ (b + d)

set_option synthInstance.maxHeartbeats 200000 in
-- Equivalent NoKC target after factoring the A-dual map through the graph root image.
def sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F
      (sqdiagBWZAdjointSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d)) +
      n ^ (a + b + d) =
    Int.toNat (X3AfterAZ a b c d n) +
      Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootImageEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      (n - 1) * n ^ (b + d)

set_option synthInstance.maxHeartbeats 200000 in
-- Equivalent NoKC target after rank-nullity on the root-image evaluation map.
def sqdiagBWZAdjointSupportRootImageAnnihilatorNoKCFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F
      (sqdiagBWZAdjointSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d)) +
      n ^ (a + b + d) +
      Module.finrank F
        (sqdiagBWAAdjointGraphRootImageAnnihilator n a b c d) =
    Int.toNat (X3AfterAZ a b c d n) +
      Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      (n - 1) * n ^ (b + d)

set_option synthInstance.maxHeartbeats 200000 in
-- Equivalent target after eliminating support, root image, and the KC-adjoint
-- kernel by rank-nullity.
def sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F (sqdiagBWAAdjointGraphRootZero n a b c d) +
      Module.finrank F
        (sqdiagBWAAdjointGraphRootImageAnnihilator n a b c d) +
      n ^ (a + b + d) =
    Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)

set_option synthInstance.maxHeartbeats 200000 in
-- The quotient rank gap isolated as the root-image annihilator dimension.
def sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F
      (sqdiagBWAAdjointGraphRootImageAnnihilator n a b c d) +
      n * (n - 1) ^ 2 + (n - 1) ^ 3 =
    (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b

set_option synthInstance.maxHeartbeats 200000 in
-- The root-zero graph form of the pre-quotient profile rank target.
def sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F (sqdiagBWAAdjointGraphRootZero n a b c d) +
      n ^ (a + b + d) +
      ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) =
    Int.toNat (X3AfterAZ a b c d n) +
      (n * (n - 1) ^ 2 + (n - 1) ^ 3) +
      n ^ (b + c + d)

set_option synthInstance.maxHeartbeats 500000 in
-- Once the annihilator profile-core rank is known, the root-zero profile
-- target is exactly the root-zero/root-image-annihilator target.
theorem sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rootImageAnnihilatorProfileCore
    {n a b c d : ℕ} [NeZero n]
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d) :
    sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d := by
  unfold sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget at hann
  unfold sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget
  unfold sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- The named reduced rank target is equivalent to the graph-lagrangian rank target.
theorem sqdiagReducedRelationVerticalOrthogonalFinrankTarget_iff_lagrangian
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) :
    sqdiagReducedRelationVerticalOrthogonalFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d := by
  unfold sqdiagReducedRelationVerticalOrthogonalFinrankTarget
  unfold sqdiagBWAAdjointGraphLagrangianFinrankTarget
  exact
    (finrank_lagrangian_add_CFun4_iff_reducedRelationVerticalOrthogonal_add_squareKernel_KC
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc).symm

set_option synthInstance.maxHeartbeats 500000 in
-- A graph-lagrangian rank certificate supplies the named reduced rank target.
theorem sqdiagReducedRelationVerticalOrthogonalFinrankTarget_of_lagrangian_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hlag : sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d) :
    sqdiagReducedRelationVerticalOrthogonalFinrankTarget n a b c d :=
  (sqdiagReducedRelationVerticalOrthogonalFinrankTarget_iff_lagrangian
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hc).mpr hlag

set_option maxHeartbeats 800000 in
-- The nested polar-map rank-nullity and final arithmetic both need extra reduction budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Rank-nullity for the polar map rewrites the lagrangian target as a polar-image target.
theorem sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_polarImage
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphPolarImageFinrankTarget n a b c d := by
  unfold sqdiagBWAAdjointGraphLagrangianFinrankTarget
  unfold sqdiagBWAAdjointGraphPolarImageFinrankTarget
  have hpolar :
      Module.finrank F
          (LinearMap.range
            (sqdiagBWAAdjointGraphPolarToRootZero
              (n := n) (a := a) (b := b) (c := c) (d := d))) +
        Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) =
      Module.finrank F (SqdiagBWAAdjointGraph n a b c d) := by
    let f :=
      sqdiagBWAAdjointGraphPolarToRootZero
        (n := n) (a := a) (b := b) (c := c) (d := d)
    change
      Module.finrank F (LinearMap.range f) +
          Module.finrank F (LinearMap.ker f) =
        Module.finrank F (SqdiagBWAAdjointGraph n a b c d)
    exact LinearMap.finrank_range_add_finrank_ker f
  have hgraph :=
    finrank_sqdiagBWAAdjointGraph_eq_adjointImage_add_kernels
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- The polar-image target can be checked on the adjoint support submodule instead.
theorem sqdiagBWAAdjointGraphPolarImageFinrankTarget_iff_adjointSupport
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphPolarImageFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportPolarImageFinrankTarget n a b c d := by
  unfold sqdiagBWAAdjointGraphPolarImageFinrankTarget
  unfold sqdiagBWZAdjointSupportPolarImageFinrankTarget
  have hadj :=
    finrank_sqdiagBWZAdjointImage_add_SquareCombinedKernel_eq_adjointSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- Replace the polar-image rank by the equivalent root-zero A-coeff dual image rank.
theorem sqdiagBWZAdjointSupportPolarImageFinrankTarget_iff_rootZeroACoeffDual
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZAdjointSupportPolarImageFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportRootZeroACoeffDualFinrankTarget n a b c d := by
  unfold sqdiagBWZAdjointSupportPolarImageFinrankTarget
  unfold sqdiagBWZAdjointSupportRootZeroACoeffDualFinrankTarget
  have hpolar :=
    finrank_sqdiagBWAAdjointGraphPolarRange_eq_rootZeroACoeffDualRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- Eliminate the KC-adjoint kernel term from the root-zero A-coeff dual rank target.
theorem sqdiagBWZAdjointSupportRootZeroACoeffDualFinrankTarget_iff_noKC
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    sqdiagBWZAdjointSupportRootZeroACoeffDualFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget n a b c d := by
  unfold sqdiagBWZAdjointSupportRootZeroACoeffDualFinrankTarget
  unfold sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget
  have hKC :=
    finrank_ker_sqdiagKCAdjointMap_add_rank
      (n := n) (a := a) (b := b) (c := c) (d := d) hc
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- Combined bridge from the lagrangian target to the raw adjoint-support/polar-image target.
theorem sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportPolarImage
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportPolarImageFinrankTarget n a b c d := by
  rw [sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_polarImage,
    sqdiagBWAAdjointGraphPolarImageFinrankTarget_iff_adjointSupport]

set_option synthInstance.maxHeartbeats 500000 in
-- Combined bridge to the root-zero A-coeff dual image rank target.
theorem sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootZeroACoeffDual
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportRootZeroACoeffDualFinrankTarget n a b c d := by
  rw [sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportPolarImage,
    sqdiagBWZAdjointSupportPolarImageFinrankTarget_iff_rootZeroACoeffDual]

set_option maxHeartbeats 800000 in
-- Direct bridge: dual rank-nullity plus graph-to-support exactness, avoiding the polar-image route.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootZeroACoeffDualNoKC_direct
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget n a b c d := by
  unfold sqdiagBWAAdjointGraphLagrangianFinrankTarget
  unfold sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget
  have hdual :=
    finrank_sqdiagBWAAdjointGraphRootZeroACoeffDualRange_add_lagrangian_eq_graph
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hgraph :=
    finrank_sqdiagBWAAdjointGraph_eq_adjointSupport_add_KCAdjointKer
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hKC :=
    finrank_ker_sqdiagKCAdjointMap_add_rank
      (n := n) (a := a) (b := b) (c := c) (d := d) hc
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- Replace the root-zero A-dual image by the equivalent root-image evaluation image.
theorem sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget_iff_rootImageEvalNoKC
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget n a b c d := by
  unfold sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget
  unfold sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget
  have hrootImage :=
    finrank_sqdiagBWAAdjointGraphRootImageEvalRange_eq_rootZeroACoeffDualRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- Rank-nullity on the root-image evaluation map replaces its image by
-- root image minus the explicit annihilator.
theorem sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget_iff_rootImageAnnihilatorNoKC
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportRootImageAnnihilatorNoKCFinrankTarget n a b c d := by
  unfold sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget
  unfold sqdiagBWZAdjointSupportRootImageAnnihilatorNoKCFinrankTarget
  have hrootImage :=
    finrank_sqdiagBWAAdjointGraphRootImageEvalRange_add_annihilator_eq_rootImage
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- Root-map rank-nullity removes the remaining support/root-image/KC-adjoint
-- terms from the annihilator target.
theorem sqdiagBWZAdjointSupportRootImageAnnihilatorNoKCFinrankTarget_iff_rootZeroAnnihilator
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    sqdiagBWZAdjointSupportRootImageAnnihilatorNoKCFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d := by
  unfold sqdiagBWZAdjointSupportRootImageAnnihilatorNoKCFinrankTarget
  unfold sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget
  have hroot :=
    finrank_sqdiagBWAAdjointGraphRootImage_add_rootZero_eq_graph
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hgraph :=
    finrank_sqdiagBWAAdjointGraph_eq_adjointSupport_add_KCAdjointKer
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hKC :=
    finrank_ker_sqdiagKCAdjointMap_add_rank
      (n := n) (a := a) (b := b) (c := c) (d := d) hc
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- Combined bridge to the KC-eliminated adjoint-support/root-zero A-dual rank target.
theorem sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootZeroACoeffDualNoKC
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget n a b c d := by
  exact
    sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootZeroACoeffDualNoKC_direct
      (n := n) (a := a) (b := b) (c := c) (d := d) hc

set_option synthInstance.maxHeartbeats 500000 in
-- Combined bridge to the root-image evaluation NoKC rank target.
theorem sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootImageEvalNoKC
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget n a b c d := by
  rw [sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootZeroACoeffDualNoKC
      (n := n) (a := a) (b := b) (c := c) (d := d) hc,
    sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget_iff_rootImageEvalNoKC
      (n := n) (a := a) (b := b) (c := c) (d := d)]

set_option synthInstance.maxHeartbeats 500000 in
-- Combined bridge to the root-image annihilator NoKC rank target.
theorem sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootImageAnnihilatorNoKC
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d ↔
      sqdiagBWZAdjointSupportRootImageAnnihilatorNoKCFinrankTarget n a b c d := by
  rw [sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootImageEvalNoKC
      (n := n) (a := a) (b := b) (c := c) (d := d) hc,
    sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget_iff_rootImageAnnihilatorNoKC
      (n := n) (a := a) (b := b) (c := c) (d := d)]

set_option synthInstance.maxHeartbeats 500000 in
-- Direct bridge to the graph root-zero/root-image-annihilator rank target.
theorem sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_rootZeroAnnihilator_direct
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d := by
  unfold sqdiagBWAAdjointGraphLagrangianFinrankTarget
  unfold sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget
  have hdim :=
    finrank_sqdiagBWAAdjointGraphLagrangian_eq_rootZero_add_rootImageAnnihilator
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- Backward-compatible bridge retaining the older `c > 0` signature.
theorem sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_rootZeroAnnihilator
    {n a b c d : ℕ} [NeZero n]
    (_hc : 0 < c) :
    sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
  sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_rootZeroAnnihilator_direct
    (n := n) (a := a) (b := b) (c := c) (d := d)

set_option maxHeartbeats 800000 in
-- The restricted root-zero graph map has the same kernel as the graph-to-reduced map.
set_option synthInstance.maxHeartbeats 300000 in
noncomputable def
    sqdiagBWAAdjointGraphRootZeroToReducedVerticalKerEquivGraphToReducedKer
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWAAdjointGraphRootZeroToReducedVertical
          (n := n) (a := a) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    LinearMap.ker
        (sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d)) where
  toFun x := by
    refine ⟨x.1.1, ?_⟩
    exact congrArg Subtype.val (LinearMap.mem_ker.mp x.2)
  invFun x := by
    have hsum :
        sqdiagBWAAdjointGraphToReducedRelation
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 =
          0 :=
      LinearMap.mem_ker.mp x.2
    have hxroot :
        x.1 ∈ sqdiagBWAAdjointGraphRootZero n a b c d := by
      rw [LinearMap.mem_ker]
      change
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1.1 = 0
      have hroot :=
        congrArg
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))
          hsum
      exact congrArg Subtype.val hroot
    let x0 : sqdiagBWAAdjointGraphRootZero n a b c d := ⟨x.1, hxroot⟩
    refine ⟨x0, ?_⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact hsum
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

set_option maxHeartbeats 800000 in
-- Rank-nullity for the root-zero graph over the reduced vertical model.
set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagBWAAdjointGraphRootZero_eq_reducedRelationVertical_add_kernels
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (sqdiagBWAAdjointGraphRootZero n a b c d) =
      Module.finrank F (sqdiagReducedRelationVertical n a b c d) +
        Module.finrank F (SquareCombinedKernel n a b c d) +
        Module.finrank F
          (LinearMap.ker
            (sqdiagKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  let f :
      sqdiagBWAAdjointGraphRootZero n a b c d →ₗ[F]
        LinearMap.ker
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) :=
    sqdiagBWAAdjointGraphRootZeroToReducedVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hrange :
      Module.finrank F (LinearMap.range f) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d) := by
    have htop : LinearMap.range f = ⊤ :=
      LinearMap.range_eq_top.mpr
        (sqdiagBWAAdjointGraphRootZeroToReducedVertical_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d))
    rw [htop, finrank_top]
  have hker :
      Module.finrank F (LinearMap.ker f) =
        Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (sqdiagKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d))) := by
    calc
      Module.finrank F (LinearMap.ker f) =
          Module.finrank F
            (LinearMap.ker
              (sqdiagBWAAdjointGraphToReducedRelation
                (n := n) (a := a) (b := b) (c := c) (d := d))) := by
            exact LinearEquiv.finrank_eq
              (sqdiagBWAAdjointGraphRootZeroToReducedVerticalKerEquivGraphToReducedKer
                (n := n) (a := a) (b := b) (c := c) (d := d))
      _ =
          Module.finrank F
            (LinearMap.ker
              (sqdiagBWAAdjointGraphToAdjointImage
                (n := n) (a := a) (b := b) (c := c) (d := d))) := by
            exact LinearEquiv.finrank_eq
              (sqdiagBWAAdjointGraphToReducedRelationKerEquivAdjointImageKer
                (n := n) (a := a) (b := b) (c := c) (d := d))
      _ =
          Module.finrank F
              (SquareCombinedKernel n a b c d ×
                LinearMap.ker
                  (sqdiagKCAdjointMap
                    (n := n) (a := a) (b := b) (c := c) (d := d))) := by
            exact LinearEquiv.finrank_eq
              (sqdiagBWAAdjointGraphToAdjointImageKerEquiv
                (n := n) (a := a) (b := b) (c := c) (d := d))
      _ =
          Module.finrank F (SquareCombinedKernel n a b c d) +
            Module.finrank F
              (LinearMap.ker
                (sqdiagKCAdjointMap
                  (n := n) (a := a) (b := b) (c := c) (d := d))) := by
            rw [Module.finrank_prod]
  rw [hrange, hker] at h
  omega

set_option synthInstance.maxHeartbeats 500000 in
-- Comparing the lagrangian and root-zero graph decompositions isolates the
-- reduced vertical-orthogonal/vertical gap without using the false root/polar route.
theorem finrank_sqdiagBWAAdjointGraphLagrangian_add_reducedVertical_eq_rootZero_add_reducedVerticalOrthogonal
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
        Module.finrank F (sqdiagReducedRelationVertical n a b c d) =
      Module.finrank F (sqdiagBWAAdjointGraphRootZero n a b c d) +
        Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) := by
  have hlag :=
    finrank_sqdiagBWAAdjointGraphLagrangian_eq_reducedRelationVerticalOrthogonal_add_kernels
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hroot :=
    finrank_sqdiagBWAAdjointGraphRootZero_eq_reducedRelationVertical_add_kernels
      (n := n) (a := a) (b := b) (c := c) (d := d)
  omega

set_option synthInstance.maxHeartbeats 500000 in
-- The reduced vertical-orthogonal/vertical quotient has the same dimension as
-- the graph root-image annihilator.
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_eq_vertical_add_rootImageAnnihilator
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
      Module.finrank F (sqdiagReducedRelationVertical n a b c d) +
        Module.finrank F
          (sqdiagBWAAdjointGraphRootImageAnnihilator n a b c d) := by
  have hcompare :=
    finrank_sqdiagBWAAdjointGraphLagrangian_add_reducedVertical_eq_rootZero_add_reducedVerticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hsplit :=
    finrank_sqdiagBWAAdjointGraphLagrangian_eq_rootZero_add_rootImageAnnihilator
      (n := n) (a := a) (b := b) (c := c) (d := d)
  omega

set_option synthInstance.maxHeartbeats 500000 in
-- The vertical-orthogonal rank gap is exactly the annihilator profile-core target.
theorem sqdiagReducedRelationVerticalOrthogonalRankGap_iff_rootImageAnnihilatorProfileCore
    {n a b c d : ℕ} [NeZero n] :
    (Module.finrank F
          (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          n * (n - 1) ^ 2 + (n - 1) ^ 3 =
        Module.finrank F
            (sqdiagReducedRelationVertical n a b c d) +
          ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ↔
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d := by
  unfold sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget
  have hann :=
    finrank_sqdiagReducedRelationVerticalOrthogonal_eq_vertical_add_rootImageAnnihilator
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- The pre-quotient vertical profile target is the root-zero graph target
-- after exchanging the KC and KC-adjoint kernel dimensions.
theorem sqdiagReducedRelationVerticalProfileFinrankTarget_iff_rootZeroProfile
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) :
    sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d := by
  unfold sqdiagReducedRelationVerticalProfileFinrankTarget
  unfold sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget
  have hroot :=
    finrank_sqdiagBWAAdjointGraphRootZero_eq_reducedRelationVertical_add_kernels
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hKC :=
    finrank_ker_KCMap_add_rootTarget_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- The root-zero target unfolds through the nested reduced/root-zero graph submodules.
theorem sqdiagReducedRelationVerticalProfileFinrankTarget_of_rootZeroProfile
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hroot :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d :=
  (sqdiagReducedRelationVerticalProfileFinrankTarget_iff_rootZeroProfile
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hc).mpr hroot

set_option synthInstance.maxHeartbeats 500000 in
-- The reverse direction uses the same nested graph/root-zero rank bridge.
theorem sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_of_verticalProfile
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hprofile :
      sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d) :
    sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d :=
  (sqdiagReducedRelationVerticalProfileFinrankTarget_iff_rootZeroProfile
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hc).mp hprofile

set_option synthInstance.maxHeartbeats 500000 in
-- Under the quotient rank gap, the orthogonal and pre-quotient profile
-- rank targets are equivalent.
theorem sqdiagReducedRelationVerticalProfileFinrankTarget_of_verticalOrthogonalFinrankTarget
    {n a b c d : ℕ} [NeZero n]
    (hrank :
      Module.finrank F
          (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          n * (n - 1) ^ 2 + (n - 1) ^ 3 =
        Module.finrank F
            (sqdiagReducedRelationVertical n a b c d) +
          ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b))
    (horth :
      sqdiagReducedRelationVerticalOrthogonalFinrankTarget n a b c d) :
    sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d := by
  unfold sqdiagReducedRelationVerticalOrthogonalFinrankTarget at horth
  unfold sqdiagReducedRelationVerticalProfileFinrankTarget
  omega

set_option synthInstance.maxHeartbeats 500000 in
-- Unfolding both named rank targets exposes nested finrank expressions.
theorem sqdiagPairPresentationVerticalOrthogonalFinrankTarget_iff_reducedRelation
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    sqdiagPairPresentationVerticalOrthogonalFinrankTarget n a b c d ↔
      sqdiagReducedRelationVerticalOrthogonalFinrankTarget n a b c d := by
  unfold sqdiagPairPresentationVerticalOrthogonalFinrankTarget
  unfold sqdiagReducedRelationVerticalOrthogonalFinrankTarget
  exact
    pairPresentationVerticalOrthogonal_add_squareKernel_KC_finrank_iff_reducedRelation
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd

set_option synthInstance.maxHeartbeats 500000 in
-- The balanced pair target is exactly the reduced target with the intersection term not eliminated.
theorem sqdiagPairPresentationVerticalOrthogonalBalancedFinrankTarget_iff_reducedRelation
    {n a b c d : ℕ} [NeZero n] :
    sqdiagPairPresentationVerticalOrthogonalBalancedFinrankTarget n a b c d ↔
      sqdiagReducedRelationVerticalOrthogonalFinrankTarget n a b c d := by
  unfold sqdiagPairPresentationVerticalOrthogonalBalancedFinrankTarget
  unfold sqdiagReducedRelationVerticalOrthogonalFinrankTarget
  have horth :=
    finrank_sqdiagAdjointPairPresentationVerticalOrthogonal_eq_reducedRelationVerticalOrthogonal_add_intersection
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- Eliminating the intersection dimension recovers the named pair target.
theorem sqdiagPairPresentationVerticalOrthogonalBalancedFinrankTarget_iff_pairTarget
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    sqdiagPairPresentationVerticalOrthogonalBalancedFinrankTarget n a b c d ↔
      sqdiagPairPresentationVerticalOrthogonalFinrankTarget n a b c d := by
  rw [sqdiagPairPresentationVerticalOrthogonalBalancedFinrankTarget_iff_reducedRelation,
    sqdiagPairPresentationVerticalOrthogonalFinrankTarget_iff_reducedRelation
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd]

set_option synthInstance.maxHeartbeats 500000 in
-- The pair-presentation rank target can be checked on the graph lagrangian.
theorem sqdiagPairPresentationVerticalOrthogonalFinrankTarget_iff_lagrangian
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    sqdiagPairPresentationVerticalOrthogonalFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d := by
  rw [sqdiagPairPresentationVerticalOrthogonalFinrankTarget_iff_reducedRelation
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd,
    sqdiagReducedRelationVerticalOrthogonalFinrankTarget_iff_lagrangian
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc]

set_option synthInstance.maxHeartbeats 500000 in
-- A graph-lagrangian rank certificate supplies the named pair rank target.
theorem sqdiagPairPresentationVerticalOrthogonalFinrankTarget_of_lagrangian_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hlag : sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d) :
    sqdiagPairPresentationVerticalOrthogonalFinrankTarget n a b c d :=
  (sqdiagPairPresentationVerticalOrthogonalFinrankTarget_iff_lagrangian
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd).mpr hlag

set_option synthInstance.maxHeartbeats 500000 in
-- Exact subtraction-free pair-rank shape obtained from the graph-lagrangian target.
theorem sqdiag_pairPresentationVerticalOrthogonal_finrank_target_of_lagrangian_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hlag : sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d) :
    Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
        Module.finrank F (SquareCombinedKernel n a b c d) +
        Module.finrank F
          (LinearMap.ker
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
        2 * (n - 1) ^ 3 =
      Int.toNat (X3AfterAZ a b c d n) +
        ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1)) := by
  exact
    sqdiagPairPresentationVerticalOrthogonalFinrankTarget_of_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hlag

set_option synthInstance.maxHeartbeats 500000 in
-- The named reduced rank target unfolds to the pair-presentation finrank certificate.
theorem sqdiag_pairPresentationVerticalOrthogonal_finrank_target_of_reducedRelation_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hred : sqdiagReducedRelationVerticalOrthogonalFinrankTarget n a b c d) :
    Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
        Module.finrank F (SquareCombinedKernel n a b c d) +
        Module.finrank F
          (LinearMap.ker
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
        2 * (n - 1) ^ 3 =
      Int.toNat (X3AfterAZ a b c d n) +
        ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1)) := by
  exact
    (sqdiagPairPresentationVerticalOrthogonalFinrankTarget_iff_reducedRelation
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd).mpr hred

set_option synthInstance.maxHeartbeats 500000 in
-- The named pair rank target unfolds back to the reduced finrank certificate.
theorem sqdiag_reducedRelationVerticalOrthogonal_finrank_target_of_pairPresentation_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hpair : sqdiagPairPresentationVerticalOrthogonalFinrankTarget n a b c d) :
    Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        Module.finrank F (SquareCombinedKernel n a b c d) +
        Module.finrank F
          (LinearMap.ker
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Int.toNat (X3AfterAZ a b c d n) := by
  exact
    (sqdiagPairPresentationVerticalOrthogonalFinrankTarget_iff_reducedRelation
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd).mp hpair

end

end SquareDiagonal
end Core4loop
