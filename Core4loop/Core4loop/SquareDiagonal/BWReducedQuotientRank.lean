import Core4loop.SquareDiagonal.BWReducedQuotientProfile
import Core4loop.SquareDiagonal.BWReducedProfileRank

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

set_option synthInstance.maxHeartbeats 200000 in
-- Combined quotient certificate: root-defect rank, vertical-orthogonal rank,
-- and vanishing of the reduced quadratic form on the vertical orthogonal.
def sqdiagReducedRelationRankAndQZeroCertificate
    (n a b c d : ℕ) [NeZero n] : Prop :=
  (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
      n * (n - 1) ^ 2 + (n - 1) ^ 3 =
    (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
  (Module.finrank F
      (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
      n * (n - 1) ^ 2 + (n - 1) ^ 3 =
    Module.finrank F
        (sqdiagReducedRelationVertical n a b c d) +
      ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
  (∀ x : SqdiagReducedRelation n a b c d,
    x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
      sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0)

set_option synthInstance.maxHeartbeats 500000 in
-- The reduced root-defect quotient dimension is the root-image annihilator
-- dimension.
theorem finrank_sqdiagReducedRelationRootDefect_eq_rootImageAnnihilator
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) =
      Module.finrank F
        (sqdiagBWAAdjointGraphRootImageAnnihilator n a b c d) := by
  have hdef :=
    finrank_sqdiagReducedRelationVerticalOrthogonal_eq_vertical_add_rootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hann :=
    finrank_sqdiagReducedRelationVerticalOrthogonal_eq_vertical_add_rootImageAnnihilator
      (n := n) (a := a) (b := b) (c := c) (d := d)
  omega

set_option synthInstance.maxHeartbeats 500000 in
-- The root-defect rank formula is the same annihilator profile-core target.
theorem sqdiagReducedRelationRootDefectRankTarget_iff_rootImageAnnihilatorProfileCore
    {n a b c d : ℕ} [NeZero n] :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ↔
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d := by
  unfold sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget
  have hann :=
    finrank_sqdiagReducedRelationRootDefect_eq_rootImageAnnihilator
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
-- The quotient rank-and-Q certificate is equivalent to the annihilator
-- profile-core rank target plus Q-vanishing on the vertical orthogonal.
theorem sqdiagReducedRelationRankAndQZeroCertificate_iff_rootImageAnnihilatorProfileCore_and_QZero
    {n a b c d : ℕ} [NeZero n] :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d ↔
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d ∧
        (∀ x : SqdiagReducedRelation n a b c d,
          x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
            sqdiagReducedRelationQ
              (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  unfold sqdiagReducedRelationRankAndQZeroCertificate
  constructor
  · intro hcert
    exact
      ⟨(sqdiagReducedRelationRootDefectRankTarget_iff_rootImageAnnihilatorProfileCore
          (n := n) (a := a) (b := b) (c := c) (d := d)).mp hcert.1,
        hcert.2.2⟩
  · intro h
    exact
      ⟨(sqdiagReducedRelationRootDefectRankTarget_iff_rootImageAnnihilatorProfileCore
          (n := n) (a := a) (b := b) (c := c) (d := d)).mpr h.1,
        (sqdiagReducedRelationVerticalOrthogonalRankGap_iff_rootImageAnnihilatorProfileCore
          (n := n) (a := a) (b := b) (c := c) (d := d)).mpr h.1,
        h.2⟩

-- Constructor form of the collapsed quotient certificate.
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_rootImageAnnihilatorProfileCore_and_QZero
    {n a b c d : ℕ} [NeZero n]
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d)
    (hQZero :
      ∀ x : SqdiagReducedRelation n a b c d,
        x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  (sqdiagReducedRelationRankAndQZeroCertificate_iff_rootImageAnnihilatorProfileCore_and_QZero
    (n := n) (a := a) (b := b) (c := c) (d := d)).mpr ⟨hann, hQZero⟩

-- Constructor form using the reduced root-zero A-coeff scalar-match condition,
-- which is equivalent to Q-vanishing on the reduced vertical orthogonal.
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_rootImageAnnihilatorProfileCore_and_rootZeroACoeffScalarMatch
    {n a b c d : ℕ} [NeZero n]
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d)
    (hmatch :
      sqdiagReducedRelationRootZeroACoeffScalarMatch n a b c d) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelationRankAndQZeroCertificate_of_rootImageAnnihilatorProfileCore_and_QZero
    (n := n) (a := a) (b := b) (c := c) (d := d) hann
    (sqdiagReducedRelationQ_eq_zero_of_rootZeroACoeffScalarMatch
      (n := n) (a := a) (b := b) (c := c) (d := d) hmatch)

-- Same constructor through the ambient pairing-match interface.
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_rootImageAnnihilatorProfileCore_and_ambientPairingMatchVertical
    {n a b c d : ℕ} [NeZero n]
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d)
    (hmatch :
      sqdiagAdjointAmbientPairingMatchVertical n a b c d) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelationRankAndQZeroCertificate_of_rootImageAnnihilatorProfileCore_and_QZero
    (n := n) (a := a) (b := b) (c := c) (d := d) hann
    (sqdiagReducedRelationQ_eq_zero_of_ambientPairingMatchVertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hmatch)

set_option synthInstance.maxHeartbeats 500000 in
-- The root-defect subtype expands through the reduced root-range kernel.
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_equiv_profile
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (e :
      sqdiagReducedRelationRootDefect n a b c d ≃ₗ[F]
        SqdiagReducedRootProfile n b d) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b := by
  rw [LinearEquiv.finrank_eq e]
  exact
    finrank_SqdiagReducedRootProfile_add_profile_core
      (n := n) (b := b) (d := d) hb hd

theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (e :
      SqdiagReducedRootProfile n b d ≃ₗ[F]
        sqdiagReducedRelationRootDefect n a b c d) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_equiv_profile
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd e.symm

set_option synthInstance.maxHeartbeats 500000 in
-- The proof combines the exact sequence subtype with the root-defect rank formula.
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_equiv_profile
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (e :
      sqdiagReducedRelationRootDefect n a b c d ≃ₗ[F]
        SqdiagReducedRootProfile n b d) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) := by
  have hseq :=
    finrank_sqdiagReducedRelationVerticalOrthogonal_eq_vertical_add_rootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hdef :=
    finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_equiv_profile
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd e
  omega

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (e :
      SqdiagReducedRootProfile n b d ≃ₗ[F]
        sqdiagReducedRelationRootDefect n a b c d) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_equiv_profile
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd e.symm

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedSectionWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth)) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedSectionWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth)) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_YZCorrectedSectionWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth)) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileYZCorrectedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_YZCorrectedSectionWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth)) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileYZCorrectedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_YZCorrectedSectionWithLine_rootZero_annihilates_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L Z p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ
          (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ hann))) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_YZCorrectedSectionWithLine_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ
    (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ hann)
    hbij

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_YZCorrectedSectionWithLine_rootZero_annihilates_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L Z p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ
          (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ hann))) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_YZCorrectedSectionWithLine_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ
    (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ hann)
    hbij

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth)) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth)) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedSectionWithLine_bijective_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (horth :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth)) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedSectionWithLine_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedSectionWithLine_bijective_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (horth :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth)) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedSectionWithLine_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hpair :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hpair))) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivPairSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hpair hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hpair :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hpair))) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivPairSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hpair hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_polar_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hpolar :
      ∀ (p : SqdiagReducedRootProfile n b d)
        (y : SqdiagAdjointAmbientPairPresentation n a b c d),
        y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d →
          sqdiagAdjointAmbientPairPresentationPolar
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L hZ p) y = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_polar_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hpolar))) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_polar_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hpolar)
      hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_polar_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hpolar :
      ∀ (p : SqdiagReducedRootProfile n b d)
        (y : SqdiagAdjointAmbientPairPresentation n a b c d),
        y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d →
          sqdiagAdjointAmbientPairPresentationPolar
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L hZ p) y = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_polar_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hpolar))) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_polar_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hpolar)
      hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_annihilates_root_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann))) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hann)
      hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_annihilates_root_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann))) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hann)
      hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_rootTarget_add_intersection_mem_annihilator_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hroot))) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hroot)
      hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_rootTarget_add_intersection_mem_annihilator_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hroot))) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hroot)
      hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffEval_eq_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (heval :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ heval))) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ heval)
      hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffEval_eq_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (heval :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ heval))) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ heval)
      hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffEval_comp_eq_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcomp :
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d)) =
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileIntersectionSectionRootWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_comp_eq
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hcomp))) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_comp_eq
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hcomp)
      hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffEval_comp_eq_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcomp :
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d)) =
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileIntersectionSectionRootWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_comp_eq
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hcomp))) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_comp_eq
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hcomp)
      hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionTraceKernelTwistWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth)) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionTraceKernelTwistWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ horth hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionTraceKernelTwistWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth)) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_profile_equiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
    (sqdiagReducedRootProfileNormalizedDefectEquivSectionTraceKernelTwistWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ horth hbij)

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange) p)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange)
          hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange hZ))) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b :=
  finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionTraceKernelTwistWithLine_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L
    (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange)
    hZ
    (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ)
    hbij

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange) p)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange)
          hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange hZ))) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) :=
  finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionTraceKernelTwistWithLine_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L
    (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange)
    hZ
    (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ)
    hbij

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_annihilates_root_bijective_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann))) :
    Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_annihilates_root_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann hbij

set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_annihilates_root_bijective_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann))) :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_annihilates_root_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann hbij

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedWithLine_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth hbij
  · exact
      finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedWithLine_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth hbij
  · intro x hx
    exact
      sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedWithLine_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth hbij hzero x hx

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionExplicitWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionExplicitWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionExplicitWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p).1.1 =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  have hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth) :=
    (sqdiagReducedRootProfileNormalizedToDefectWithLine_bijective_iff_rootTarget
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth).mpr hrootbij
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij hzero

set_option synthInstance.maxHeartbeats 500000 in
-- With the line-lift choice the explicit intersection adds no root target, so
-- the defect-map bijectivity can be checked on the profile skeleton root.
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_lineLift_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hM :
      LinearMap.range (sqdiagMatrixConstantRootCore (n := n)) ≤
        LinearMap.range (sqdiagLineCoreBuildR (n := n)))
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd
              (sqdiagReducedRootProfileLineLift
                (n := n) (b := b) (d := d) hM) p)).2 ∈
          LinearMap.range
            (sqdiagKCAdjointRangeEmbed
              (n := n) (a := a) (b := b) (d := d)))
    (horth :
      let L := sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM
      let hZ :=
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_forall_of_lineLift_coeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd hM hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p =
              R0.1.1.1))
    (hzero :
      let L := sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let L := sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM
  let hZ :=
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_forall_of_lineLift_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd hM hcoeff
  have hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth) :=
    (sqdiagReducedRootProfileNormalizedToDefectWithLine_bijective_iff_skeletonRootTarget_of_lineLift
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd hM hZ horth).mpr hrootbij
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_target_rootZero_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d :=
    sqdiagReducedRootProfileNormalizedRelationWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_target_rootZero_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionExplicitWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionExplicitWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionExplicitWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p).1.1 =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d :=
    sqdiagReducedRootProfileNormalizedRelationWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hrootbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_range_le_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (horth :
      let hZ :=
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedWithLine_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_range_le_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (horth :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hverticalCoeffRange :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedSectionWithLine_bijective_of_intersectionMaps_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hroot hcoeff horth hbij
  · exact
      finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedSectionWithLine_bijective_of_intersectionMaps_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hroot hcoeff horth hbij
  · intro x hx
    exact
      sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_le_bijective_of_intersectionMaps_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hroot hcoeff horth hbij hverticalCoeffRange x hx

set_option synthInstance.maxHeartbeats 500000 in
-- Constructor form of the section/coreparam route to the quotient certificate.
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionWithLine_range_le_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (horth :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hverticalCoeffRange :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_range_le_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hroot hcoeff horth hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedSectionWithLine_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth hbij
  · exact
      finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedSectionWithLine_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth hbij
  · intro x hx
    exact
      sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_le_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth hbij hverticalCoeffRange x hx

set_option synthInstance.maxHeartbeats 500000 in
-- Certificate constructor for the weak target-in-Z-adjoint interface.  Unlike
-- the older `range_le` constructor, this does not force the intersection root
-- coefficient through Z-matrix slices.
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionWithLine_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ horth hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionTraceKernelTwistWithLine_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ horth hbij
  · exact
      finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionTraceKernelTwistWithLine_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ horth hbij
  · intro x hx
    exact
      sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionTraceKernelTwistWithLine_reducedVerticalCoeffMap_range_le_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ horth hbij hverticalCoeffRange x hx

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_target_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L T hZ horth hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange) p)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange)
          hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange hZ)))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L
            (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange)
            hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_target_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L
    (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange)
    hZ
    (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ)
    hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange) p)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange)
          hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange hZ)))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L
            (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange)
            hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hEvalRange hZ hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange) p)
    (hrootTarget :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L
              (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L hEvalRange) p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L
              (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L hEvalRange) q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L
                (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L hEvalRange) p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L
            (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange) hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let T :=
    sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange
  let horth :=
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ
  have hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth) := by
    exact
      (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_bijective_iff_rootTarget
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ horth).mpr hrootTarget
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ hbij
      ((sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine_range_le_reducedVerticalCoeffMap_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ).mpr hverticalCoeffRange)

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange) p)
    (hrootTarget :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L
              (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L hEvalRange) p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L
              (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L hEvalRange) q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L
                (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L hEvalRange) p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L
            (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange) hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hEvalRange hZ hrootTarget hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcorrectionRootCoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange p).1 ∈
          LinearMap.range
            (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hrootTarget :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hZ0 hcorrectionRootCoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ0 hcorrectionRootCoeff
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ hrootTarget hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcorrectionRootCoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange p).1 ∈
          LinearMap.range
            (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hrootTarget :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hZ0 hcorrectionRootCoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hEvalRange hZ0 hcorrectionRootCoeff hrootTarget hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_targetFromBase_correctionRange_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcorrectionRootCoeffRange :
      LinearMap.range
          ((LinearMap.ker (SquareRootTrace (n := n) (c := c))).subtype.comp
            (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange)) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hrootTarget :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hZ0 hcorrectionRootCoeffRange
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ0 hcorrectionRootCoeffRange
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ hrootTarget hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_targetFromBase_correctionRange_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcorrectionRootCoeffRange :
      LinearMap.range
          ((LinearMap.ker (SquareRootTrace (n := n) (c := c))).subtype.comp
            (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange)) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hrootTarget :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hZ0 hcorrectionRootCoeffRange
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_targetFromBase_correctionRange_pointwiseCoeff_rootTarget_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hEvalRange hZ0 hcorrectionRootCoeffRange hrootTarget hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hrootTarget :
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let T :=
    sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ0
  let horth :=
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ
  have hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth) := by
    exact
      (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_bijective_iff_rootTarget
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ horth).mpr hrootTarget
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ horth hbij
      ((sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine_range_le_reducedVerticalCoeffMap_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ).mpr hverticalCoeffRange)

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hrootTarget :
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZSliceEvalRange hZ0 hrootTarget hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_targetFromBase_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (K : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagRootTraceKernelZSliceCoeffSpace n c)
    (hK :
      (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
        sqdiagReducedRootProfileRootZeroDemandMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hrootTarget :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let hZSliceEvalRange :=
    sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ0 hrootTarget hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_targetFromBase_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (K : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagRootTraceKernelZSliceCoeffSpace n c)
    (hK :
      (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
        sqdiagReducedRootProfileRootZeroDemandMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hrootTarget :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_targetFromBase_pointwiseCoeff_rootTarget_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L K hK hZ0 hrootTarget hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hbij :
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      let horth :=
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let T :=
    sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ0
  let horth :=
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ horth hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hbij :
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      let horth :=
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_target_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZSliceEvalRange hZ0 hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (K : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagRootTraceKernelZSliceCoeffSpace n c)
    (hK :
      (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
        sqdiagReducedRootProfileRootZeroDemandMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hbij :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      let horth :=
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth))
    (hverticalCoeffRange :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let hZSliceEvalRange :=
    sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ0 hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (K : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagRootTraceKernelZSliceCoeffSpace n c)
    (hK :
      (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
        sqdiagReducedRootProfileRootZeroDemandMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hbij :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      let horth :=
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth))
    (hverticalCoeffRange :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L K hK hZ0 hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective_verticalLift
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (K : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagRootTraceKernelZSliceCoeffSpace n c)
    (hK :
      (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
        sqdiagReducedRootProfileRootZeroDemandMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hbij :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      let horth :=
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth))
    (V : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationVertical n a b c d)
    (hV :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      (sqdiagReducedRelationVerticalCoeffMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp V =
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d := by
  let hZSliceEvalRange :=
    sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK
  let T :=
    sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ0
  have hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) :=
    (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine_range_le_reducedVerticalCoeffMap_iff_exists_linear_lift
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ).mpr ⟨V, hV⟩
  exact
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK hZ0 hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (K : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagRootTraceKernelZSliceCoeffSpace n c)
    (hK :
      (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
        sqdiagReducedRootProfileRootZeroDemandMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (U : sqdiagReducedRelationRootDefect n a b c d →ₗ[F]
      SqdiagReducedRootProfile n b d)
    (hU_left :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      let horth :=
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ
      U.comp
          (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ horth) =
        LinearMap.id)
    (hU_right :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      let horth :=
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ
      (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth).comp U =
        LinearMap.id)
    (V : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationVertical n a b c d)
    (hV :
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      (sqdiagReducedRelationVerticalCoeffMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp V =
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d := by
  let hZSliceEvalRange :=
    sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK
  let T :=
    sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ0
  let horth :=
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ
  have hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth) := by
    exact
      (linearMap_bijective_iff_exists_linear_inverse
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth)).mpr
        ⟨U, hU_left, hU_right⟩
  exact
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective_verticalLift
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK hZ0 hbij V hV

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift_targetLifts
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (R : SqdiagReducedRootProfile n b d →ₗ[F]
      ZeroSumProfileM n (MatrixZeroSum n))
    (hR :
      (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)).comp R =
        sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)
    (C : SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagKCAdjointRangeModel n b d)
    (hC :
      (sqdiagKCAdjointRangeEmbed
        (n := n) (a := a) (b := b) (d := d)).comp C =
        sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)
    (K : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagRootTraceKernelZSliceCoeffSpace n c)
    (hK :
      (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
        sqdiagReducedRootProfileRootZeroDemandMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)
    (U : sqdiagReducedRelationRootDefect n a b c d →ₗ[F]
      SqdiagReducedRootProfile n b d)
    (hU_left :
      let hZ0 :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_linear_lifts
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L R hR C hC
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      let horth :=
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ
      U.comp
          (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ horth) =
        LinearMap.id)
    (hU_right :
      let hZ0 :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_linear_lifts
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L R hR C hC
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      let horth :=
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ
      (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth).comp U =
        LinearMap.id)
    (V : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationVertical n a b c d)
    (hV :
      let hZ0 :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_linear_lifts
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L R hR C hC
      let hZSliceEvalRange :=
        sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L K hK
      let T :=
        sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange hZ0
      (sqdiagReducedRelationVerticalCoeffMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp V =
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L K hK
    (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_linear_lifts
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L R hR C hC)
    U hU_left hU_right V hV

structure SqdiagReducedTraceKernelZSliceTargetLiftCertificate
    (n a b c d : ℕ) [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : Type where
  L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n
  R : SqdiagReducedRootProfile n b d →ₗ[F]
    ZeroSumProfileM n (MatrixZeroSum n)
  hR :
    (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)).comp R =
      sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
  C : SqdiagReducedRootProfile n b d →ₗ[F]
    SqdiagKCAdjointRangeModel n b d
  hC :
    (sqdiagKCAdjointRangeEmbed
      (n := n) (a := a) (b := b) (d := d)).comp C =
      sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
  K : SqdiagReducedRootProfile n b d →ₗ[F]
    sqdiagRootTraceKernelZSliceCoeffSpace n c
  hK :
    (sqdiagRootTraceKernelZSlicePullYWEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
      sqdiagReducedRootProfileRootZeroDemandMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
  U : sqdiagReducedRelationRootDefect n a b c d →ₗ[F]
    SqdiagReducedRootProfile n b d
  hU_left :
    let hZ0 :=
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_linear_lifts
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L R hR C hC
    let hZSliceEvalRange :=
      sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L K hK
    let T :=
      sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZSliceEvalRange
    let hZ :=
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZSliceEvalRange hZ0
    let horth :=
      sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZSliceEvalRange hZ
    U.comp
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth) =
      LinearMap.id
  hU_right :
    let hZ0 :=
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_linear_lifts
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L R hR C hC
    let hZSliceEvalRange :=
      sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L K hK
    let T :=
      sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZSliceEvalRange
    let hZ :=
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZSliceEvalRange hZ0
    let horth :=
      sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZSliceEvalRange hZ
    (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ horth).comp U =
      LinearMap.id
  V : SqdiagReducedRootProfile n b d →ₗ[F]
    sqdiagReducedRelationVertical n a b c d
  hV :
    let hZ0 :=
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_linear_lifts
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L R hR C hC
    let hZSliceEvalRange :=
      sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L K hK
    let T :=
      sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZSliceEvalRange
    let hZ :=
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZSliceEvalRange hZ0
    (sqdiagReducedRelationVerticalCoeffMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp V =
      sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_traceKernelZSliceTargetLiftCertificate
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (cert :
      SqdiagReducedTraceKernelZSliceTargetLiftCertificate
        n a b c d hb hc hd) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift_targetLifts
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd cert.L cert.R cert.hR cert.C cert.hC cert.K cert.hK
    cert.U cert.hU_left cert.hU_right cert.V cert.hV

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_range_le_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hroot :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hbij :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange hZ)))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeff
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let T :=
    sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hroot hcoeff
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_range_le_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hroot :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hbij :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange hZ)))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeff
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_range_le_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hEvalRange hroot hcoeff hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hroot :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hbij :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hcoeffT :=
        sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hcoeff
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeffT
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange hZ)))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hcoeffT :=
        sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hcoeff
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeffT
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let hcoeffT :=
    sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hcoeff
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_range_le_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeffT hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hroot :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hbij :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hcoeffT :=
        sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hcoeff
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeffT
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange hZ)))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hcoeffT :=
        sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hcoeff
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeffT
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hEvalRange hroot hcoeff hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hroot :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hrootTarget :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hcoeffT :=
        sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hcoeff
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeffT
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let T :=
    sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange
  let hcoeffT :=
    sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hcoeff
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hroot hcoeffT
  let horth :=
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ
  have hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth) := by
    exact
      (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_bijective_iff_rootTarget
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ horth).mpr hrootTarget
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeff hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hroot :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hrootTarget :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hcoeffT :=
        sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hcoeff
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeffT
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_rootTarget_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hEvalRange hroot hcoeff hrootTarget hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hroot :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hrootTarget :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hcoeffT :=
        sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hcoeff
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeffT
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let T :=
    sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange
  let hcoeffT :=
    sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hcoeff
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hroot hcoeffT
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeff hrootTarget
      ((sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine_range_le_reducedVerticalCoeffMap_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ).mpr hverticalCoeffRange)

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hroot :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hrootTarget :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      let T :=
        sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange
      let hcoeffT :=
        sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange hcoeff
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hroot hcoeffT
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_pointwiseCoeff_rootTarget_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hEvalRange hroot hcoeff hrootTarget hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootTarget_add_intersection_mem_annihilator_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hroot)))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_rootTarget_add_intersection_mem_annihilator_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hroot hbij
  · exact
      finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_rootTarget_add_intersection_mem_annihilator_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hroot hbij
  · intro x hx
    exact
      sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_le_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ
        (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ hroot)
        hbij hverticalCoeffRange x hx

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionWithLine_target_rootTarget_add_intersection_mem_annihilator_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hroot)))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootTarget_add_intersection_mem_annihilator_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ hroot hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootZeroACoeffEval_eq_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (heval :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ heval)))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffEval_eq_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ heval hbij
  · exact
      finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffEval_eq_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ heval hbij
  · intro x hx
    exact
      sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_le_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ
        (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ heval)
        hbij hverticalCoeffRange x hx

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionWithLine_target_rootZeroACoeffEval_eq_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (heval :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ heval)))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootZeroACoeffEval_eq_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ heval hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootZeroACoeffEval_comp_eq_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcomp :
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d)) =
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileIntersectionSectionRootWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_comp_eq
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hcomp)))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffEval_comp_eq_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hcomp hbij
  · exact
      finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_normalizedPairSectionWithLine_rootZeroACoeffEval_comp_eq_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hcomp hbij
  · intro x hx
    exact
      sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_le_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ
        (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_comp_eq
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ hcomp)
        hbij hverticalCoeffRange x hx

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionWithLine_target_rootZeroACoeffEval_comp_eq_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcomp :
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d)) =
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileIntersectionSectionRootWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_comp_eq
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hcomp)))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootZeroACoeffEval_comp_eq_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ hcomp hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth))
    (hQZero :
      ∀ x : SqdiagReducedRelation n a b c d,
        x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  refine ⟨?_, ?_, hQZero⟩
  · exact
      finrank_sqdiagReducedRelationRootDefect_add_profile_core_of_YZCorrectedSectionWithLine_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L Z hZ horth hbij
  · exact
      finrank_sqdiagReducedRelationVerticalOrthogonal_add_profile_core_of_YZCorrectedSectionWithLine_bijective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L Z hZ horth hbij

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_YZCorrectedSectionWithLine_target_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth))
    (hQZero :
      ∀ x : SqdiagReducedRelation n a b c d,
        x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ horth hbij hQZero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ horth hbij
    (sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_YZCorrectedSectionWithLine_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth hbij hzero)

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_YZCorrectedSectionWithLine_target_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_rootCoeff_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ horth hbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z q) →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
              R0.1.1.1))
    (hQZero :
      ∀ x : SqdiagReducedRelation n a b c d,
        x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  have hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth) :=
    (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_bijective_iff_rootTarget
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth).mpr hrootbij
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth hbij hQZero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_YZCorrectedSectionWithLine_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z q) →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
              R0.1.1.1))
    (hQZero :
      ∀ x : SqdiagReducedRelation n a b c d,
        x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ horth hrootbij hQZero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z q) →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  have hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth) :=
    (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_bijective_iff_rootTarget
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth).mpr hrootbij
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_rootCoeff_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth hbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_YZCorrectedSectionWithLine_rootTarget_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z q) →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootCoeff_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ horth hrootbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_rootZero_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L Z p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ
          (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ hann)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d :=
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ hann
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_rootCoeff_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth hbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_YZCorrectedSectionWithLine_target_rootZero_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L Z p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ
          (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ hann)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_rootZero_rootCoeff_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ hann hbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootZero_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L Z p)).1 = 0)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z q) →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d :=
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ hann
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootCoeff_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth hrootbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_YZCorrectedSectionWithLine_rootTarget_rootZero_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L Z p)).1 = 0)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z q) →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootZero_rootCoeff_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ hann hrootbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_rootAnnihilator_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ
          (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_mem_annihilator_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ hroot)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d :=
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_mem_annihilator_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ hroot
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_rootCoeff_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth hbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_YZCorrectedSectionWithLine_target_rootAnnihilator_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ
          (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_mem_annihilator_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ hroot)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_target_rootAnnihilator_rootCoeff_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ hroot hbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootAnnihilator_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z q) →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d :=
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_mem_annihilator_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ hroot
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootCoeff_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth hrootbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRankAndQZeroCertificate_of_YZCorrectedSectionWithLine_rootTarget_rootAnnihilator_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z q) →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootAnnihilator_rootCoeff_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ hroot hrootbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootAnnihilatorRange_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hrootRange :
      LinearMap.range
          (sqdiagReducedRootProfileYZCorrectedRootTarget
            (n := n) (b := b) (c := c) (d := d) Z) ≤
        sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileYZCorrectedRootTarget
              (n := n) (b := b) (c := c) (d := d) Z p =
            sqdiagReducedRootProfileYZCorrectedRootTarget
              (n := n) (b := b) (c := c) (d := d) Z q →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileYZCorrectedRootTarget
                (n := n) (b := b) (c := c) (d := d) Z p =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  have hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d := by
    intro p
    have hp :
        sqdiagReducedRootProfileYZCorrectedRootTarget
            (n := n) (b := b) (c := c) (d := d) Z p ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d :=
      hrootRange ⟨p, rfl⟩
    simpa [sqdiagReducedRootProfileYZCorrectedRootTarget_apply] using hp
  have hrootbij' :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z q) →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
              R0.1.1.1) := by
    constructor
    · intro p q hpq
      exact hrootbij.1 p q
        (by
          simpa [sqdiagReducedRootProfileYZCorrectedRootTarget_apply] using hpq)
    · intro R0
      rcases hrootbij.2 R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      simpa [sqdiagReducedRootProfileYZCorrectedRootTarget_apply] using hp
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootAnnihilator_rootCoeff_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ hroot hrootbij' hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem
    sqdiagReducedRelationRankAndQZeroCertificate_of_YZCorrectedSectionWithLine_rootTarget_rootAnnihilatorRange_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hrootRange :
      LinearMap.range
          (sqdiagReducedRootProfileYZCorrectedRootTarget
            (n := n) (b := b) (c := c) (d := d) Z) ≤
        sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileYZCorrectedRootTarget
              (n := n) (b := b) (c := c) (d := d) Z p =
            sqdiagReducedRootProfileYZCorrectedRootTarget
              (n := n) (b := b) (c := c) (d := d) Z q →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileYZCorrectedRootTarget
                (n := n) (b := b) (c := c) (d := d) Z p =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootAnnihilatorRange_rootCoeff_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ hrootRange hrootbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootZeroEvalRange_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d))) ≤
        LinearMap.range
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (pullYZ (n := n) (b := b) (c := c) (d := d))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange) p)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileYZCorrectedRootTarget
              (n := n) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange) p =
            sqdiagReducedRootProfileYZCorrectedRootTarget
              (n := n) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange) q →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileYZCorrectedRootTarget
                (n := n) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
                  (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange) p =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
              (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange)
              p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
                (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
                  (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange)
                p)).1 = 0) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootTarget_rootAnnihilatorRange_rootCoeff_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L
      (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange)
      hZ
      (sqdiagReducedRootProfileYZCorrectedRootTarget_range_le_rootZeroACoeffAnnihilator_of_rootZeroEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange)
      hrootbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem
    sqdiagReducedRelationRankAndQZeroCertificate_of_YZCorrectedSectionWithLine_rootZeroEvalRange_rootCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d))) ≤
        LinearMap.range
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (pullYZ (n := n) (b := b) (c := c) (d := d))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange) p)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileYZCorrectedRootTarget
              (n := n) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange) p =
            sqdiagReducedRootProfileYZCorrectedRootTarget
              (n := n) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange) q →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileYZCorrectedRootTarget
                (n := n) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
                  (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange) p =
              R0.1.1.1))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
              (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange)
              p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
                (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
                  (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange)
                p)).1 = 0) :
    sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
  sqdiagReducedRelation_rank_and_Q_eq_zero_of_YZCorrectedSectionWithLine_rootZeroEvalRange_rootCoeff_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hEvalRange hZ hrootbij hzero

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  have hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth) :=
    (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_bijective_iff_rootTarget
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth).mpr hrootbij
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootZero_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d :=
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootZero_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  let horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d :=
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hrootbij hverticalCoeffRange

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootZero_pointwiseCoeff_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hverticalCoeffRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootZero_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann hbij
      ((sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine_range_le_reducedVerticalCoeffMap_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ).mpr hverticalCoeffRange)

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootZero_pointwiseCoeff_rootTarget_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hrootbij :
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p).1.1 =
              R0.1.1.1))
    (hverticalCoeffRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b) ∧
    (Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b)) ∧
    (∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0) := by
  exact
    sqdiagReducedRelation_rank_and_Q_eq_zero_of_normalizedSectionWithLine_target_rootZero_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann hrootbij
      ((sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine_range_le_reducedVerticalCoeffMap_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ).mpr hverticalCoeffRange)

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationVerticalOrthogonalFinrankTarget_of_verticalProfileFinrankTarget
    {n a b c d : ℕ} [NeZero n]
    (hrank :
      Module.finrank F
          (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          n * (n - 1) ^ 2 + (n - 1) ^ 3 =
        Module.finrank F
            (sqdiagReducedRelationVertical n a b c d) +
          ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b))
    (hfin : sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d) :
    sqdiagReducedRelationVerticalOrthogonalFinrankTarget n a b c d := by
  unfold sqdiagReducedRelationVerticalProfileFinrankTarget at hfin
  unfold sqdiagReducedRelationVerticalOrthogonalFinrankTarget
  omega

set_option synthInstance.maxHeartbeats 500000 in
-- This packages the quotient rank gap with the pre-quotient profile target.
theorem sqdiagReducedRelationVerticalOrthogonalFinrankTarget_of_rank_and_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hfin : sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d) :
    sqdiagReducedRelationVerticalOrthogonalFinrankTarget n a b c d :=
  by
  unfold sqdiagReducedRelationRankAndQZeroCertificate at hrankQ
  exact
    sqdiagReducedRelationVerticalOrthogonalFinrankTarget_of_verticalProfileFinrankTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) hrankQ.2.1 hfin

set_option synthInstance.maxHeartbeats 500000 in
-- This unfolds the quotient certificate before applying the profile/orthogonal bridge.
theorem sqdiagReducedRelationVerticalProfileFinrankTarget_of_rankQ_and_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (horth : sqdiagReducedRelationVerticalOrthogonalFinrankTarget n a b c d) :
    sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d := by
  unfold sqdiagReducedRelationRankAndQZeroCertificate at hrankQ
  exact
    sqdiagReducedRelationVerticalProfileFinrankTarget_of_verticalOrthogonalFinrankTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) hrankQ.2.1 horth

set_option synthInstance.maxHeartbeats 500000 in
-- A graph-lagrangian rank certificate supplies the pre-quotient profile target
-- once the quotient rank gap is known.
theorem sqdiagReducedRelationVerticalProfileFinrankTarget_of_rank_and_Q_zero_and_lagrangian
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hlag : sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d) :
    sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d :=
  sqdiagReducedRelationVerticalProfileFinrankTarget_of_rankQ_and_verticalOrthogonal
    (n := n) (a := a) (b := b) (c := c) (d := d) hrankQ
    (sqdiagReducedRelationVerticalOrthogonalFinrankTarget_of_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hlag)

set_option synthInstance.maxHeartbeats 500000 in
-- The same quotient rank gap converts the pre-quotient profile target back
-- into the graph-lagrangian rank target.
theorem sqdiagBWAAdjointGraphLagrangianFinrankTarget_of_rankQ_and_verticalProfile
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hprofile : sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d) :
    sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d :=
  (sqdiagReducedRelationVerticalOrthogonalFinrankTarget_iff_lagrangian
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hc).mp
    (sqdiagReducedRelationVerticalOrthogonalFinrankTarget_of_rank_and_Q_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) hrankQ hprofile)

set_option synthInstance.maxHeartbeats 500000 in
-- With the quotient rank certificate fixed, the profile and lagrangian rank
-- targets are equivalent formulations of the same remaining rank statement.
theorem sqdiagReducedRelationVerticalProfileFinrankTarget_iff_lagrangian_of_rankQ
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d) :
    sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d := by
  constructor
  · intro hprofile
    exact
      sqdiagBWAAdjointGraphLagrangianFinrankTarget_of_rankQ_and_verticalProfile
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ hprofile
  · intro hlag
    exact
      sqdiagReducedRelationVerticalProfileFinrankTarget_of_rank_and_Q_zero_and_lagrangian
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ hlag

set_option synthInstance.maxHeartbeats 500000 in
-- The root-zero graph profile target is also equivalent after the quotient
-- rank gap is fixed.
theorem sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_lagrangian_of_rankQ
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d) :
    sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d := by
  rw [← sqdiagReducedRelationVerticalProfileFinrankTarget_iff_rootZeroProfile
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc,
    sqdiagReducedRelationVerticalProfileFinrankTarget_iff_lagrangian_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ]

set_option synthInstance.maxHeartbeats 500000 in
-- With the quotient rank certificate fixed, the pre-quotient profile target
-- is equivalent to the root-zero/root-image-annihilator rank target.
theorem sqdiagReducedRelationVerticalProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d) :
    sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d := by
  rw [sqdiagReducedRelationVerticalProfileFinrankTarget_iff_lagrangian_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ,
    sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_rootZeroAnnihilator
      (n := n) (a := a) (b := b) (c := c) (d := d) hc]

set_option synthInstance.maxHeartbeats 500000 in
-- The root-zero graph profile target and the root-image-annihilator target
-- are equivalent under the same quotient rank certificate.
theorem sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d) :
    sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d ↔
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d := by
  rw [sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_lagrangian_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ,
    sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_rootZeroAnnihilator
      (n := n) (a := a) (b := b) (c := c) (d := d) hc]

theorem sqdiagReducedRelationQ_eq_zero_of_rankAndQZeroCertificate
    {n a b c d : ℕ} [NeZero n]
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d) :
    ∀ x : SqdiagReducedRelation n a b c d,
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  unfold sqdiagReducedRelationRankAndQZeroCertificate at hrankQ
  exact hrankQ.2.2

end

end SquareDiagonal
end Core4loop
