import Core4loop.SquareDiagonal.BWSupportRank
import Core4loop.SquareDiagonal.BWPairPresentation
import Core4loop.SquareDiagonal.BWQuadraticRank
import Core4loop.SquareDiagonal.BWQuadraticWitness
import Core4loop.SquareDiagonal.BWReducedProfileRank
import Core4loop.SquareDiagonal.BWReducedQuotientRank

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

theorem survivor_sum_Q3_eq_BW_classified_value
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    (∑ B : BFun4 n a c d,
      ∑ W : WFun4 n a b c,
        sqdiagCFiberValue (n := n) (a := a) (b := b) (c := c) (d := d) B W) := by
  exact sqdiag_survivor_sum_as_BW_classified_value
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem survivor_sum_Q3_eq_BW_ZDiff_kernel_classified_value
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    (∑ B : BFun4 n a c d,
      ∑ W : WFun4 n a b c,
        sqdiagCFiberClassifiedValue
          (n := n) (a := a) (b := b) (c := c) (d := d) B W) := by
  exact sqdiag_survivor_sum_as_BW_ZDiff_kernel_classified_value
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_support_fiber_sum
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : sqdiagBWZCompatSupport n a b c d,
      sqdiagCFiberValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
      =
    (Nat.card (sqdiagBWZCompatSupport n a b c d) : ℤ) *
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact sqdiag_sum_over_BWZCompatSupport_fiberValue
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_support_card
    {n a b c d : ℕ} [NeZero n] :
    Nat.card (sqdiagBWZCompatSupport n a b c d) =
      2 ^ Module.finrank F
        (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  exact natCard_sqdiagBWZCompatSupport
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_adjoint_support_card
    {n a b c d : ℕ} [NeZero n] :
    Nat.card (sqdiagBWZAdjointSupport n a b c d) =
      2 ^ Module.finrank F
        (sqdiagBWZAdjointSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  exact natCard_sqdiagBWZAdjointSupport
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BWA_adjoint_graph_support_card
    {n a b c d : ℕ} [NeZero n] :
    Nat.card (sqdiagBWAAdjointGraphSupport n a b c d) =
      2 ^ Module.finrank F
        (sqdiagBWAAdjointGraphSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  exact natCard_sqdiagBWAAdjointGraphSupport
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BWA_adjoint_graph_rootCoeffSign_sum
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      ∑ x : sqdiagBWAAdjointGraphSupport n a b c d,
        bitSign
          (sqdiagRootCoeffApply x.1.2
            (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1)) := by
  rfl

theorem BWA_adjoint_graph_witness_rootCoeffApply_eq
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWAAdjointGraphSupport n a b c d) :
    sqdiagRootCoeffApply
        (sqdiagBWZAdjointWitness
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagBWAAdjointGraphToBWZAdjointSupport
            (n := n) (a := a) (b := b) (c := c) (d := d) x))
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1) =
      sqdiagRootCoeffApply x.1.2
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1) := by
  exact sqdiagBWAAdjointGraph_witness_rootCoeffApply_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) x

theorem BW_ZDiff_adjoint_support_classified_sum
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    (∑ x : sqdiagBWZAdjointSupport n a b c d,
      sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2) := by
  exact sqdiag_survivor_sum_as_BWZAdjointSupport_classifiedValue
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_adjoint_support_rootCoeffSign_sum
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      ∑ x : sqdiagBWZAdjointSupport n a b c d,
        bitSign
          (sqdiagRootCoeffApply
            (sqdiagBWZAdjointWitness
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
            (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
  exact sqdiag_survivor_sum_eq_kernelCard_mul_BWZAdjointSupport_rootCoeffSign
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_adjoint_witness_fiber_total_sum
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZAdjointWitnessFiberTotalSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        sqdiagBWZAdjointRootCoeffSignSum
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact sqdiagBWZAdjointWitnessFiberTotalSignSum_eq_KCAdjointKernelCard_mul_rootCoeffSignSum
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_adjoint_witness_fiber_total_survivor_bridge
    {n a b c d : ℕ} [NeZero n] :
    sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      (∑ x : Surviving_yzw n a b c d,
        bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      sqdiagBWZAdjointWitnessFiberTotalSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact
    sqdiagKCAdjointKernelCard_mul_survivor_sum_eq_CKernelCard_mul_BWZAdjointWitnessFiberTotalSignSum
      (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_witness_fiber_total
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      sqdiagBWZAdjointWitnessFiberTotalSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact sqdiagBWAAdjointGraphRootSignSum_eq_BWZAdjointWitnessFiberTotalSignSum
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BWA_adjoint_graph_survivor_bridge
    {n a b c d : ℕ} [NeZero n] :
    sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      (∑ x : Surviving_yzw n a b c d,
        bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact
    sqdiagKCAdjointKernelCard_mul_survivor_sum_eq_CKernelCard_mul_BWAAdjointGraphRootSignSum
      (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hQzero :
      ∀ x : SqdiagBWAAdjointGraph n a b c d,
        x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d →
          sqdiagBWAAdjointGraphQ x = 0) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  exact sqdiagBWAAdjointGraphRootSignSum_eq_lagrangian_card_of_Q_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hQzero

/--
Conditional diagnostic route only.
The surjectivity premise is false for the general positive SquareDiagonal
family; production proofs should use the reduced-relation or pair-presentation
entrypoints below.
-/
theorem BWA_adjoint_graph_lagrangian_Q_zero_of_image_root_projection_surjective
    {n a b c d : ℕ} [NeZero n]
    (hsurj :
      Function.Surjective
        (sqdiagBWZCompatImageRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  exact
    sqdiagBWAAdjointGraphQ_eq_zero_of_mem_lagrangian_of_imageRootMap_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) hsurj x hx

theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_image_root_projection_surjective
    {n a b c d : ℕ} [NeZero n]
    (hsurj :
      Function.Surjective
        (sqdiagBWZCompatImageRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  exact
    BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_Q_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_image_root_projection_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d) hsurj x hx)

theorem BWA_adjoint_graph_lagrangian_Q_zero_of_ambient_pair_coeff_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hzero :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 :=
  sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentation_coeff_rootCoeff_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hzero x hx

theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_ambient_pair_coeff_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hzero :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  exact
    BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_Q_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_ambient_pair_coeff_rootCoeff_zero
          (n := n) (a := a) (b := b) (c := c) (d := d) hzero x hx)

theorem BWA_adjoint_graph_lagrangian_Q_zero_of_ambient_pairing_match_vertical
    {n a b c d : ℕ} [NeZero n]
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 :=
  sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentation_pairing_match_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d) hmatch x hx

theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_ambient_pairing_match_vertical
    {n a b c d : ℕ} [NeZero n]
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  exact
    BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_Q_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_ambient_pairing_match_vertical
          (n := n) (a := a) (b := b) (c := c) (d := d) hmatch x hx)

theorem BWA_adjoint_graph_lagrangian_Q_zero_of_reduced_relation_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 :=
  sqdiagBWAAdjointGraphQ_eq_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
    (n := n) (a := a) (b := b) (c := c) (d := d) hred x hx

theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_reduced_relation_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  exact
    BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_Q_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_reduced_relation_Q_zero
          (n := n) (a := a) (b := b) (c := c) (d := d) hred x hx)

set_option synthInstance.maxHeartbeats 200000 in
-- Reduced vertical dimension equality makes the reduced phase vanish on the orthogonal space.
theorem BWA_adjoint_graph_lagrangian_Q_zero_of_reduced_relation_verticalOrthogonal_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hphasefin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d))
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 :=
  BWA_adjoint_graph_lagrangian_Q_zero_of_reduced_relation_Q_zero
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (fun z hz =>
      sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_finrank_eq
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hphasefin z hz)
    x hx

set_option synthInstance.maxHeartbeats 200000 in
-- This is the graph root-sign endpoint for the reduced dimension phase certificate.
theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_reduced_relation_verticalOrthogonal_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hphasefin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d)) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  exact
    BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_Q_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_reduced_relation_verticalOrthogonal_finrank_eq
          (n := n) (a := a) (b := b) (c := c) (d := d) hphasefin x hx)

set_option synthInstance.maxHeartbeats 500000 in
-- Reduced polar/root image-rank equality supplies the graph phase certificate.
theorem BWA_adjoint_graph_lagrangian_Q_zero_of_reduced_relation_polarRootRankMatch
    {n a b c d : ℕ} [NeZero n]
    (hrange : sqdiagReducedRelationPolarRootRankMatch n a b c d)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 :=
  BWA_adjoint_graph_lagrangian_Q_zero_of_reduced_relation_verticalOrthogonal_finrank_eq
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRelationVerticalOrthogonal_finrank_eq_vertical_of_polarRange_finrank_eq_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hrange)
    x hx

set_option synthInstance.maxHeartbeats 500000 in
-- Root-sign endpoint using the reduced polar/root image-rank certificate.
theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_reduced_relation_polarRootRankMatch
    {n a b c d : ℕ} [NeZero n]
    (hrange : sqdiagReducedRelationPolarRootRankMatch n a b c d) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  exact
    BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_Q_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_reduced_relation_polarRootRankMatch
          (n := n) (a := a) (b := b) (c := c) (d := d) hrange x hx)

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero graph A-coefficient separation is the current production phase certificate.
theorem BWA_adjoint_graph_lagrangian_Q_zero_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 :=
  sqdiagBWAAdjointGraphQ_eq_zero_of_rootZeroACoeffSpace_separates_reducedRoot
    (n := n) (a := a) (b := b) (c := c) (d := d) hsep x hx

set_option synthInstance.maxHeartbeats 500000 in
-- Root-sign endpoint using the root-zero graph A-coefficient separation certificate.
theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  exact
    BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_Q_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_rootZeroACoeffSpace_separates_reducedRoot
          (n := n) (a := a) (b := b) (c := c) (d := d) hsep x hx)

theorem BWA_adjoint_graph_lagrangian_Q_zero_of_pair_presentation_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 :=
  sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
    (n := n) (a := a) (b := b) (c := c) (d := d) hpair x hx

theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_pair_presentation_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  exact
    BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_Q_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_pair_presentation_Q_zero
          (n := n) (a := a) (b := b) (c := c) (d := d) hpair x hx)

set_option synthInstance.maxHeartbeats 200000 in
-- The pair vertical-orthogonal finrank term is a nested kernel subtype.
theorem BWA_adjoint_graph_lagrangian_Q_zero_of_pair_presentation_verticalOrthogonal_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hphasefin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d))
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 :=
  sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_verticalOrthogonal_finrank_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) hphasefin x hx

set_option synthInstance.maxHeartbeats 200000 in
-- This endpoint reuses the same nested pair vertical-orthogonal finrank term.
theorem BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_pair_presentation_verticalOrthogonal_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hphasefin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d)) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  exact
    BWA_adjoint_graph_rootCoeffSign_sum_eq_lagrangian_card_of_Q_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_pair_presentation_verticalOrthogonal_finrank_eq
          (n := n) (a := a) (b := b) (c := c) (d := d) hphasefin x hx)

theorem survivor_sum_Q3_eq_pow_of_BWA_adjoint_graph_eval
    {n a b c d : ℕ} [NeZero n]
    (hgraph :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        sqdiagBWAAdjointGraphRootSignSum
          (n := n) (a := a) (b := b) (c := c) (d := d) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  apply mul_left_cancel₀
    (sqdiagKCAdjointKernelCardZ_ne_zero
      (n := n) (a := a) (b := b) (c := c) (d := d))
  calc
    sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (∑ x : Surviving_yzw n a b c d,
          bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2))
        =
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        sqdiagBWAAdjointGraphRootSignSum
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
        exact BWA_adjoint_graph_survivor_bridge
          (n := n) (a := a) (b := b) (c := c) (d := d)
    _ =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := hgraph

theorem survivor_sum_Q3_eq_pow_of_lagrangian_phase_and_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hQzero :
      ∀ x : SqdiagBWAAdjointGraph n a b c d,
        x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d →
          sqdiagBWAAdjointGraphQ x = 0)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact survivor_sum_Q3_eq_pow_of_BWA_adjoint_graph_eval
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagBWAAdjointGraphRootSignSum_weighted_eval_of_Q_zero_of_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d) hQzero hcard)

theorem survivor_sum_Q3_eq_pow_of_image_root_projection_surjective_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hsurj :
      Function.Surjective
        (sqdiagBWZCompatImageRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_lagrangian_phase_and_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_image_root_projection_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d) hsurj x hx)
      hcard

theorem survivor_sum_Q3_eq_pow_of_ambient_pair_coeff_rootCoeff_zero_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hzero :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_lagrangian_phase_and_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_ambient_pair_coeff_rootCoeff_zero
          (n := n) (a := a) (b := b) (c := c) (d := d) hzero x hx)
      hcard

theorem survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_lagrangian_phase_and_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_ambient_pairing_match_vertical
          (n := n) (a := a) (b := b) (c := c) (d := d) hmatch x hx)
      hcard

theorem survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_lagrangian_phase_and_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_reduced_relation_Q_zero
          (n := n) (a := a) (b := b) (c := c) (d := d) hred x hx)
      hcard

set_option synthInstance.maxHeartbeats 200000 in
-- Reduced dimension phase plus the existing weighted-card certificate.
theorem survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hphasefin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d))
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun z hz =>
        sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_finrank_eq
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hphasefin z hz)
      hcard

set_option synthInstance.maxHeartbeats 500000 in
-- Reduced polar/root image-rank equality plus the weighted-card certificate.
theorem survivor_sum_Q3_eq_pow_of_reduced_relation_polarRootRankMatch_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hrange : sqdiagReducedRelationPolarRootRankMatch n a b c d)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRelationVerticalOrthogonal_finrank_eq_vertical_of_polarRange_finrank_eq_rootRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hrange)
      hcard

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero graph A-coefficient separation plus weighted-cardinality gives the survivor sum.
theorem survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_lagrangian_phase_and_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_rootZeroACoeffSpace_separates_reducedRoot
          (n := n) (a := a) (b := b) (c := c) (d := d) hsep x hx)
      hcard

theorem survivor_sum_Q3_eq_pow_of_pair_presentation_Q_zero_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_lagrangian_phase_and_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_pair_presentation_Q_zero
          (n := n) (a := a) (b := b) (c := c) (d := d) hpair x hx)
      hcard

set_option synthInstance.maxHeartbeats 200000 in
-- Pair-presentation dimension phase plus the existing weighted-card certificate.
theorem survivor_sum_Q3_eq_pow_of_pair_presentation_verticalOrthogonal_finrank_eq_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hphasefin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d))
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_lagrangian_phase_and_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x hx =>
        BWA_adjoint_graph_lagrangian_Q_zero_of_pair_presentation_verticalOrthogonal_finrank_eq
          (n := n) (a := a) (b := b) (c := c) (d := d) hphasefin x hx)
      hcard

theorem survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_lagrangian_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hred
      (lagrangian_weighted_card_of_finrank_lagrangian_add_CFun4
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Reduced dimension phase plus the lagrangian finrank certificate.
theorem survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hphasefin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d))
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hphasefin
      (lagrangian_weighted_card_of_finrank_lagrangian_add_CFun4
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero graph A-coefficient separation plus the clean lagrangian finrank certificate.
theorem survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_lagrangian_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hsep
      (lagrangian_weighted_card_of_finrank_lagrangian_add_CFun4
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- The reduced vertical-orthogonal finrank term is a nested kernel subtype.
theorem survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hred
      (lagrangian_weighted_card_of_reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Reduced dimension phase plus the reduced vertical-rank certificate.
theorem survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hphasefin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d))
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hphasefin
      (lagrangian_weighted_card_of_reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Reduced polar/root image-rank equality plus the reduced vertical-rank certificate.
theorem survivor_sum_Q3_eq_pow_of_reduced_relation_polarRootRankMatch_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrange : sqdiagReducedRelationPolarRootRankMatch n a b c d)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_reduced_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc
      (sqdiagReducedRelationVerticalOrthogonal_finrank_eq_vertical_of_polarRange_finrank_eq_rootRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hrange)
      hfin

set_option synthInstance.maxHeartbeats 500000 in
-- The remaining reverse rank inequality plus reduced rank is enough for the survivor sum.
theorem survivor_sum_Q3_eq_pow_of_reduced_relation_rootRank_le_polarRank_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hle : sqdiagReducedRelationRootRankLePolarRank n a b c d)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_polarRootRankMatch_and_reduced_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc
      (sqdiagReducedRelationPolarRootRankMatch_of_rootRange_finrank_le_polarRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hle)
      hfin

set_option synthInstance.maxHeartbeats 500000 in
-- Injectivity of the induced root-to-polar map plus reduced rank is enough for the survivor sum.
theorem survivor_sum_Q3_eq_pow_of_reduced_relation_rootRangeToPolarVertical_injective_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hinj :
      Function.Injective
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_rootRank_le_polarRank_and_reduced_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc
      (sqdiagReducedRelationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
        (n := n) (a := a) (b := b) (c := c) (d := d) hinj)
      hfin

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero graph A-coefficient separation plus the reduced vertical-rank certificate.
theorem survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_rootRangeToPolarVertical_injective_and_reduced_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc
      (sqdiagReducedRelationRootRangeToPolarVertical_injective_of_rootZeroACoeffSpace_separates_reducedRoot
        (n := n) (a := a) (b := b) (c := c) (d := d) hsep)
      hfin

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero graph A-coefficient separation plus pair-presentation rank certificate.
theorem survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hsep
      (lagrangian_weighted_card_of_pairPresentationVerticalOrthogonal_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- The reverse kernel inclusion plus reduced rank is enough for the survivor sum.
theorem survivor_sum_Q3_eq_pow_of_reduced_relation_polarToVertical_ker_le_rootMap_ker_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hker :
      LinearMap.ker
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_rootRank_le_polarRank_and_reduced_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc
      (sqdiagReducedRelationRootRankLePolarRank_of_polarToVertical_ker_le_rootMap_ker
        (n := n) (a := a) (b := b) (c := c) (d := d) hker)
      hfin

set_option synthInstance.maxHeartbeats 200000 in
-- This endpoint reuses the same nested reduced vertical-orthogonal finrank term.
theorem survivor_sum_Q3_eq_pow_of_pair_presentation_Q_zero_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_pair_presentation_Q_zero_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hpair
      (lagrangian_weighted_card_of_reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Pair-presentation phase plus pair-presentation rank certificate.
theorem survivor_sum_Q3_eq_pow_of_pair_presentation_Q_zero_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_pair_presentation_Q_zero_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hpair
      (lagrangian_weighted_card_of_pairPresentationVerticalOrthogonal_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Pair-presentation dimension phase plus pair-presentation rank certificate.
theorem survivor_sum_Q3_eq_pow_of_pair_presentation_verticalOrthogonal_finrank_eq_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hphasefin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d))
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_pair_presentation_verticalOrthogonal_finrank_eq_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hphasefin
      (lagrangian_weighted_card_of_pairPresentationVerticalOrthogonal_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Pair reverse rank inequality plus pair-presentation rank certificate.
theorem survivor_sum_Q3_eq_pow_of_pair_presentation_rootRank_le_polarRank_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hle : sqdiagAdjointPairPresentationRootRankLePolarRank n a b c d)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_pair_presentation_Q_zero_and_pair_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd
      (fun x hx =>
        sqdiagAdjointPairPresentationQ_eq_zero_of_rootRange_finrank_le_polarRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hle x hx)
      hfin

set_option synthInstance.maxHeartbeats 500000 in
-- Pair induced-map injectivity plus pair-presentation rank certificate.
theorem survivor_sum_Q3_eq_pow_of_pair_presentation_rootRangeToPolarVertical_injective_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hinj :
      Function.Injective
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_pair_presentation_rootRank_le_polarRank_and_pair_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd
      (sqdiagAdjointPairPresentationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
        (n := n) (a := a) (b := b) (c := c) (d := d) hinj)
      hfin

set_option synthInstance.maxHeartbeats 500000 in
-- Pair reverse kernel inclusion plus pair-presentation rank certificate.
theorem survivor_sum_Q3_eq_pow_of_pair_presentation_polarToVertical_ker_le_rootMap_ker_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hker :
      LinearMap.ker
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_pair_presentation_rootRangeToPolarVertical_injective_and_pair_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd
      (sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_of_polarToVertical_ker_le_rootMap_ker
        (n := n) (a := a) (b := b) (c := c) (d := d) hker)
      hfin

set_option synthInstance.maxHeartbeats 200000 in
-- Ambient pairing-match phase plus reduced vertical-rank certificate.
theorem survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hmatch
      (lagrangian_weighted_card_of_reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Ambient pairing-match phase plus pair-presentation rank certificate.
theorem survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hmatch
      (lagrangian_weighted_card_of_pairPresentationVerticalOrthogonal_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd hfin)

theorem DeltaNF_squareDiagonal_eq_pow_support_of_BWA_adjoint_graph_eval
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hgraph :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        sqdiagBWAAdjointGraphRootSignSum
          (n := n) (a := a) (b := b) (c := c) (d := d) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_BWA_adjoint_graph_eval
        (n := n) (a := a) (b := b) (c := c) (d := d) hgraph)

theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_BWA_adjoint_graph_eval
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hgraph :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        sqdiagBWAAdjointGraphRootSignSum
          (n := n) (a := a) (b := b) (c := c) (d := d) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_BWA_adjoint_graph_eval
        (n := n) (a := a) (b := b) (c := c) (d := d) hgraph)

theorem DeltaNF_squareDiagonal_eq_pow_support_of_ambient_pair_coeff_rootCoeff_zero_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hzero :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_ambient_pair_coeff_rootCoeff_zero_and_lagrangian_weighted_card
        (n := n) (a := a) (b := b) (c := c) (d := d) hzero hcard)

theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pair_coeff_rootCoeff_zero_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hzero :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_ambient_pair_coeff_rootCoeff_zero_and_lagrangian_weighted_card
        (n := n) (a := a) (b := b) (c := c) (d := d) hzero hcard)

theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_Q_zero_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_lagrangian_weighted_card
        (n := n) (a := a) (b := b) (c := c) (d := d) hred hcard)

set_option synthInstance.maxHeartbeats 200000 in
-- Support-form endpoint using reduced dimension phase and weighted-card certificate.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hphasefin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d))
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_weighted_card
        (n := n) (a := a) (b := b) (c := c) (d := d) hphasefin hcard)

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using reduced polar/root image-rank equality and weighted card.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_polarRootRankMatch_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrange : sqdiagReducedRelationPolarRootRankMatch n a b c d)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_polarRootRankMatch_and_lagrangian_weighted_card
        (n := n) (a := a) (b := b) (c := c) (d := d) hrange hcard)

theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_Q_zero_and_lagrangian_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_lagrangian_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hred hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Support-form endpoint using reduced dimension phase and lagrangian finrank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hphasefin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d))
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hphasefin hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using root-zero graph A-coefficient separation and lagrangian finrank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_rootZeroACoeffSpace_separates_reducedRoot_and_lagrangian_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_lagrangian_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hsep hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- The reduced vertical-orthogonal finrank term is a nested kernel subtype.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_Q_zero_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hred hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Support-form endpoint using reduced dimension phase and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_verticalOrthogonal_finrank_eq_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hphasefin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d))
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hphasefin hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using reduced polar/root image-rank equality and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_polarRootRankMatch_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrange : sqdiagReducedRelationPolarRootRankMatch n a b c d)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_polarRootRankMatch_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hrange hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using the remaining reverse rank inequality and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_rootRank_le_polarRank_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hle : sqdiagReducedRelationRootRankLePolarRank n a b c d)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_rootRank_le_polarRank_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hle hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using injectivity of the induced root-to-polar map.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_rootRangeToPolarVertical_injective_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hinj :
      Function.Injective
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_rootRangeToPolarVertical_injective_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hinj hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using root-zero graph A-coefficient separation and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_rootZeroACoeffSpace_separates_reducedRoot_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hsep hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using root-zero graph A-coefficient separation and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_rootZeroACoeffSpace_separates_reducedRoot_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_pair_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hb hc hd hsep hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using the reverse kernel inclusion and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_reduced_relation_polarToVertical_ker_le_rootMap_ker_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hker :
      LinearMap.ker
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_polarToVertical_ker_le_rootMap_ker_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hker hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- This endpoint combines pair-presentation phase with reduced vertical finrank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_pair_presentation_Q_zero_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_pair_presentation_Q_zero_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hpair hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Final support-form endpoint using pair-presentation phase and pair-rank certificates.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_pair_presentation_Q_zero_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_pair_presentation_Q_zero_and_pair_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hb hc hd hpair hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Final support-form endpoint using pair-presentation dimension phase and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_pair_presentation_verticalOrthogonal_finrank_eq_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hphasefin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d))
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_pair_presentation_verticalOrthogonal_finrank_eq_and_pair_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hb hc hd hphasefin hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using pair reverse rank inequality and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_pair_presentation_rootRank_le_polarRank_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hle : sqdiagAdjointPairPresentationRootRankLePolarRank n a b c d)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_pair_presentation_rootRank_le_polarRank_and_pair_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hb hc hd hle hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using pair induced-map injectivity and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_pair_presentation_rootRangeToPolarVertical_injective_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hinj :
      Function.Injective
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_pair_presentation_rootRank_le_polarRank_and_pair_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hAfter
      (sqdiagAdjointPairPresentationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
        (n := n) (a := a) (b := b) (c := c) (d := d) hinj)
      hfin

set_option synthInstance.maxHeartbeats 500000 in
-- Support-form endpoint using pair reverse kernel inclusion and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_pair_presentation_polarToVertical_ker_le_rootMap_ker_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hker :
      LinearMap.ker
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_pair_presentation_rootRangeToPolarVertical_injective_and_pair_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hAfter
      (sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_of_polarToVertical_ker_le_rootMap_ker
        (n := n) (a := a) (b := b) (c := c) (d := d) hker)
      hfin

set_option synthInstance.maxHeartbeats 200000 in
-- Final support-form endpoint using ambient pairing-match phase and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_ambient_pairing_match_vertical_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hmatch hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Final support-form endpoint using ambient pairing-match phase and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_support_of_ambient_pairing_match_vertical_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (supportSumZ a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_support_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_pair_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hb hc hd hmatch hfin)

theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_Q_zero_and_lagrangian_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_lagrangian_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hred hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- X3Z-form endpoint using reduced dimension phase and lagrangian finrank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hphasefin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d))
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_lagrangian_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hphasefin hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- X3Z-form endpoint using root-zero graph A-coefficient separation and lagrangian finrank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rootZeroACoeffSpace_separates_reducedRoot_and_lagrangian_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_lagrangian_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hsep hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- The reduced vertical-orthogonal finrank term is a nested kernel subtype.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_Q_zero_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hred hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- X3Z-form endpoint using reduced dimension phase and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_verticalOrthogonal_finrank_eq_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hphasefin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d))
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_verticalOrthogonal_finrank_eq_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hphasefin hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- X3Z-form endpoint using reduced polar/root image-rank equality and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_polarRootRankMatch_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrange : sqdiagReducedRelationPolarRootRankMatch n a b c d)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_polarRootRankMatch_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hrange hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- X3Z-form endpoint using the remaining reverse rank inequality and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_rootRank_le_polarRank_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hle : sqdiagReducedRelationRootRankLePolarRank n a b c d)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_rootRank_le_polarRank_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hle hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- X3Z-form endpoint using injectivity of the induced root-to-polar map.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_rootRangeToPolarVertical_injective_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hinj :
      Function.Injective
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_rootRangeToPolarVertical_injective_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hinj hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- X3Z-form endpoint using root-zero graph A-coefficient separation and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rootZeroACoeffSpace_separates_reducedRoot_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hsep hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- X3Z-form endpoint using root-zero graph A-coefficient separation and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rootZeroACoeffSpace_separates_reducedRoot_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_rootZeroACoeffSpace_separates_reducedRoot_and_pair_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hb hc hd hsep hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- X3Z-form endpoint using the reverse kernel inclusion and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_polarToVertical_ker_le_rootMap_ker_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hker :
      LinearMap.ker
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_polarToVertical_ker_le_rootMap_ker_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hker hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- This endpoint combines pair-presentation phase with reduced vertical finrank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_pair_presentation_Q_zero_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_pair_presentation_Q_zero_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hpair hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Final X3Z-form endpoint using pair-presentation phase and pair-rank certificates.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_pair_presentation_Q_zero_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_pair_presentation_Q_zero_and_pair_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hb hc hd hpair hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Final X3Z-form endpoint using pair-presentation dimension phase and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_pair_presentation_verticalOrthogonal_finrank_eq_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hphasefin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d))
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_pair_presentation_verticalOrthogonal_finrank_eq_and_pair_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hb hc hd hphasefin hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- X3Z-form endpoint using pair reverse rank inequality and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_pair_presentation_rootRank_le_polarRank_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hle : sqdiagAdjointPairPresentationRootRankLePolarRank n a b c d)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_pair_presentation_rootRank_le_polarRank_and_pair_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hb hc hd hle hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- X3Z-form endpoint using pair induced-map injectivity and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_pair_presentation_rootRangeToPolarVertical_injective_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hinj :
      Function.Injective
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_pair_presentation_rootRank_le_polarRank_and_pair_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hAfter
      (sqdiagAdjointPairPresentationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
        (n := n) (a := a) (b := b) (c := c) (d := d) hinj)
      hfin

set_option synthInstance.maxHeartbeats 500000 in
-- X3Z-form endpoint using pair reverse kernel inclusion and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_pair_presentation_polarToVertical_ker_le_rootMap_ker_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hker :
      LinearMap.ker
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_pair_presentation_rootRangeToPolarVertical_injective_and_pair_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hAfter
      (sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_of_polarToVertical_ker_le_rootMap_ker
        (n := n) (a := a) (b := b) (c := c) (d := d) hker)
      hfin

set_option synthInstance.maxHeartbeats 200000 in
-- Final X3Z-form endpoint using ambient pairing-match phase and reduced rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_reduced_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_reduced_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hmatch hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- The named reduced rank target unfolds to the existing final reduced-rank endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_reduced_finrank_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin : sqdiagReducedRelationVerticalOrthogonalFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_reduced_vertical_finrank
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hAfter hmatch hfin

set_option synthInstance.maxHeartbeats 200000 in
-- Final X3Z-form endpoint using ambient pairing-match phase and pair rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_pair_vertical_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_pair_vertical_finrank
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hb hc hd hmatch hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- The named pair rank target unfolds to the existing final pair-rank endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_pair_finrank_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin : sqdiagPairPresentationVerticalOrthogonalFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_pair_vertical_finrank
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hb hc hd hAfter hmatch hfin

set_option synthInstance.maxHeartbeats 500000 in
-- Positive-parameter endpoint once the two remaining phase/rank certificates are available.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_pair_finrank_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin : sqdiagPairPresentationVerticalOrthogonalFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_pair_finrank_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hb hc hd
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hmatch hfin

set_option synthInstance.maxHeartbeats 500000 in
-- The balanced pair-rank target keeps the intersection term explicit.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_pair_balanced_finrank_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin :
      sqdiagPairPresentationVerticalOrthogonalBalancedFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_pair_finrank_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hb hc hd hAfter hmatch
    ((sqdiagPairPresentationVerticalOrthogonalBalancedFinrankTarget_iff_pairTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd).mp hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Ambient pairing-match phase plus the named graph-lagrangian rank target.
theorem survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_lagrangian_finrank_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin : sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_lagrangian_weighted_card
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hmatch
      (lagrangian_weighted_card_of_finrank_lagrangian_add_CFun4
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Final X3Z-form endpoint using ambient pairing-match phase and graph-lagrangian rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_ambient_pairing_match_vertical_and_lagrangian_finrank_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hfin : sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_ambient_pairing_match_vertical_and_lagrangian_finrank_target
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ha hc hmatch hfin)

theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_Q_zero_and_lagrangian_weighted_card
    {n a b c d : ℕ} [NeZero n]
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (hcard :
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n)) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_survivor_sum_Q3_eq_pow
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hAfter
      (survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_lagrangian_weighted_card
        (n := n) (a := a) (b := b) (c := c) (d := d) hred hcard)

set_option synthInstance.maxHeartbeats 500000 in
-- Final quotient-certificate survivor endpoint with the pre-quotient profile rank target.
theorem survivor_sum_Q3_eq_pow_of_reduced_relation_rankAndQZero_and_vertical_profile_finrank_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hfin : sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_Q_zero_and_reduced_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc
      (sqdiagReducedRelationQ_eq_zero_of_rankAndQZeroCertificate
        (n := n) (a := a) (b := b) (c := c) (d := d) hrankQ)
      (sqdiagReducedRelationVerticalOrthogonalFinrankTarget_of_rank_and_Q_zero
        (n := n) (a := a) (b := b) (c := c) (d := d) hrankQ hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Final X3Z endpoint from the quotient certificate plus the pre-quotient profile rank target.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_rankAndQZero_and_vertical_profile_finrank_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hfin : sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_Q_zero_and_reduced_vertical_finrank
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc hAfter
      (sqdiagReducedRelationQ_eq_zero_of_rankAndQZeroCertificate
        (n := n) (a := a) (b := b) (c := c) (d := d) hrankQ)
      (sqdiagReducedRelationVerticalOrthogonalFinrankTarget_of_rank_and_Q_zero
        (n := n) (a := a) (b := b) (c := c) (d := d) hrankQ hfin)

set_option synthInstance.maxHeartbeats 500000 in
-- Positive-parameter version using the existing nonnegativity certificate for X3AfterAZ.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_rankAndQZero_and_vertical_profile_finrank_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hfin : sqdiagReducedRelationVerticalProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_rankAndQZero_and_vertical_profile_finrank_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hrankQ hfin

-- Quotient-certificate survivor endpoint using the graph-lagrangian rank target.
theorem survivor_sum_Q3_eq_pow_of_rankQ_and_lagrangian_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hlag : sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_reduced_relation_rankAndQZero_and_vertical_profile_finrank_target
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ
      (sqdiagReducedRelationVerticalProfileFinrankTarget_of_rank_and_Q_zero_and_lagrangian
        (n := n) (a := a) (b := b) (c := c) ha hc hrankQ hlag)

-- Final X3Z endpoint from the quotient certificate plus graph-lagrangian rank.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_lagrangian_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hlag : sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_reduced_relation_rankAndQZero_and_vertical_profile_finrank_target
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hAfter hrankQ
      (sqdiagReducedRelationVerticalProfileFinrankTarget_of_rank_and_Q_zero_and_lagrangian
        (n := n) (a := a) (b := b) (c := c) ha hc hrankQ hlag)

-- Positive-parameter version of the quotient + graph-lagrangian endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_lagrangian_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hlag : sqdiagBWAAdjointGraphLagrangianFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_lagrangian_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hrankQ hlag

-- Quotient-certificate survivor endpoint using the adjoint-support/polar-image rank target.
theorem survivor_sum_Q3_eq_pow_of_rankQ_and_adjointSupportPolarImage_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupport : sqdiagBWZAdjointSupportPolarImageFinrankTarget n a b c d) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportPolarImage
        (n := n) (a := a) (b := b) (c := c) (d := d)).mpr hsupport)

-- Final X3Z endpoint from the quotient certificate plus the adjoint-support/polar-image target.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportPolarImage_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupport : sqdiagBWZAdjointSupportPolarImageFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc hAfter hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportPolarImage
        (n := n) (a := a) (b := b) (c := c) (d := d)).mpr hsupport)

-- Positive-parameter version of the quotient + adjoint-support/polar-image endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportPolarImage_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupport : sqdiagBWZAdjointSupportPolarImageFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportPolarImage_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hrankQ hsupport

-- Quotient-certificate survivor endpoint using the adjoint-support/root-zero A-dual target.
theorem survivor_sum_Q3_eq_pow_of_rankQ_and_adjointSupportRootZeroACoeffDual_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportDual : sqdiagBWZAdjointSupportRootZeroACoeffDualFinrankTarget n a b c d) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootZeroACoeffDual
        (n := n) (a := a) (b := b) (c := c) (d := d)).mpr hsupportDual)

-- Final X3Z endpoint from the quotient certificate plus the adjoint-support/root-zero A-dual target.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootZeroACoeffDual_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportDual : sqdiagBWZAdjointSupportRootZeroACoeffDualFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc hAfter hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootZeroACoeffDual
        (n := n) (a := a) (b := b) (c := c) (d := d)).mpr hsupportDual)

-- Positive-parameter version of the quotient + adjoint-support/root-zero A-dual endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootZeroACoeffDual_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportDual : sqdiagBWZAdjointSupportRootZeroACoeffDualFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootZeroACoeffDual_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hrankQ hsupportDual

-- Quotient-certificate survivor endpoint using the KC-eliminated adjoint-support/A-dual target.
theorem survivor_sum_Q3_eq_pow_of_rankQ_and_adjointSupportRootZeroACoeffDualNoKC_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportDual :
      sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget n a b c d) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootZeroACoeffDualNoKC
        (n := n) (a := a) (b := b) (c := c) (d := d) hc).mpr hsupportDual)

-- Final X3Z endpoint from the quotient certificate plus the KC-eliminated A-dual target.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootZeroACoeffDualNoKC_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportDual :
      sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc hAfter hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootZeroACoeffDualNoKC
        (n := n) (a := a) (b := b) (c := c) (d := d) hc).mpr hsupportDual)

-- Positive-parameter version of the quotient + KC-eliminated A-dual endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootZeroACoeffDualNoKC_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportDual :
      sqdiagBWZAdjointSupportRootZeroACoeffDualNoKCFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootZeroACoeffDualNoKC_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hrankQ hsupportDual

-- Quotient-certificate survivor endpoint using the root-image evaluation NoKC target.
theorem survivor_sum_Q3_eq_pow_of_rankQ_and_adjointSupportRootImageEvalNoKC_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportRootImage :
      sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget n a b c d) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootImageEvalNoKC
        (n := n) (a := a) (b := b) (c := c) (d := d) hc).mpr hsupportRootImage)

-- Final X3Z endpoint from the quotient certificate plus the root-image evaluation NoKC target.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootImageEvalNoKC_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportRootImage :
      sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc hAfter hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootImageEvalNoKC
        (n := n) (a := a) (b := b) (c := c) (d := d) hc).mpr hsupportRootImage)

-- Positive-parameter version of the quotient + root-image evaluation NoKC endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootImageEvalNoKC_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportRootImage :
      sqdiagBWZAdjointSupportRootImageEvalNoKCFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootImageEvalNoKC_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hrankQ hsupportRootImage

-- Quotient-certificate survivor endpoint using the root-image annihilator NoKC target.
theorem survivor_sum_Q3_eq_pow_of_rankQ_and_adjointSupportRootImageAnnihilatorNoKC_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportRootImage :
      sqdiagBWZAdjointSupportRootImageAnnihilatorNoKCFinrankTarget n a b c d) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootImageAnnihilatorNoKC
        (n := n) (a := a) (b := b) (c := c) (d := d) hc).mpr hsupportRootImage)

-- Final X3Z endpoint from the quotient certificate plus the root-image annihilator NoKC target.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootImageAnnihilatorNoKC_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportRootImage :
      sqdiagBWZAdjointSupportRootImageAnnihilatorNoKCFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc hAfter hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_adjointSupportRootImageAnnihilatorNoKC
        (n := n) (a := a) (b := b) (c := c) (d := d) hc).mpr hsupportRootImage)

-- Positive-parameter version of the quotient + root-image annihilator NoKC endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootImageAnnihilatorNoKC_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hsupportRootImage :
      sqdiagBWZAdjointSupportRootImageAnnihilatorNoKCFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_adjointSupportRootImageAnnihilatorNoKC_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hrankQ hsupportRootImage

-- Quotient-certificate survivor endpoint using the graph root-zero/root-image-annihilator target.
theorem survivor_sum_Q3_eq_pow_of_rankQ_and_rootZeroAnnihilator_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  exact
    survivor_sum_Q3_eq_pow_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_rootZeroAnnihilator
        (n := n) (a := a) (b := b) (c := c) (d := d) hc).mpr hrootZero)

-- Final X3Z endpoint from the quotient certificate plus the graph root-zero
-- root-image-annihilator rank target.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_lagrangian_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc hAfter hrankQ
      ((sqdiagBWAAdjointGraphLagrangianFinrankTarget_iff_rootZeroAnnihilator
        (n := n) (a := a) (b := b) (c := c) (d := d) hc).mpr hrootZero)

-- Positive-parameter version of the quotient + graph root-zero/root-image-annihilator endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrankQ : sqdiagReducedRelationRankAndQZeroCertificate n a b c d)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Final endpoint for the section/coreparam quotient route.  The remaining
-- E2-C work is concentrated in the section range, orthogonality, bijectivity,
-- and vertical-coefficient hypotheses below.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionWithLine_range_le_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionWithLine_range_le_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hroot hcoeff horth hbij hverticalCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Same final endpoint when the graph root-zero target is supplied in profile
-- form; the quotient certificate converts it to the annihilator target.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionWithLine_range_le_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionWithLine_range_le_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hroot hcoeff horth hbij hverticalCoeffRange
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Final endpoint for the trace-kernel twist route.  The root-zero eval range
-- condition supplies the vertical-orthogonal section used in the quotient
-- rank-and-Q certificate.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ hbij hverticalCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Same trace-kernel endpoint with the graph root-zero target supplied in
-- profile form.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ hbij hverticalCoeffRange
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Range-form final endpoint for the trace-kernel twist route.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_range_le_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_range_le_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeff hbij hverticalCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Range-form trace-kernel endpoint with the graph root-zero target supplied
-- in profile form.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_range_le_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_range_le_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeff hbij hverticalCoeffRange
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero-eval trace-kernel endpoint where the coeff range is stated for
-- the untwisted normalized section; the constructed twist has zero compat
-- component, so this implies the corresponding twisted coeff range.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeff hbij hverticalCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeff hbij hverticalCoeffRange
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Same endpoint as the section-coeff trace-kernel variant, but the
-- section-to-defect bijectivity is stated by the equivalent rootTarget test.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_rootTarget_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeff hrootTarget hverticalCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero profile form of the rootTarget trace-kernel endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_rootTarget_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeff hrootTarget hverticalCoeffRange
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Pointwise vertical-coeff form of the rootTarget trace-kernel endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_pointwiseCoeff_rootTarget_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeff hrootTarget hverticalCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero profile form of the pointwise rootTarget trace-kernel endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_pointwiseCoeff_rootTarget_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_sectionCoeffRange_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hroot hcoeff hrootTarget hverticalCoeffRange
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Final form using the trace-kernel target predicate directly, with pointwise
-- rootTarget and vertical-coeff hypotheses.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ hrootTarget hverticalCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero profile form of the direct trace-kernel target endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ hrootTarget hverticalCoeffRange
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Final endpoint where the trace-kernel target condition is derived from the
-- base section target and the correction root-coeff range.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ0 hcorrectionRootCoeff
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd L hEvalRange hZ hrootTarget hverticalCoeffRange hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero profile form of the base-target trace-kernel endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ0 hcorrectionRootCoeff
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective_and_rootZeroProfile_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd L hEvalRange hZ hrootTarget hverticalCoeffRange hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Base-target trace-kernel endpoint with correction membership supplied as a
-- single range inclusion.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_targetFromBase_correctionRange_pointwiseCoeff_rootTarget_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ0 hcorrectionRootCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd L hEvalRange hZ hrootTarget hverticalCoeffRange hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Same range-inclusion endpoint with the graph root-zero target supplied in
-- profile form.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_targetFromBase_correctionRange_pointwiseCoeff_rootTarget_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ0 hcorrectionRootCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelTwistWithLine_rootZeroEvalRange_target_pointwiseCoeff_rootTarget_bijective_and_rootZeroProfile_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd L hEvalRange hZ hrootTarget hverticalCoeffRange hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Final endpoint using the Z-slice restricted trace-kernel eval range.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ0 hrootTarget hverticalCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Same Z-slice restricted final endpoint with the graph root-zero target
-- supplied in profile form.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_rootZeroZSliceEvalRange_targetFromBase_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange hZ0 hrootTarget hverticalCoeffRange
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Final endpoint using an explicit Z-slice trace-kernel correction operator.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_targetFromBase_pointwiseCoeff_rootTarget_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_targetFromBase_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK hZ0 hrootTarget hverticalCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Same explicit-correction endpoint with the root-zero target in profile form.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_targetFromBase_pointwiseCoeff_rootTarget_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_targetFromBase_pointwiseCoeff_rootTarget_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK hZ0 hrootTarget hverticalCoeffRange
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Final endpoint using an explicit Z-slice correction, with the Rank-side
-- assumptions stated as the actual defect-map bijectivity and a linear range
-- inclusion.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK hZ0 hbij hverticalCoeffRange
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Same explicit-correction endpoint, with the root-zero target supplied in
-- profile form.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK hZ0 hbij hverticalCoeffRange
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Same actual-defect endpoint, replacing the vertical range inclusion by an
-- explicit linear lift through the reduced vertical relation.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective_verticalLift_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
          hb hc hd L T hZ)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective_verticalLift
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK hZ0 hbij V hV
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Vertical-lift version of the final profile-target endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective_verticalLift_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
          hb hc hd L T hZ)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_bijective_verticalLift
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK hZ0 hbij V hV
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Final endpoint with the actual defect-map bijectivity supplied by an
-- explicit two-sided linear inverse.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
          hb hc hd L T hZ)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK hZ0 U hU_left hU_right V hV
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Linear-inverse version of the final profile-target endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
          hb hc hd L T hZ)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L K hK hZ0 U hU_left hU_right V hV
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Final endpoint whose base normalized-section target is supplied by explicit
-- linear lifts into the two target models.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift_targetLifts_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
          hb hc hd L T hZ)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift_targetLifts
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L R hR C hC K hK U hU_left hU_right V hV
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Profile-target variant of the explicit target-lift final endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift_targetLifts_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
          hb hc hd L T hZ)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_normalizedSectionTraceKernelZSliceTwistWithLine_linearCorrection_target_linearInverse_verticalLift_targetLifts
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L R hR C hC K hK U hU_left hU_right V hV
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

set_option synthInstance.maxHeartbeats 500000 in
-- Compact final endpoint: all trace-kernel/Z-slice target-lift data is packed
-- into one certificate object.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_traceKernelZSliceTargetLiftCertificate_and_rootZeroAnnihilator_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (cert :
      SqdiagReducedTraceKernelZSliceTargetLiftCertificate
        n a b c d hb hc hd)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_traceKernelZSliceTargetLiftCertificate
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd cert
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootZero

set_option synthInstance.maxHeartbeats 500000 in
-- Compact profile-target variant of the certificate endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_traceKernelZSliceTargetLiftCertificate_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (cert :
      SqdiagReducedTraceKernelZSliceTargetLiftCertificate
        n a b c d hb hc hd)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_traceKernelZSliceTargetLiftCertificate
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd cert
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rankQ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target_positive
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hb hc hd hrankQ hrootAnn

-- Survivor endpoint from the split quotient/profile certificate and the
-- root-zero profile target.
theorem survivor_sum_Q3_eq_pow_of_profileCore_QZero_and_rootZeroProfile_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d)
    (hQZero :
      ∀ x : SqdiagReducedRelation n a b c d,
        x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_rootImageAnnihilatorProfileCore_and_QZero
      (n := n) (a := a) (b := b) (c := c) (d := d) hann hQZero
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rootImageAnnihilatorProfileCore
      (n := n) (a := a) (b := b) (c := c) (d := d) hann).mp hrootZero
  exact
    survivor_sum_Q3_eq_pow_of_rankQ_and_rootZeroAnnihilator_target
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hrankQ hrootAnn

-- Final X3Z endpoint from the split quotient/profile certificate and the
-- root-zero profile target.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_QZero_and_rootZeroProfile_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d)
    (hQZero :
      ∀ x : SqdiagReducedRelation n a b c d,
        x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) := by
  have hrankQ :
      sqdiagReducedRelationRankAndQZeroCertificate n a b c d :=
    sqdiagReducedRelationRankAndQZeroCertificate_of_rootImageAnnihilatorProfileCore_and_QZero
      (n := n) (a := a) (b := b) (c := c) (d := d) hann hQZero
  have hrootAnn :
      sqdiagBWAAdjointGraphRootZeroAnnihilatorFinrankTarget n a b c d :=
    (sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget_iff_rootZeroAnnihilator_of_rootImageAnnihilatorProfileCore
      (n := n) (a := a) (b := b) (c := c) (d := d) hann).mp hrootZero
  exact
    DeltaNF_squareDiagonal_eq_pow_X3Z_of_rankQ_and_rootZeroAnnihilator_target
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ha hc hAfter hrankQ hrootAnn

-- Positive-parameter version of the split quotient/profile endpoint.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_QZero_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d)
    (hQZero :
      ∀ x : SqdiagReducedRelation n a b c d,
        x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_QZero_and_rootZeroProfile_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hann hQZero hrootZero

-- Split endpoint with Q-zero supplied through the reduced root-zero A-coeff
-- scalar-match interface.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_rootZeroACoeffScalarMatch_and_rootZeroProfile_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d)
    (hmatch :
      sqdiagReducedRelationRootZeroACoeffScalarMatch n a b c d)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_QZero_and_rootZeroProfile_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc hAfter hann
    (sqdiagReducedRelationQ_eq_zero_of_rootZeroACoeffScalarMatch
      (n := n) (a := a) (b := b) (c := c) (d := d) hmatch)
    hrootZero

theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_rootZeroACoeffScalarMatch_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d)
    (hmatch :
      sqdiagReducedRelationRootZeroACoeffScalarMatch n a b c d)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_rootZeroACoeffScalarMatch_and_rootZeroProfile_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hann hmatch hrootZero

-- Same split endpoint with Q-zero supplied through ambient pairing-match.
theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_ambientPairingMatchVertical_and_rootZeroProfile_target
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hAfter : 0 ≤ X3AfterAZ a b c d n)
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d)
    (hmatch :
      sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_QZero_and_rootZeroProfile_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc hAfter hann
    (sqdiagReducedRelationQ_eq_zero_of_ambientPairingMatchVertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hmatch)
    hrootZero

theorem DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_ambientPairingMatchVertical_and_rootZeroProfile_target_positive
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hann :
      sqdiagBWAAdjointGraphRootImageAnnihilatorProfileCoreFinrankTarget n a b c d)
    (hmatch :
      sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (hrootZero :
      sqdiagBWAAdjointGraphRootZeroProfileFinrankTarget n a b c d) :
    DeltaNF .squareDiagonal a b c d n =
      (2 : ℤ) ^ Int.toNat (X3Z a b c d n) :=
  DeltaNF_squareDiagonal_eq_pow_X3Z_of_profileCore_ambientPairingMatchVertical_and_rootZeroProfile_target
    (n := n) (a := a) (b := b) (c := c) (d := d)
    ha hc
    (X3AfterAZ_nonneg_of_positive
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd)
    hann hmatch hrootZero

theorem BW_ZDiff_compat_support_fiber_sum_finrank
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : sqdiagBWZCompatSupport n a b c d,
      sqdiagCFiberValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
      =
    ((2 ^ Module.finrank F
      (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) : ℕ) : ℤ) *
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [BW_ZDiff_compat_support_fiber_sum
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  rw [natCard_sqdiagBWZCompatSupport
    (n := n) (a := a) (b := b) (c := c) (d := d)]

theorem SquareCombined_kernel_fiber_sum
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : SquareCombinedKernel n a b c d,
      sqdiagCFiberValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
      =
    (Nat.card (SquareCombinedKernel n a b c d) : ℤ) *
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact sqdiag_sum_over_SquareCombinedKernel_fiberValue
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem C_phase_linear_zero_iff_squareCompat_zero
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W = 0 ↔
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0 := by
  exact sqdiagCPhaseLinear_eq_zero_iff_squareCompat_eq_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) B W

theorem C_phase_kernel_zero_iff_exists_KC_adjoint_coeff
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    sqdiagCPhaseKernelZero (n := n) (a := a) (b := b) (c := c) (d := d) B W ↔
      ∃ A : RootTarget n b c d,
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W =
          sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A := by
  exact sqdiagCPhaseKernelZero_iff_exists_KCAdjointCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d) B W

theorem BW_ZDiff_compat_submodule_le_adjoint_submodule
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) ≤
      sqdiagBWZAdjointSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact sqdiagBWZCompatSubmodule_le_sqdiagBWZAdjointSubmodule
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_support_finrank_decomposition
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagBWZCompatRestrictedMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
      + Module.finrank F (SquareCombinedKernel n a b c d)
      =
    Module.finrank F
      (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  exact finrank_sqdiagBWZCompatRestricted_range_add_SquareCombinedKernel
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_support_finrank_image_inf_decomposition
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (↑(LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
          sqdiagZCompatTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d)))
      + Module.finrank F (SquareCombinedKernel n a b c d)
      =
    Module.finrank F
      (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  exact finrank_sqdiagBWZCompat_image_inf_add_SquareCombinedKernel
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_image_root_projection_injective
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
      (sqdiagBWZCompatImageRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  exact sqdiagBWZCompatImageRootMap_injective
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_image_root_projection_ker_eq_bot
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWZCompatImageRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) = ⊥ := by
  exact sqdiagBWZCompatImageRootMap_ker_eq_bot
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_image_inf_finrank_eq_root_projection_range
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (↑(LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
          sqdiagZCompatTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d)))
      =
    Module.finrank F
      (LinearMap.range
        (sqdiagBWZCompatImageRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  exact finrank_sqdiagBWZCompat_image_inf_eq_root_projection_range
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_image_inf_finrank_le_root_sup_inf
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (↑(LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
          sqdiagZCompatTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d)))
      ≤
    Module.finrank F
      (↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
        ZDiffSpace (n := n) (b := b) (c := c) (d := d))) := by
  exact finrank_sqdiagBWZCompat_image_inf_le_root_sup_inf
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_support_finrank_BW_sup_inf_decomposition
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (↑((LinearMap.range
              (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d)) ⊔
            LinearMap.range
              (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d))) ⊓
          sqdiagZCompatTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d)))
      + Module.finrank F (SquareCombinedKernel n a b c d)
      =
    Module.finrank F
      (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  exact finrank_sqdiagBWZCompat_BW_sup_inf_add_SquareCombinedKernel
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_support_finrank_le_root_sup_inf_add_kernel
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
      Module.finrank F
          (↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
              WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
            ZDiffSpace (n := n) (b := b) (c := c) (d := d))) +
        Module.finrank F (SquareCombinedKernel n a b c d) := by
  exact finrank_sqdiagBWZCompatSubmodule_le_root_sup_inf_add_SquareCombinedKernel
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem BW_ZDiff_compat_support_finrank_add_inf_YZW_le_pair_infs_add_kernel
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d))
      + (n - 1) ^ 3 ≤
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b +
        Module.finrank F (SquareCombinedKernel n a b c d) := by
  exact
    finrank_sqdiagBWZCompatSubmodule_add_inf_YZW_le_pair_infs_add_SquareCombinedKernel
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd

end SquareDiagonal
end Core4loop
