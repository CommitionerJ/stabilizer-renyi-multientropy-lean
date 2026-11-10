import Core4loop.SquareDiagonal.BWQuadraticMetabolic
import Core4loop.SquareDiagonal.BWReducedRelation
import Core4loop.SquareDiagonal.KCAdjointRank
import Core4loop.SquareDiagonal.SurvivorEval

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

theorem sqdiagCKernelCardZ_eq_pow_finrank
    {n a b c d : ℕ} [NeZero n] :
    sqdiagCKernelCardZ
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (2 : ℤ) ^
        Module.finrank F
          (LinearMap.ker
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  unfold sqdiagCKernelCardZ
  have hnat :
      Fintype.card
          (LinearMap.ker
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        2 ^
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) := by
    rw [← Nat.card_eq_fintype_card]
    rw [Module.natCard_eq_pow_finrank (K := F)]
    simp [F]
  exact_mod_cast hnat

theorem sqdiagKCAdjointKernelCardZ_eq_pow_finrank
    {n a b c d : ℕ} [NeZero n] :
    sqdiagKCAdjointKernelCardZ
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (2 : ℤ) ^
        Module.finrank F
          (LinearMap.ker
            (sqdiagKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  unfold sqdiagKCAdjointKernelCardZ
  have hnat :
      Fintype.card
          (LinearMap.ker
            (sqdiagKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
        2 ^
          Module.finrank F
            (LinearMap.ker
              (sqdiagKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d))) := by
    rw [← Nat.card_eq_fintype_card]
    rw [Module.natCard_eq_pow_finrank (K := F)]
    simp [F]
  exact_mod_cast hnat

set_option synthInstance.maxHeartbeats 200000 in
-- The lagrangian is a nested kernel subtype, so the standard cardinality theorem needs more instance budget.
theorem natCard_sqdiagBWAAdjointGraphLagrangian_eq_pow_finrank
    {n a b c d : ℕ} [NeZero n] :
    (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      (2 : ℤ) ^
        Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) := by
  have hnat :
      Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) =
        2 ^ Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    simp [F]
  exact_mod_cast hnat

theorem lagrangian_weighted_card_of_finrank_lagrangian_add_CFun4
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  have hker :=
    finrank_ker_KCMap_add_rootTarget_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc
  have hsum :
      Module.finrank F
          (LinearMap.ker
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
        Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) =
      Module.finrank F
          (LinearMap.ker
            (sqdiagKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) +
        Int.toNat (X3AfterAZ a b c d n) := by
    omega
  rw [sqdiagCKernelCardZ_eq_pow_finrank
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  rw [sqdiagKCAdjointKernelCardZ_eq_pow_finrank
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  rw [natCard_sqdiagBWAAdjointGraphLagrangian_eq_pow_finrank
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  rw [← pow_add, ← pow_add, hsum]

set_option synthInstance.maxHeartbeats 200000 in
-- The reduced vertical-orthogonal module is a nested kernel subtype.
theorem finrank_lagrangian_add_CFun4_of_reducedRelationVerticalOrthogonal_add_squareKernel_KC
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hredfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
        n ^ (a + b + d) =
      Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d) := by
  have hlag :=
    finrank_sqdiagBWAAdjointGraphLagrangian_eq_reducedRelationVerticalOrthogonal_add_kernels
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hker :=
    finrank_ker_KCMap_add_rootTarget_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc
  omega

set_option synthInstance.maxHeartbeats 200000 in
-- The clean lagrangian finrank target also implies the reduced rank target.
theorem reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank_of_lagrangian_add_CFun4
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hfin :
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) :
    Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        Module.finrank F (SquareCombinedKernel n a b c d) +
        Module.finrank F
          (LinearMap.ker
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Int.toNat (X3AfterAZ a b c d n) := by
  have hlag :=
    finrank_sqdiagBWAAdjointGraphLagrangian_eq_reducedRelationVerticalOrthogonal_add_kernels
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hker :=
    finrank_ker_KCMap_add_rootTarget_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc
  omega

set_option synthInstance.maxHeartbeats 200000 in
-- The clean lagrangian and reduced rank targets are equivalent.
theorem finrank_lagrangian_add_CFun4_iff_reducedRelationVerticalOrthogonal_add_squareKernel_KC
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) :
    (Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) +
          n ^ (a + b + d) =
        Int.toNat (X3AfterAZ a b c d n) + n ^ (b + c + d)) ↔
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n) := by
  constructor
  · exact
      reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank_of_lagrangian_add_CFun4
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc
  · exact
      finrank_lagrangian_add_CFun4_of_reducedRelationVerticalOrthogonal_add_squareKernel_KC
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hc

set_option synthInstance.maxHeartbeats 200000 in
-- This wrapper reuses the same reduced vertical-orthogonal finrank statement.
theorem lagrangian_weighted_card_of_reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c)
    (hredfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) :=
  lagrangian_weighted_card_of_finrank_lagrangian_add_CFun4
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hc
    (finrank_lagrangian_add_CFun4_of_reducedRelationVerticalOrthogonal_add_squareKernel_KC
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hc hredfin)

set_option synthInstance.maxHeartbeats 200000 in
-- Converts the pair-presentation vertical-orthogonal rank target to the reduced rank target.
theorem reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank_of_pairPresentation
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hpairfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        Module.finrank F (SquareCombinedKernel n a b c d) +
        Module.finrank F
          (LinearMap.ker
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Int.toNat (X3AfterAZ a b c d n) := by
  have horth :=
    finrank_sqdiagAdjointPairPresentationVerticalOrthogonal_eq_reducedRelationVerticalOrthogonal_add_intersection
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hI :=
    finrank_SquareBWIntersection_add_core
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd
  omega

set_option synthInstance.maxHeartbeats 200000 in
-- Converts the reduced rank target back to the pair-presentation rank target.
theorem pairPresentationVerticalOrthogonal_add_squareKernel_KC_finrank_of_reducedRelation
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hredfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n)) :
    Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
        Module.finrank F (SquareCombinedKernel n a b c d) +
        Module.finrank F
          (LinearMap.ker
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
        2 * (n - 1) ^ 3 =
      Int.toNat (X3AfterAZ a b c d n) +
        ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1)) := by
  have horth :=
    finrank_sqdiagAdjointPairPresentationVerticalOrthogonal_eq_reducedRelationVerticalOrthogonal_add_intersection
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hI :=
    finrank_SquareBWIntersection_add_core
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd
  omega

set_option synthInstance.maxHeartbeats 200000 in
-- The reduced and pair-presentation rank targets are equivalent.
theorem pairPresentationVerticalOrthogonal_add_squareKernel_KC_finrank_iff_reducedRelation
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) ↔
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Int.toNat (X3AfterAZ a b c d n) := by
  constructor
  · exact
      reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank_of_pairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd
  · exact
      pairPresentationVerticalOrthogonal_add_squareKernel_KC_finrank_of_reducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd

set_option synthInstance.maxHeartbeats 200000 in
-- Pair-presentation rank certificate form of the weighted-cardinality identity.
theorem lagrangian_weighted_card_of_pairPresentationVerticalOrthogonal_finrank
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hpairfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
          Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d))) +
          2 * (n - 1) ^ 3 =
        Int.toNat (X3AfterAZ a b c d n) +
          ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1))) :
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) :=
  lagrangian_weighted_card_of_reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hc
    (reducedRelationVerticalOrthogonal_add_squareKernel_KC_finrank_of_pairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd hpairfin)

theorem sqdiagBWAAdjointGraphRootSignSum_weighted_eval_of_Q_zero_of_lagrangian_weighted_card
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
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
    sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      (2 : ℤ) ^ Int.toNat (X3AfterAZ a b c d n) := by
  rw [sqdiagBWAAdjointGraphRootSignSum_eq_lagrangian_card_of_Q_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hQzero]
  exact hcard

end

end SquareDiagonal
end Core4loop
