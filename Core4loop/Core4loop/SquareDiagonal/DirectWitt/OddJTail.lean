import Core4loop.SquareDiagonal.DirectWitt.OddOrbit
import Core4loop.ZeroSumSpaces.PointedAugConstNormalForm

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

noncomputable section

local instance (S : Type*) : DecidableEq S := Classical.decEq S

/-!
# The odd pointed-tail twist

For a finite pointed type `(S, s0)`, the odd source and dual normal forms
have the same scalar coordinate but different tail coordinates.  On the
full pointed-tail function space, the change of tail coordinates is

`J(u)(t) = u(t) + ∑ v, u(v)`.

When `Fintype.card S` is odd, the tail has even cardinality and `J` is an
involution.  This file proves that elementary finite-dimensional statement,
the resulting symmetric nondegenerate twisted dot product, and the exact
source-to-dual coordinate bridge.
-/

/-- The explicit change from odd source-tail coordinates to dual-tail
coordinates.  The domain is the full pointed-tail function space. -/
noncomputable def oddTailJ
    (S : Type*) [Fintype S] (s0 : S) :
    (PointedTail S s0 → F) →ₗ[F] (PointedTail S s0 → F) where
  toFun u := fun t => u t + ∑ v, u v
  map_add' u v := by
    funext t
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    abel
  map_smul' r u := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

@[simp] theorem oddTailJ_apply
    (S : Type*) [Fintype S] (s0 : S)
    (u : PointedTail S s0 → F) (t : PointedTail S s0) :
    oddTailJ S s0 u t = u t + ∑ v, u v := rfl

/-- Removing the distinguished point from an odd finite type leaves an
even-cardinality tail. -/
theorem oddTail_card_even
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) :
    Even (Fintype.card (PointedTail S s0)) := by
  rcases hodd with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [card_pointedTail, hk]
  omega

private theorem oddTail_sum_const_zero
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (x : F) :
    (∑ _ : PointedTail S s0, x) = 0 := by
  rcases oddTail_card_even s0 hodd with ⟨k, hk⟩
  rw [Finset.sum_const, Finset.card_univ, hk]
  rw [add_nsmul, F_add_self]

private theorem oddTailJ_sum
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S))
    (u : PointedTail S s0 → F) :
    (∑ t, oddTailJ S s0 u t) = ∑ t, u t := by
  simp only [oddTailJ_apply]
  rw [Finset.sum_add_distrib, oddTail_sum_const_zero s0 hodd, add_zero]

/-- On an odd-cardinality source, the pointed-tail twist is its own
inverse.  This includes the cardinality-one case, where the tail is empty. -/
@[simp] theorem oddTailJ_sq_apply
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S))
    (u : PointedTail S s0 → F) :
    oddTailJ S s0 (oddTailJ S s0 u) = u := by
  funext t
  rw [oddTailJ_apply, oddTailJ_apply, oddTailJ_sum s0 hodd,
    add_assoc, F_add_self, add_zero]

/-- The explicit pointed-tail equivalence whose forward and inverse maps
are both `oddTailJ`. -/
noncomputable def oddTailJEquiv
    (S : Type*) [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) :
    (PointedTail S s0 → F) ≃ₗ[F]
      (PointedTail S s0 → F) where
  toLinearMap := oddTailJ S s0
  invFun := oddTailJ S s0
  left_inv := oddTailJ_sq_apply s0 hodd
  right_inv := oddTailJ_sq_apply s0 hodd

/-- The ordinary tail dot product with the second argument transported by
the source-to-dual twist. -/
noncomputable def oddTailTwistedDot
    (S : Type*) [Fintype S] (s0 : S)
    (u v : PointedTail S s0 → F) : F :=
  ∑ t, u t * oddTailJ S s0 v t

private theorem oddTailJ_pairing
    {S : Type*} [Fintype S] (s0 : S)
    (u v : PointedTail S s0 → F) :
    (∑ t, oddTailJ S s0 u t * v t) =
      ∑ t, u t * oddTailJ S s0 v t := by
  simp only [oddTailJ_apply, add_mul, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]

/-- The `J`-twisted dot product is symmetric for every finite tail; no
parity hypothesis is needed for this finite-sum identity. -/
theorem oddTailTwistedDot_comm
    (S : Type*) [Fintype S] (s0 : S)
    (u v : PointedTail S s0 → F) :
    oddTailTwistedDot S s0 u v =
      oddTailTwistedDot S s0 v u := by
  rw [oddTailTwistedDot, oddTailTwistedDot]
  calc
    (∑ t, u t * oddTailJ S s0 v t) =
        ∑ t, oddTailJ S s0 u t * v t :=
      (oddTailJ_pairing s0 u v).symm
    _ = ∑ t, v t * oddTailJ S s0 u t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [mul_comm]

/-- For an odd-cardinality source, the twisted tail pairing has trivial
left radical.  Coordinate probes are transported through the explicit
involution. -/
theorem oddTailTwistedDot_nondegenerate
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S))
    (u : PointedTail S s0 → F)
    (hu : ∀ v, oddTailTwistedDot S s0 u v = 0) :
    u = 0 := by
  funext t
  have ht :=
    hu (oddTailJ S s0
      (Pi.single t (1 : F) : PointedTail S s0 → F))
  rw [oddTailTwistedDot, oddTailJ_sq_apply s0 hodd] at ht
  rw [Finset.sum_eq_single t] at ht
  · simpa using ht
  · intro v _ hvt
    rw [Pi.single_eq_of_ne hvt]
    simp
  · simp

/-- The exact direction of the odd coordinate change:
source tail, followed by `J`, is the dual tail. -/
theorem pointedDualOdd_tail_eq_oddTailJ_source
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (g : S → F) :
    (pointedDualOddEquiv S s0 hodd g).2 =
      oddTailJ S s0 (pointedSrcOddEquiv S s0 hodd g).2 := by
  let x := pointedSrcOddEquiv S s0 hodd g
  have hg : g = (pointedSrcOddEquiv S s0 hodd).symm x := by
    exact ((pointedSrcOddEquiv S s0 hodd).symm_apply_apply g).symm
  rw [hg]
  funext t
  rw [pointedDualOddEquiv_apply_snd, oddTailJ_apply]
  simp only [LinearEquiv.apply_symm_apply]
  simp only [pointedSrcOddEquiv]
  change
    pointedSrcOddBuild S s0 x t.1 +
        pointedSrcOddBuild S s0 x s0 =
      x.2 t + ∑ v, x.2 v
  rw [pointedSrcOddBuild_at_tail, pointedSrcOddBuild_at_point]
  calc
    x.2 t + x.1 + (x.1 + ∑ v, x.2 v) =
        x.2 t + (x.1 + x.1) + ∑ v, x.2 v := by
      abel
    _ = x.2 t + ∑ v, x.2 v := by
      rw [F_add_self, add_zero]

/-- The reverse coordinate identity follows from the same twist only after
using its odd-cardinality involutivity. -/
theorem pointedSrcOdd_tail_eq_oddTailJ_dual
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (g : S → F) :
    (pointedSrcOddEquiv S s0 hodd g).2 =
      oddTailJ S s0 (pointedDualOddEquiv S s0 hodd g).2 := by
  rw [pointedDualOdd_tail_eq_oddTailJ_source s0 hodd g,
    oddTailJ_sq_apply s0 hodd]

/-- The production pointwise pairing written entirely in odd source
coordinates.  Its tail term is genuinely `J`-twisted. -/
theorem pointedOdd_pairing_source_J
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (f g : S → F) :
    (∑ s, f s * g s) =
      (pointedSrcOddEquiv S s0 hodd f).1 *
          (pointedSrcOddEquiv S s0 hodd g).1 +
        oddTailTwistedDot S s0
          (pointedSrcOddEquiv S s0 hodd f).2
          (pointedSrcOddEquiv S s0 hodd g).2 := by
  rw [pointedOdd_pairing s0 hodd]
  simp only [pointedDualOddEquiv_apply_fst,
    pointedSrcOddEquiv_apply_fst]
  rw [pointedDualOdd_tail_eq_oddTailJ_source s0 hodd g]
  rfl

end

end Core4loop.SquareDiagonal.DirectWitt
