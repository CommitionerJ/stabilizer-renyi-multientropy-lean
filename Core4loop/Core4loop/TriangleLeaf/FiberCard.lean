import Core4loop.TriangleLeaf.ProfileFibers
import Core4loop.TriangleLeaf.VisibleCard

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable def linearMapFiberEquivKerOfSurjective {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (L : V →ₗ[F] W) (hL : Function.Surjective L) (target : W) :
    {x : V // L x = target} ≃ LinearMap.ker L where
  toFun x :=
    ⟨x.1 - Classical.choose (hL target), by
      rw [LinearMap.mem_ker]
      rw [map_sub, x.2, Classical.choose_spec (hL target)]
      simp⟩
  invFun x :=
    ⟨x.1 + Classical.choose (hL target), by
      rw [map_add, LinearMap.mem_ker.mp x.2, Classical.choose_spec (hL target)]
      simp⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

noncomputable def leafBVisFiberEquivKer {n a c d : ℕ} [NeZero n]
    (V : LeafBVisible n c d) :
    LeafBVisFiber (n := n) (a := a) (c := c) (d := d) V
      ≃
    LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d)) :=
  linearMapFiberEquivKerOfSurjective
    (leafBVisMap (n := n) (a := a) (c := c) (d := d))
    (leafBVisMap_surjective (n := n) (a := a) (c := c) (d := d)) V

noncomputable def leafCVisFiberEquivKer {n a b d : ℕ} [NeZero n]
    (V : LeafCVisible n b d) :
    LeafCVisFiber (n := n) (a := a) (b := b) (d := d) V
      ≃
    LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d)) :=
  linearMapFiberEquivKerOfSurjective
    (leafCVisMap (n := n) (a := a) (b := b) (d := d))
    (leafCVisMap_surjective (n := n) (a := a) (b := b) (d := d)) V

noncomputable instance instFintypeKerLeafBVisMap {n a c d : ℕ} [NeZero n] :
    Fintype
      (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))) := by
  classical
  letI : Finite
      (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))) :=
    Finite.of_injective
      (fun x :
        LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d)) =>
        (x.1 : BFun4 n a c d))
      (fun _ _ h => Subtype.ext h)
  exact Fintype.ofFinite
    (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d)))

noncomputable instance instFintypeKerLeafCVisMap {n a b d : ℕ} [NeZero n] :
    Fintype
      (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d))) := by
  classical
  letI : Finite
      (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d))) :=
    Finite.of_injective
      (fun x :
        LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d)) =>
        (x.1 : CFun4 n a b d))
      (fun _ _ h => Subtype.ext h)
  exact Fintype.ofFinite
    (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d)))

set_option synthInstance.maxHeartbeats 200000 in
-- Kernel submodules are finite function spaces; instance search is deep here.
theorem card_ker_leafBVisMap {n a c d : ℕ} [NeZero n] :
    Fintype.card
        (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d)))
      =
      2 ^ Module.finrank F
        (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))) := by
  rw [← Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

set_option synthInstance.maxHeartbeats 200000 in
-- Kernel submodules are finite function spaces; instance search is deep here.
theorem card_ker_leafCVisMap {n a b d : ℕ} [NeZero n] :
    Fintype.card
        (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d)))
      =
      2 ^ Module.finrank F
        (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d))) := by
  rw [← Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

theorem card_LeafBVisFiber {n a c d : ℕ} [NeZero n]
    (V : LeafBVisible n c d) :
    Fintype.card (LeafBVisFiber (n := n) (a := a) (c := c) (d := d) V)
      =
      2 ^ Module.finrank F
        (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))) := by
  rw [Fintype.card_congr
    (leafBVisFiberEquivKer (n := n) (a := a) (c := c) (d := d) V)]
  exact card_ker_leafBVisMap (n := n) (a := a) (c := c) (d := d)

theorem card_LeafCVisFiber {n a b d : ℕ} [NeZero n]
    (V : LeafCVisible n b d) :
    Fintype.card (LeafCVisFiber (n := n) (a := a) (b := b) (d := d) V)
      =
      2 ^ Module.finrank F
        (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d))) := by
  rw [Fintype.card_congr
    (leafCVisFiberEquivKer (n := n) (a := a) (b := b) (d := d) V)]
  exact card_ker_leafCVisMap (n := n) (a := a) (b := b) (d := d)

theorem card_LeafVisibleFiberPair {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d) :
    Fintype.card
        (LeafVisibleFiberPair (n := n) (a := a) (b := b) (c := c) (d := d) H)
      =
      (2 ^ Module.finrank F
        (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))))
        *
      (2 ^ Module.finrank F
        (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d)))) := by
  rw [Fintype.card_prod]
  rw [card_LeafBVisFiber (n := n) (a := a) (c := c) (d := d) H.1.1]
  rw [card_LeafCVisFiber (n := n) (a := a) (b := b) (d := d) H.1.2]

theorem card_LeafSurvivingSigma_factor {n a b c d : ℕ} [NeZero n] :
    Fintype.card (LeafSurvivingSigma n a b c d)
      =
      Fintype.card (LeafVisibleKernel n b c d)
        *
      ((2 ^ Module.finrank F
        (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))))
        *
      (2 ^ Module.finrank F
        (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d))))) := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ H : LeafVisibleKernel n b c d,
      Fintype.card
        (LeafVisibleFiberPair (n := n) (a := a) (b := b) (c := c) (d := d) H))
        =
        ∑ _ : LeafVisibleKernel n b c d,
          (2 ^ Module.finrank F
            (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))))
            *
          (2 ^ Module.finrank F
            (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d)))) := by
          refine Finset.sum_congr rfl ?_
          intro H _
          exact card_LeafVisibleFiberPair (n := n) (a := a) (b := b) (c := c)
            (d := d) H
    _ =
        Fintype.card (LeafVisibleKernel n b c d)
          *
        ((2 ^ Module.finrank F
          (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))))
          *
        (2 ^ Module.finrank F
          (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d))))) := by
          rw [Finset.sum_const_nat (by intro _ _; rfl)]
          rw [Finset.card_univ]

end

end TriangleLeaf
end Core4loop
