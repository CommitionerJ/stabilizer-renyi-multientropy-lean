import Core4loop.TriangleLeaf.PassiveSpace

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

abbrev LeafProfile (n a d : ℕ) [NeZero n] :=
  PVec n a → PassiveRaw n d

noncomputable def leafSigmaRaw {n a d : ℕ} [NeZero n] :
    LeafProfile n a d →ₗ[F] PassiveRaw n d where
  toFun φ := fun w => ∑ p : PVec n a, φ p w
  map_add' φ ψ := by
    funext w
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
  map_smul' r φ := by
    funext w
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]

noncomputable def leafSigmaQuot {n a d : ℕ} [NeZero n] :
    LeafProfile n a d →ₗ[F] PassiveQuot n d :=
  ((PassiveDiffSpace n d).mkQ).comp
    (leafSigmaRaw (n := n) (a := a) (d := d))

theorem leafSigmaRaw_single_zeroVec {n a d : ℕ} [NeZero n]
    (f : PassiveRaw n d) :
    leafSigmaRaw (n := n) (a := a) (d := d)
        (fun p : PVec n a => if p = (zeroVec : PVec n a) then f else 0)
      =
      f := by
  funext w
  change (∑ p : PVec n a,
      (if p = (zeroVec : PVec n a) then f else 0) w) = f w
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · simp
  · intro p _ hp
    simp [hp]
  · simp

theorem leafSigmaQuot_surjective {n a d : ℕ} [NeZero n] :
    Function.Surjective (leafSigmaQuot (n := n) (a := a) (d := d)) := by
  intro q
  rcases (PassiveDiffSpace n d).mkQ_surjective q with ⟨f, hf⟩
  refine ⟨fun p : PVec n a => if p = (zeroVec : PVec n a) then f else 0, ?_⟩
  unfold leafSigmaQuot
  rw [LinearMap.comp_apply, leafSigmaRaw_single_zeroVec]
  exact hf

theorem finrank_LeafProfile {n a d : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F (LeafProfile n a d) = n ^ (a + d - 1) := by
  calc
    Module.finrank F (LeafProfile n a d)
        = ∑ _ : PVec n a, Module.finrank F (PassiveRaw n d) := by
            simp [LeafProfile, Module.finrank_pi_fintype
              (R := F) (M := fun _ : PVec n a => PassiveRaw n d)]
    _ = Fintype.card (PVec n a) * n ^ d := by
            rw [finrank_PassiveRaw]
            simp
    _ = n ^ (a + d - 1) := by
            rw [card_vec]
            have hpow : n ^ (a - 1) * n ^ d = n ^ ((a - 1) + d) := by
              rw [← pow_add]
            rw [hpow]
            congr 1
            omega

theorem finrank_ker_leafSigmaQuot_add {n a d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker (leafSigmaQuot (n := n) (a := a) (d := d)))
      + (n ^ d - (n - 1))
      =
      n ^ (a + d - 1) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (leafSigmaQuot (n := n) (a := a) (d := d))
  have hsurj :
      LinearMap.range (leafSigmaQuot (n := n) (a := a) (d := d)) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (leafSigmaQuot_surjective (n := n) (a := a) (d := d))
  rw [hsurj, finrank_top, finrank_PassiveQuot (n := n) (d := d) hd,
    finrank_LeafProfile (n := n) (a := a) (d := d) ha] at hnull
  omega

end TriangleLeaf
end Core4loop
