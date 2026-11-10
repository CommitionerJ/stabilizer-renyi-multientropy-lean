import Core4loop.TriangleLeaf.PassiveDecomposition

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafVisibleProfileCoord (n a d : ℕ) [NeZero n] (hd : 0 < d) :=
  PVec n a → PassiveVisibleSpace n d hd

abbrev LeafDiffProfileCoord (n a : ℕ) [NeZero n] :=
  PVec n a → ZeroSumProfile n

noncomputable def leafProfileEquivVisibleDiff
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafProfile n a d ≃ₗ[F]
      LeafVisibleProfileCoord n a d hd × LeafDiffProfileCoord n a where
  toFun φ :=
    (fun p => (passiveRawEquivVisibleDiff (n := n) (d := d) hd (φ p)).1,
      fun p => (passiveRawEquivVisibleDiff (n := n) (d := d) hd (φ p)).2)
  invFun X := fun p =>
    (passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm (X.1 p, X.2 p)
  left_inv φ := by
    funext p
    exact (passiveRawEquivVisibleDiff (n := n) (d := d) hd).left_inv (φ p)
  right_inv X := by
    apply Prod.ext
    · funext p
      exact congrArg Prod.fst
        ((passiveRawEquivVisibleDiff (n := n) (d := d) hd).right_inv (X.1 p, X.2 p))
    · funext p
      exact congrArg Prod.snd
        ((passiveRawEquivVisibleDiff (n := n) (d := d) hd).right_inv (X.1 p, X.2 p))
  map_add' φ ψ := by
    ext p <;> simp
  map_smul' r φ := by
    ext p <;> simp

theorem leafProfileEquivVisibleDiff_apply_fst
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (φ : LeafProfile n a d) (p : PVec n a) :
    (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd φ).1 p =
      passiveVisiblePartToSpace (n := n) (d := d) hd (φ p) := rfl

theorem leafProfileEquivVisibleDiff_apply_snd
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (φ : LeafProfile n a d) (p : PVec n a) :
    (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd φ).2 p =
      passiveRepProfileMap (n := n) (d := d) hd (φ p) := rfl

theorem leafProfileEquivVisibleDiff_symm_apply
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (X : LeafVisibleProfileCoord n a d hd × LeafDiffProfileCoord n a)
    (p : PVec n a) :
    (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd).symm X p =
      (passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm (X.1 p, X.2 p) := rfl

noncomputable def leafVisibleProfileSum
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafVisibleProfileCoord n a d hd →ₗ[F] PassiveVisibleSpace n d hd where
  toFun V := ∑ p : PVec n a, V p
  map_add' V W := by
    rw [← Finset.sum_add_distrib]
    rfl
  map_smul' r V := by
    rw [Finset.smul_sum]
    rfl

theorem leafVisibleProfileSum_apply
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafVisibleProfileCoord n a d hd) :
    leafVisibleProfileSum (n := n) (a := a) (d := d) hd V =
      ∑ p : PVec n a, V p := rfl

end

end TriangleLeaf
end Core4loop
