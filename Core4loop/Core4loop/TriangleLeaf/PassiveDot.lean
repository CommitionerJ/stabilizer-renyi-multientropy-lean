import Core4loop.TriangleLeaf.ProfilePair
import Core4loop.TriangleLeaf.PassiveDecomposition

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable def passiveDot {n d : ℕ} [NeZero n]
    (f g : PassiveRaw n d) : F :=
  ∑ w : WVec n d, f w * g w

theorem passiveDot_add_left {n d : ℕ} [NeZero n]
    (f g h : PassiveRaw n d) :
    passiveDot (n := n) (d := d) (f + g) h =
      passiveDot (n := n) (d := d) f h
        + passiveDot (n := n) (d := d) g h := by
  unfold passiveDot
  calc
    (∑ w : WVec n d, (f + g) w * h w)
        = ∑ w : WVec n d, (f w * h w + g w * h w) := by
            refine Finset.sum_congr rfl ?_
            intro w _
            simp only [Pi.add_apply]
            ring
    _ =
        (∑ w : WVec n d, f w * h w)
          + ∑ w : WVec n d, g w * h w := by
          rw [Finset.sum_add_distrib]

theorem passiveDot_add_right {n d : ℕ} [NeZero n]
    (f g h : PassiveRaw n d) :
    passiveDot (n := n) (d := d) f (g + h) =
      passiveDot (n := n) (d := d) f g
        + passiveDot (n := n) (d := d) f h := by
  unfold passiveDot
  calc
    (∑ w : WVec n d, f w * (g + h) w)
        = ∑ w : WVec n d, (f w * g w + f w * h w) := by
            refine Finset.sum_congr rfl ?_
            intro w _
            simp only [Pi.add_apply]
            ring
    _ =
        (∑ w : WVec n d, f w * g w)
          + ∑ w : WVec n d, f w * h w := by
          rw [Finset.sum_add_distrib]

theorem passiveDot_smul_left {n d : ℕ} [NeZero n]
    (r : F) (f g : PassiveRaw n d) :
    passiveDot (n := n) (d := d) (r • f) g =
      r * passiveDot (n := n) (d := d) f g := by
  unfold passiveDot
  simp [Finset.mul_sum, mul_assoc]

theorem passiveDot_smul_right {n d : ℕ} [NeZero n]
    (r : F) (f g : PassiveRaw n d) :
    passiveDot (n := n) (d := d) f (r • g) =
      r * passiveDot (n := n) (d := d) f g := by
  unfold passiveDot
  simp [Finset.mul_sum, mul_left_comm]

theorem passiveDot_add_add {n d : ℕ} [NeZero n]
    (f₀ f₁ g₀ g₁ : PassiveRaw n d) :
    passiveDot (n := n) (d := d) (f₀ + f₁) (g₀ + g₁)
      =
      passiveDot (n := n) (d := d) f₀ g₀
        + passiveDot (n := n) (d := d) f₀ g₁
        + passiveDot (n := n) (d := d) f₁ g₀
        + passiveDot (n := n) (d := d) f₁ g₁ := by
  rw [passiveDot_add_left, passiveDot_add_right, passiveDot_add_right]
  ac_rfl

theorem passiveDot_visibleDiff_symm_apply
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : PassiveVisibleSpace n d hd × ZeroSumProfile n) :
    passiveDot (n := n) (d := d)
        ((passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm X)
        ((passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm Y)
      =
      passiveDot (n := n) (d := d) X.1.1 Y.1.1
        + passiveDot (n := n) (d := d) X.1.1
            (PassiveDiffEmbed (n := n) (d := d) Y.2)
        + passiveDot (n := n) (d := d)
            (PassiveDiffEmbed (n := n) (d := d) X.2) Y.1.1
        + passiveDot (n := n) (d := d)
            (PassiveDiffEmbed (n := n) (d := d) X.2)
            (PassiveDiffEmbed (n := n) (d := d) Y.2) := by
  rw [passiveRawEquivVisibleDiff_symm_apply
      (n := n) (d := d) hd X,
    passiveRawEquivVisibleDiff_symm_apply
      (n := n) (d := d) hd Y]
  rw [passiveDot_add_add]

theorem leafDotProfile_eq_sum_passiveDot
    {n a d : ℕ} [NeZero n]
    (φ ψ : LeafProfile n a d) :
    leafDotProfile (n := n) (a := a) (d := d) φ ψ =
      ∑ p : PVec n a,
        passiveDot (n := n) (d := d) (φ p) (ψ p) := by
  rfl

end

end TriangleLeaf
end Core4loop
