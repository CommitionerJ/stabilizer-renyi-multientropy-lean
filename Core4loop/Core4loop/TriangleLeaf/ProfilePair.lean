import Core4loop.TriangleLeaf.VisibleCompat

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

private lemma sum_p_y_z_w_comm
    {P Y Z W : Type*} [Fintype P] [Fintype Y] [Fintype Z] [Fintype W]
    (f : P → Y → Z → W → F) :
    (∑ p : P, ∑ y : Y, ∑ z : Z, ∑ w : W, f p y z w)
      =
    ∑ y : Y, ∑ z : Z, ∑ p : P, ∑ w : W, f p y z w := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Finset.sum_comm]

noncomputable def leafDotProfile {n a d : ℕ} [NeZero n]
    (φ ψ : LeafProfile n a d) : F :=
  ∑ p : PVec n a, ∑ w : WVec n d, φ p w * ψ p w

theorem leafDotProfile_add_left {n a d : ℕ} [NeZero n]
    (φ ψ χ : LeafProfile n a d) :
    leafDotProfile (φ + ψ) χ =
      leafDotProfile φ χ + leafDotProfile ψ χ := by
  unfold leafDotProfile
  calc
    (∑ p : PVec n a, ∑ w : WVec n d, (φ + ψ) p w * χ p w)
        =
        ∑ p : PVec n a, ∑ w : WVec n d,
          (φ p w * χ p w + ψ p w * χ p w) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro w _
          simp only [Pi.add_apply]
          ring
    _ =
        (∑ p : PVec n a, ∑ w : WVec n d, φ p w * χ p w)
          + ∑ p : PVec n a, ∑ w : WVec n d, ψ p w * χ p w := by
          simp_rw [Finset.sum_add_distrib]

theorem leafDotProfile_add_right {n a d : ℕ} [NeZero n]
    (φ ψ χ : LeafProfile n a d) :
    leafDotProfile φ (ψ + χ) =
      leafDotProfile φ ψ + leafDotProfile φ χ := by
  unfold leafDotProfile
  calc
    (∑ p : PVec n a, ∑ w : WVec n d, φ p w * (ψ + χ) p w)
        =
        ∑ p : PVec n a, ∑ w : WVec n d,
          (φ p w * ψ p w + φ p w * χ p w) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro w _
          simp only [Pi.add_apply]
          ring
    _ =
        (∑ p : PVec n a, ∑ w : WVec n d, φ p w * ψ p w)
          + ∑ p : PVec n a, ∑ w : WVec n d, φ p w * χ p w := by
          simp_rw [Finset.sum_add_distrib]

theorem leafDotProfile_smul_left {n a d : ℕ} [NeZero n]
    (r : F) (φ ψ : LeafProfile n a d) :
    leafDotProfile (r • φ) ψ = r * leafDotProfile φ ψ := by
  unfold leafDotProfile
  simp [Finset.mul_sum, mul_assoc]

theorem leafDotProfile_smul_right {n a d : ℕ} [NeZero n]
    (r : F) (φ ψ : LeafProfile n a d) :
    leafDotProfile φ (r • ψ) = r * leafDotProfile φ ψ := by
  unfold leafDotProfile
  simp [Finset.mul_sum, mul_left_comm]

noncomputable def qLeafLeft {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) : F :=
  ∑ y : YVec n b, ∑ z : ZVec n c,
    leafDotProfile
      (leafBProfile B (vecSum y) z)
      (leafCProfile C y (vecSum z))

noncomputable def qLeafRight {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) : F :=
  ∑ y : YVec n b, ∑ z : ZVec n c,
    leafDotProfile
      (leafBProfile B (vecSum y + 1) z)
      (leafCProfile C y (vecSum z + 1))

noncomputable def qLeafProfile {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) : F :=
  qLeafLeft B C + qLeafRight B C

theorem Q1_eq_qLeafProfile {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) :
    Q1 B C =
      qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) B C := by
  unfold Q1 qLeafProfile qLeafLeft qLeafRight leafDotProfile
    leafBProfile leafCProfile betaB gammaB deltaC etaC
  simp_rw [Finset.sum_add_distrib]
  rw [sum_p_y_z_w_comm
    (P := PVec n a) (Y := YVec n b) (Z := ZVec n c) (W := WVec n d)
    (f := fun p y z w => B p (vecSum y) z w * C p y (vecSum z) w)]
  rw [sum_p_y_z_w_comm
    (P := PVec n a) (Y := YVec n b) (Z := ZVec n c) (W := WVec n d)
    (f := fun p y z w => B p (vecSum y + 1) z w * C p y (vecSum z + 1) w)]

end TriangleLeaf
end Core4loop
