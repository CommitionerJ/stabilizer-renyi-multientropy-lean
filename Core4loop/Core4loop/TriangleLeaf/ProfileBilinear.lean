import Core4loop.TriangleLeaf.ProfileKernelCoords

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

lemma qLeafLeft_add_left {n a b c d : ℕ} [NeZero n]
    (B₁ B₂ : BFun4 n a c d) (C : CFun4 n a b d) :
    qLeafLeft (n := n) (a := a) (b := b) (c := c) (d := d) (B₁ + B₂) C =
      qLeafLeft (n := n) (a := a) (b := b) (c := c) (d := d) B₁ C
        + qLeafLeft (n := n) (a := a) (b := b) (c := c) (d := d) B₂ C := by
  unfold qLeafLeft
  calc
    (∑ y : YVec n b, ∑ z : ZVec n c,
        leafDotProfile (leafBProfile (B₁ + B₂) (vecSum y) z)
          (leafCProfile C y (vecSum z)))
      =
        ∑ y : YVec n b, ∑ z : ZVec n c,
          (leafDotProfile (leafBProfile B₁ (vecSum y) z)
              (leafCProfile C y (vecSum z))
            + leafDotProfile (leafBProfile B₂ (vecSum y) z)
              (leafCProfile C y (vecSum z))) := by
          refine Finset.sum_congr rfl ?_
          intro y _
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [show leafBProfile (B₁ + B₂) (vecSum y) z =
            leafBProfile B₁ (vecSum y) z + leafBProfile B₂ (vecSum y) z by rfl]
          rw [leafDotProfile_add_left]
    _ = (∑ y : YVec n b, ∑ z : ZVec n c,
          leafDotProfile (leafBProfile B₁ (vecSum y) z)
            (leafCProfile C y (vecSum z)))
        + ∑ y : YVec n b, ∑ z : ZVec n c,
          leafDotProfile (leafBProfile B₂ (vecSum y) z)
            (leafCProfile C y (vecSum z)) := by
          simp_rw [Finset.sum_add_distrib]

lemma qLeafLeft_add_right {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C₁ C₂ : CFun4 n a b d) :
    qLeafLeft (n := n) (a := a) (b := b) (c := c) (d := d) B (C₁ + C₂) =
      qLeafLeft (n := n) (a := a) (b := b) (c := c) (d := d) B C₁
        + qLeafLeft (n := n) (a := a) (b := b) (c := c) (d := d) B C₂ := by
  unfold qLeafLeft
  calc
    (∑ y : YVec n b, ∑ z : ZVec n c,
        leafDotProfile (leafBProfile B (vecSum y) z)
          (leafCProfile (C₁ + C₂) y (vecSum z)))
      =
        ∑ y : YVec n b, ∑ z : ZVec n c,
          (leafDotProfile (leafBProfile B (vecSum y) z)
              (leafCProfile C₁ y (vecSum z))
            + leafDotProfile (leafBProfile B (vecSum y) z)
              (leafCProfile C₂ y (vecSum z))) := by
          refine Finset.sum_congr rfl ?_
          intro y _
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [show leafCProfile (C₁ + C₂) y (vecSum z) =
            leafCProfile C₁ y (vecSum z) + leafCProfile C₂ y (vecSum z) by rfl]
          rw [leafDotProfile_add_right]
    _ = (∑ y : YVec n b, ∑ z : ZVec n c,
          leafDotProfile (leafBProfile B (vecSum y) z)
            (leafCProfile C₁ y (vecSum z)))
        + ∑ y : YVec n b, ∑ z : ZVec n c,
          leafDotProfile (leafBProfile B (vecSum y) z)
            (leafCProfile C₂ y (vecSum z)) := by
          simp_rw [Finset.sum_add_distrib]

lemma qLeafRight_add_left {n a b c d : ℕ} [NeZero n]
    (B₁ B₂ : BFun4 n a c d) (C : CFun4 n a b d) :
    qLeafRight (n := n) (a := a) (b := b) (c := c) (d := d) (B₁ + B₂) C =
      qLeafRight (n := n) (a := a) (b := b) (c := c) (d := d) B₁ C
        + qLeafRight (n := n) (a := a) (b := b) (c := c) (d := d) B₂ C := by
  unfold qLeafRight
  calc
    (∑ y : YVec n b, ∑ z : ZVec n c,
        leafDotProfile (leafBProfile (B₁ + B₂) (vecSum y + 1) z)
          (leafCProfile C y (vecSum z + 1)))
      =
        ∑ y : YVec n b, ∑ z : ZVec n c,
          (leafDotProfile (leafBProfile B₁ (vecSum y + 1) z)
              (leafCProfile C y (vecSum z + 1))
            + leafDotProfile (leafBProfile B₂ (vecSum y + 1) z)
              (leafCProfile C y (vecSum z + 1))) := by
          refine Finset.sum_congr rfl ?_
          intro y _
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [show leafBProfile (B₁ + B₂) (vecSum y + 1) z =
            leafBProfile B₁ (vecSum y + 1) z
              + leafBProfile B₂ (vecSum y + 1) z by rfl]
          rw [leafDotProfile_add_left]
    _ = (∑ y : YVec n b, ∑ z : ZVec n c,
          leafDotProfile (leafBProfile B₁ (vecSum y + 1) z)
            (leafCProfile C y (vecSum z + 1)))
        + ∑ y : YVec n b, ∑ z : ZVec n c,
          leafDotProfile (leafBProfile B₂ (vecSum y + 1) z)
            (leafCProfile C y (vecSum z + 1)) := by
          simp_rw [Finset.sum_add_distrib]

lemma qLeafRight_add_right {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C₁ C₂ : CFun4 n a b d) :
    qLeafRight (n := n) (a := a) (b := b) (c := c) (d := d) B (C₁ + C₂) =
      qLeafRight (n := n) (a := a) (b := b) (c := c) (d := d) B C₁
        + qLeafRight (n := n) (a := a) (b := b) (c := c) (d := d) B C₂ := by
  unfold qLeafRight
  calc
    (∑ y : YVec n b, ∑ z : ZVec n c,
        leafDotProfile (leafBProfile B (vecSum y + 1) z)
          (leafCProfile (C₁ + C₂) y (vecSum z + 1)))
      =
        ∑ y : YVec n b, ∑ z : ZVec n c,
          (leafDotProfile (leafBProfile B (vecSum y + 1) z)
              (leafCProfile C₁ y (vecSum z + 1))
            + leafDotProfile (leafBProfile B (vecSum y + 1) z)
              (leafCProfile C₂ y (vecSum z + 1))) := by
          refine Finset.sum_congr rfl ?_
          intro y _
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [show leafCProfile (C₁ + C₂) y (vecSum z + 1) =
            leafCProfile C₁ y (vecSum z + 1)
              + leafCProfile C₂ y (vecSum z + 1) by rfl]
          rw [leafDotProfile_add_right]
    _ = (∑ y : YVec n b, ∑ z : ZVec n c,
          leafDotProfile (leafBProfile B (vecSum y + 1) z)
            (leafCProfile C₁ y (vecSum z + 1)))
        + ∑ y : YVec n b, ∑ z : ZVec n c,
          leafDotProfile (leafBProfile B (vecSum y + 1) z)
            (leafCProfile C₂ y (vecSum z + 1)) := by
          simp_rw [Finset.sum_add_distrib]

lemma qLeafProfile_add_left {n a b c d : ℕ} [NeZero n]
    (B₁ B₂ : BFun4 n a c d) (C : CFun4 n a b d) :
    qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) (B₁ + B₂) C =
      qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) B₁ C
        + qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) B₂ C := by
  unfold qLeafProfile
  rw [qLeafLeft_add_left, qLeafRight_add_left]
  ac_rfl

lemma qLeafProfile_add_right {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C₁ C₂ : CFun4 n a b d) :
    qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) B (C₁ + C₂) =
      qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) B C₁
        + qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) B C₂ := by
  unfold qLeafProfile
  rw [qLeafLeft_add_right, qLeafRight_add_right]
  ac_rfl

lemma qLeafProfile_add_add {n a b c d : ℕ} [NeZero n]
    (B₀ B₁ : BFun4 n a c d) (C₀ C₁ : CFun4 n a b d) :
    qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d)
        (B₀ + B₁) (C₀ + C₁)
      =
      qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) B₀ C₀
        + qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) B₀ C₁
        + qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) B₁ C₀
        + qLeafProfile (n := n) (a := a) (b := b) (c := c) (d := d) B₁ C₁ := by
  rw [qLeafProfile_add_left, qLeafProfile_add_right, qLeafProfile_add_right]
  ac_rfl

end

end TriangleLeaf
end Core4loop
