import Core4loop.TriangleLeaf.CompatibleSourceCore

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Neutral compatible-C domain and Q1 coefficient maps for the TriangleLeaf E6 route.

This owner contains only compatible-source and coefficient-map declarations.
-/

abbrev triangleLeafCCompat
    (n a b c d : ℕ) [NeZero n] :=
  LinearMap.range
    (triangleLeafCompatibleCProj
      (n := n) (a := a) (b := b) (c := c) (d := d))

theorem mem_triangleLeafCCompat_iff_exists_compatibleB
    {n a b c d : ℕ} [NeZero n]
    (C : CFun4 n a b d) :
    C ∈ triangleLeafCCompat n a b c d ↔
      ∃ B : BFun4 n a c d,
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B +
            KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
          ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  constructor
  · rintro ⟨X, hX⟩
    have hC : X.1.2 = C := by
      simpa [triangleLeafCompatibleCProj] using hX
    refine ⟨X.1.1, ?_⟩
    rw [← hC]
    exact
      (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) X.1).mp X.2
  · rintro ⟨B, hBC⟩
    let X : triangleLeafCompatibleSubmodule n a b c d :=
      ⟨(B, C),
        (triangleLeafCompatibleSubmodule_carrier_iff
          (n := n) (a := a) (b := b) (c := c) (d := d) (B, C)).mpr hBC⟩
    refine ⟨X, ?_⟩
    rfl

theorem mem_triangleLeafCCompat_iff_KCMap_mem_sup
    {n a b c d : ℕ} [NeZero n]
    (C : CFun4 n a b d) :
    C ∈ triangleLeafCCompat n a b c d ↔
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C ∈
        YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rw [mem_triangleLeafCCompat_iff_exists_compatibleB]
  constructor
  · rintro ⟨B, hBC⟩
    have hKB :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B ∈
          YDiffSpace (n := n) (b := b) (c := c) (d := d) := by
      rw [← range_KBMap_eq_YDiffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d)]
      exact ⟨B, rfl⟩
    have hnegKB :
        -KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B ∈
          YDiffSpace (n := n) (b := b) (c := c) (d := d) :=
      (YDiffSpace (n := n) (b := b) (c := c) (d := d)).neg_mem hKB
    have hsum :
        -KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B +
            (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B +
              KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C)
          ∈ YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
              WDiffSpace (n := n) (b := b) (c := c) (d := d) :=
      Submodule.add_mem_sup hnegKB hBC
    simpa only [neg_add_cancel_left] using hsum
  · intro hC
    rcases Submodule.mem_sup.mp hC with ⟨y, hy, w, hw, hyw⟩
    have hnegy :
        -y ∈ YDiffSpace (n := n) (b := b) (c := c) (d := d) :=
      (YDiffSpace (n := n) (b := b) (c := c) (d := d)).neg_mem hy
    rw [← range_KBMap_eq_YDiffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)] at hnegy
    rcases hnegy with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    have hEq :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B +
            KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C =
          w := by
      rw [hB, ← hyw]
      abel
    rw [hEq]
    exact hw

noncomputable def triangleLeafQ1BOnlyCoeffAll
    {n a b c d : ℕ} [NeZero n] :
    CFun4 n a b d →ₗ[F] (triangleLeafBOnly n a b c d →ₗ[F] F) where
  toFun C :=
    { toFun := fun Y => Q1 Y.1.1.1 C
      map_add' := fun Y Z => by
        change Q1 (Y.1.1.1 + Z.1.1.1) C =
          Q1 Y.1.1.1 C + Q1 Z.1.1.1 C
        unfold Q1 betaB gammaB deltaC etaC
        simp only [Pi.add_apply]
        simp_rw [add_mul, Finset.sum_add_distrib]
        abel
      map_smul' := fun x Y => by
        change Q1 (x • Y.1.1.1) C = x • Q1 Y.1.1.1 C
        unfold Q1 betaB gammaB deltaC etaC
        simp only [Pi.smul_apply, smul_eq_mul]
        simp only [mul_assoc, mul_add, Finset.mul_sum] }
  map_add' C D := by
    ext Y
    change Q1 Y.1.1.1 (C + D) = Q1 Y.1.1.1 C + Q1 Y.1.1.1 D
    unfold Q1 betaB gammaB deltaC etaC
    simp only [Pi.add_apply]
    simp_rw [mul_add, Finset.sum_add_distrib]
    abel
  map_smul' x C := by
    ext Y
    change Q1 Y.1.1.1 (x • C) = x • Q1 Y.1.1.1 C
    unfold Q1 betaB gammaB deltaC etaC
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [mul_left_comm, mul_add, Finset.mul_sum]

noncomputable def triangleLeafQ1BOnlyCoeffCompat
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafCCompat n a b c d →ₗ[F]
      (triangleLeafBOnly n a b c d →ₗ[F] F) :=
  (triangleLeafQ1BOnlyCoeffAll
    (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (triangleLeafCCompat n a b c d).subtype

theorem range_triangleLeafQ1BOnlyCoeffCompat_eq_map
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (triangleLeafQ1BOnlyCoeffCompat
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      Submodule.map
        (triangleLeafQ1BOnlyCoeffAll
          (n := n) (a := a) (b := b) (c := c) (d := d))
        (triangleLeafCCompat n a b c d) := by
  ext f
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨C.1, C.2, rfl⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨⟨C, hC⟩, rfl⟩

theorem range_triangleLeafQ1BOnlyCoeffCompat_le_all
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (triangleLeafQ1BOnlyCoeffCompat
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
      LinearMap.range
        (triangleLeafQ1BOnlyCoeffAll
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rintro f ⟨C, rfl⟩
  exact ⟨C.1, rfl⟩

end

end TriangleLeaf
end Core4loop
