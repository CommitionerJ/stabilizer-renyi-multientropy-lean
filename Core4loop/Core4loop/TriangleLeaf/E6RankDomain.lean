import Core4loop.TriangleLeaf.E5OneSidedQZero
import Core4loop.TriangleLeaf.E6Q1CoeffCore

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Exact compatible-C domain for the TriangleLeaf E6 rank route.

This module records only domain, factorization, range, and generic
exact-sequence identities.  It makes no rank calculation.
-/

noncomputable def triangleLeafCompatibleCProjToRange
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafCompatibleSubmodule n a b c d →ₗ[F]
      triangleLeafCCompat n a b c d :=
  (triangleLeafCompatibleCProj
    (n := n) (a := a) (b := b) (c := c) (d := d)).rangeRestrict

@[simp] theorem triangleLeafCompatibleCProjToRange_apply
    {n a b c d : ℕ} [NeZero n]
    (X : triangleLeafCompatibleSubmodule n a b c d) :
    (triangleLeafCompatibleCProjToRange
      (n := n) (a := a) (b := b) (c := c) (d := d) X).1 =
      X.1.2 :=
  rfl

theorem triangleLeafCompatibleCProjToRange_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (triangleLeafCompatibleCProjToRange
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [← LinearMap.range_eq_top]
  exact LinearMap.range_rangeRestrict _

theorem ker_triangleLeafCompatibleCProjToRange
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (triangleLeafCompatibleCProjToRange
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      triangleLeafBOnly n a b c d := by
  exact LinearMap.ker_rangeRestrict _

set_option synthInstance.maxHeartbeats 1000000 in
-- Nested range/kernel subtypes require additional typeclass normalization.
theorem finrank_triangleLeafCCompat_add_finrank_triangleLeafBOnly
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (triangleLeafCCompat n a b c d) +
        Module.finrank F (triangleLeafBOnly n a b c d) =
      Module.finrank F (triangleLeafCompatibleSubmodule n a b c d) := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafCompatibleCProjToRange
        (n := n) (a := a) (b := b) (c := c) (d := d))
  rw [LinearMap.range_eq_top.mpr
      (triangleLeafCompatibleCProjToRange_surjective
        (n := n) (a := a) (b := b) (c := c) (d := d)),
    finrank_top,
    ker_triangleLeafCompatibleCProjToRange] at h
  exact h

theorem triangleLeafBOnlyPolarMap_eq_coeffCompat_comp
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafBOnlyPolarMap
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (triangleLeafQ1BOnlyCoeffCompat
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (triangleLeafCompatibleCProjToRange
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  apply LinearMap.ext
  intro X
  apply LinearMap.ext
  intro Y
  change
    Q1 X.1.1 Y.1.1.2 + Q1 Y.1.1.1 X.1.2 =
      Q1 Y.1.1.1 X.1.2
  have hY : Y.1.1.2 = 0 := by
    exact LinearMap.mem_ker.mp Y.2
  have hzero : Q1 X.1.1 (0 : CFun4 n a b d) = 0 := by
    unfold Q1 deltaC etaC
    simp
  rw [hY, hzero, zero_add]

theorem range_triangleLeafBOnlyPolarMap_eq_coeffCompat
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (triangleLeafBOnlyPolarMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      LinearMap.range
        (triangleLeafQ1BOnlyCoeffCompat
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [triangleLeafBOnlyPolarMap_eq_coeffCompat_comp]
  apply le_antisymm
  · rintro f ⟨X, rfl⟩
    exact ⟨triangleLeafCompatibleCProjToRange X, rfl⟩
  · rintro f ⟨C, rfl⟩
    rcases triangleLeafCompatibleCProjToRange_surjective C with ⟨X, rfl⟩
    exact ⟨X, rfl⟩

theorem range_restrict_ker_comp_eq_ker
    {K V C D : Type*}
    [DivisionRing K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup C] [Module K C]
    [AddCommGroup D] [Module K D]
    (f : V →ₗ[K] C) (g : C →ₗ[K] D)
    (hf : Function.Surjective f) :
    LinearMap.range
        (f.comp (LinearMap.ker (g.comp f)).subtype) =
      LinearMap.ker g := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact LinearMap.mem_ker.mp x.2
  · intro y hy
    rcases hf y with ⟨x, rfl⟩
    refine ⟨⟨x, ?_⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact LinearMap.mem_ker.mp hy

end

end TriangleLeaf
end Core4loop
