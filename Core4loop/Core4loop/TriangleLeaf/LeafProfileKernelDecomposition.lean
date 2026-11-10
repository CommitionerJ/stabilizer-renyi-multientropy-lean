import Core4loop.TriangleLeaf.LeafProfileDecomposition

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafVisibleProfileKernel (n a d : ℕ) [NeZero n] (hd : 0 < d) :=
  LinearMap.ker (leafVisibleProfileSum (n := n) (a := a) (d := d) hd)

theorem leafSigmaRaw_eq_sum
    {n a d : ℕ} [NeZero n] (φ : LeafProfile n a d) :
    leafSigmaRaw (n := n) (a := a) (d := d) φ =
      ∑ p : PVec n a, φ p := by
  funext w
  simp [leafSigmaRaw]

theorem passiveVisiblePartToSpace_leafSigmaRaw
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (φ : LeafProfile n a d) :
    passiveVisiblePartToSpace (n := n) (d := d) hd
        (leafSigmaRaw (n := n) (a := a) (d := d) φ)
      =
      leafVisibleProfileSum (n := n) (a := a) (d := d) hd
        ((leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd φ).1) := by
  rw [leafSigmaRaw_eq_sum (n := n) (a := a) (d := d) φ]
  rw [map_sum]
  rfl

theorem leafSigmaRaw_mem_PassiveDiffSpace_iff_visible_sum_eq_zero
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (φ : LeafProfile n a d) :
    leafSigmaRaw (n := n) (a := a) (d := d) φ ∈ PassiveDiffSpace n d
      ↔
      leafVisibleProfileSum (n := n) (a := a) (d := d) hd
        ((leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd φ).1) = 0 := by
  constructor
  · intro hφ
    rw [← passiveVisiblePartToSpace_leafSigmaRaw
      (n := n) (a := a) (d := d) hd φ]
    apply Subtype.ext
    exact
      (passiveVisiblePart_eq_zero_iff_mem_PassiveDiffSpace
        (n := n) (d := d) hd
        (leafSigmaRaw (n := n) (a := a) (d := d) φ)).2 hφ
  · intro hφ
    have hvisible :
        passiveVisiblePartToSpace (n := n) (d := d) hd
            (leafSigmaRaw (n := n) (a := a) (d := d) φ) = 0 := by
      rwa [passiveVisiblePartToSpace_leafSigmaRaw
        (n := n) (a := a) (d := d) hd φ]
    exact
      (passiveVisiblePart_eq_zero_iff_mem_PassiveDiffSpace
        (n := n) (d := d) hd
        (leafSigmaRaw (n := n) (a := a) (d := d) φ)).1
        (congrArg Subtype.val hvisible)

theorem leafSigmaQuot_eq_zero_iff_visible_sum_eq_zero
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (φ : LeafProfile n a d) :
    leafSigmaQuot (n := n) (a := a) (d := d) φ = 0
      ↔
      leafVisibleProfileSum (n := n) (a := a) (d := d) hd
        ((leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd φ).1) = 0 := by
  unfold leafSigmaQuot
  rw [LinearMap.comp_apply]
  change
    Submodule.Quotient.mk (p := PassiveDiffSpace n d)
        (leafSigmaRaw (n := n) (a := a) (d := d) φ) = 0
      ↔
      leafVisibleProfileSum (n := n) (a := a) (d := d) hd
        ((leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd φ).1) = 0
  exact
    (Submodule.Quotient.mk_eq_zero
      (p := PassiveDiffSpace n d)
      (x := leafSigmaRaw (n := n) (a := a) (d := d) φ)).trans
      (leafSigmaRaw_mem_PassiveDiffSpace_iff_visible_sum_eq_zero
        (n := n) (a := a) (d := d) hd φ)

theorem mem_LeafProfileKernel_iff_visible_sum_eq_zero
    {n a d : ℕ} [NeZero n] (hd : 0 < d) (φ : LeafProfile n a d) :
    φ ∈ LeafProfileKernel n a d
      ↔
      leafVisibleProfileSum (n := n) (a := a) (d := d) hd
        ((leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd φ).1) = 0 := by
  rw [LinearMap.mem_ker]
  exact leafSigmaQuot_eq_zero_iff_visible_sum_eq_zero
    (n := n) (a := a) (d := d) hd φ

noncomputable def leafProfileKernelEquivVisibleDiff
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafProfileKernel n a d ≃ₗ[F]
      LeafVisibleProfileKernel n a d hd × LeafDiffProfileCoord n a where
  toFun K :=
    let X := leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd K.1
    (⟨X.1,
      by
        rw [LinearMap.mem_ker]
        exact
          (mem_LeafProfileKernel_iff_visible_sum_eq_zero
            (n := n) (a := a) (d := d) hd K.1).1 K.2⟩,
      X.2)
  invFun X :=
    let φ :=
      (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd).symm
        (X.1.1, X.2)
    ⟨φ,
      by
        apply
          (mem_LeafProfileKernel_iff_visible_sum_eq_zero
            (n := n) (a := a) (d := d) hd φ).2
        have hfst :
            (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd φ).1 =
              X.1.1 :=
          congrArg Prod.fst
            ((leafProfileEquivVisibleDiff
              (n := n) (a := a) (d := d) hd).right_inv (X.1.1, X.2))
        rw [hfst]
        exact LinearMap.mem_ker.mp X.1.2⟩
  left_inv K := by
    apply Subtype.ext
    exact
      (leafProfileEquivVisibleDiff
        (n := n) (a := a) (d := d) hd).left_inv K.1
  right_inv X := by
    apply Prod.ext
    · apply Subtype.ext
      change
        (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd
          ((leafProfileEquivVisibleDiff
            (n := n) (a := a) (d := d) hd).symm (X.1.1, X.2))).1 =
          X.1.1
      exact congrArg Prod.fst
        ((leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd).right_inv (X.1.1, X.2))
    · change
        (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd
          ((leafProfileEquivVisibleDiff
            (n := n) (a := a) (d := d) hd).symm (X.1.1, X.2))).2 =
          X.2
      exact congrArg Prod.snd
        ((leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd).right_inv (X.1.1, X.2))
  map_add' K L := by
    apply Prod.ext
    · apply Subtype.ext
      change
        (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd
          (K.1 + L.1)).1 =
          (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd K.1).1
            + (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd L.1).1
      exact congrArg Prod.fst
        (map_add (leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd) K.1 L.1)
    · change
        (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd
          (K.1 + L.1)).2 =
          (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd K.1).2
            + (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd L.1).2
      exact congrArg Prod.snd
        (map_add (leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd) K.1 L.1)
  map_smul' r K := by
    apply Prod.ext
    · apply Subtype.ext
      change
        (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd
          (r • K.1)).1 =
          r • (leafProfileEquivVisibleDiff
            (n := n) (a := a) (d := d) hd K.1).1
      exact congrArg Prod.fst
        (map_smul (leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd) r K.1)
    · change
        (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd
          (r • K.1)).2 =
          r • (leafProfileEquivVisibleDiff
            (n := n) (a := a) (d := d) hd K.1).2
      exact congrArg Prod.snd
        (map_smul (leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd) r K.1)

theorem leafProfileKernelEquivVisibleDiff_apply_fst
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (K : LeafProfileKernel n a d) :
    ((leafProfileKernelEquivVisibleDiff
      (n := n) (a := a) (d := d) hd K).1 : LeafVisibleProfileCoord n a d hd)
      =
      (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd K.1).1 := rfl

theorem leafProfileKernelEquivVisibleDiff_apply_snd
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (K : LeafProfileKernel n a d) :
    (leafProfileKernelEquivVisibleDiff
      (n := n) (a := a) (d := d) hd K).2
      =
      (leafProfileEquivVisibleDiff (n := n) (a := a) (d := d) hd K.1).2 := rfl

end

end TriangleLeaf
end Core4loop
