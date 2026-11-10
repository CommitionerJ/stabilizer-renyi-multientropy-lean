import Core4loop.TriangleLeaf.E5OneSidedRank

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable def triangleLeafBCFieldSwapEquiv
    {n a b c d : ℕ} [NeZero n] :
    (BFun4 n a c d × CFun4 n a b d) ≃ₗ[F]
      (BFun4 n a b d × CFun4 n a c d) where
  toFun X :=
    (fun p sz y w => X.2 p y sz w,
      fun p z sy w => X.1 p sy z w)
  invFun X :=
    (fun p sy z w => X.2 p z sy w,
      fun p y sz w => X.1 p sz y w)
  left_inv X := by
    apply Prod.ext
    · funext p sy z w
      rfl
    · funext p y sz w
      rfl
  right_inv X := by
    apply Prod.ext
    · funext p sz y w
      rfl
    · funext p z sy w
      rfl
  map_add' X Y := by
    apply Prod.ext
    · funext p sz y w
      rfl
    · funext p z sy w
      rfl
  map_smul' x X := by
    apply Prod.ext
    · funext p sz y w
      rfl
    · funext p z sy w
      rfl

@[simp] theorem triangleLeafBCFieldSwapEquiv_fst
    {n a b c d : ℕ} [NeZero n]
    (X : BFun4 n a c d × CFun4 n a b d)
    (p : PVec n a) (sz : I n) (y : ZVec n b) (w : WVec n d) :
    (triangleLeafBCFieldSwapEquiv X).1 p sz y w =
      X.2 p y sz w :=
  rfl

@[simp] theorem triangleLeafBCFieldSwapEquiv_snd
    {n a b c d : ℕ} [NeZero n]
    (X : BFun4 n a c d × CFun4 n a b d)
    (p : PVec n a) (z : YVec n c) (sy : I n) (w : WVec n d) :
    (triangleLeafBCFieldSwapEquiv X).2 p z sy w =
      X.1 p sy z w :=
  rfl

noncomputable def triangleLeafRootSwapYZEquiv
    {n b c d : ℕ} :
    RootTarget n b c d ≃ₗ[F] RootTarget n c b d where
  toFun f := fun z y w => f y z w
  invFun f := fun y z w => f z y w
  left_inv f := by
    funext y z w
    rfl
  right_inv f := by
    funext z y w
    rfl
  map_add' f g := by
    funext z y w
    rfl
  map_smul' x f := by
    funext z y w
    rfl

theorem triangleLeafRootSwapYZ_KBMap_add_KCMap
    {n a b c d : ℕ} [NeZero n]
    (X : BFun4 n a c d × CFun4 n a b d) :
    triangleLeafRootSwapYZEquiv
        (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) X.1 +
          KCMap (n := n) (a := a) (b := b) (c := c) (d := d) X.2) =
      KBMap (n := n) (a := a) (b := c) (c := b) (d := d)
          (triangleLeafBCFieldSwapEquiv X).1 +
        KCMap (n := n) (a := a) (b := c) (c := b) (d := d)
          (triangleLeafBCFieldSwapEquiv X).2 := by
  funext z y w
  simp only [triangleLeafRootSwapYZEquiv,
    triangleLeafBCFieldSwapEquiv, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
  change
    (∑ p : PVec n a,
        (X.1 p (vecSum y) z w + X.1 p (vecSum y + 1) z w)) +
      (∑ p : PVec n a,
        (X.2 p y (vecSum z) w + X.2 p y (vecSum z + 1) w)) =
    (∑ p : PVec n a,
        (X.2 p y (vecSum z) w + X.2 p y (vecSum z + 1) w)) +
      (∑ p : PVec n a,
        (X.1 p (vecSum y) z w + X.1 p (vecSum y + 1) z w))
  exact add_comm _ _

noncomputable def triangleLeafWCoeffSwapEquiv
    {n b c : ℕ} [NeZero n] :
    WCoeff n b c ≃ₗ[F] WCoeff n c b where
  toFun R := fun z y => R y z
  invFun R := fun y z => R z y
  left_inv R := by
    funext y z
    rfl
  right_inv R := by
    funext z y
    rfl
  map_add' R S := by
    funext z y
    rfl
  map_smul' x R := by
    funext z y
    rfl

theorem triangleLeafRootSwapYZ_WDiffEmbed
    {n b c d : ℕ} [NeZero n]
    (R : WCoeff n b c) :
    triangleLeafRootSwapYZEquiv
        (WDiffEmbed
          (n := n) (b := b) (c := c) (d := d) R) =
      WDiffEmbed
        (n := n) (b := c) (c := b) (d := d)
        (triangleLeafWCoeffSwapEquiv R) :=
  rfl

theorem triangleLeafRootSwapYZ_mem_WDiffSpace
    {n b c d : ℕ} [NeZero n]
    (f : RootTarget n b c d)
    (hf : f ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)) :
    triangleLeafRootSwapYZEquiv f ∈
      WDiffSpace (n := n) (b := c) (c := b) (d := d) := by
  rcases hf with ⟨R, hR⟩
  refine ⟨triangleLeafWCoeffSwapEquiv R, ?_⟩
  calc
    WDiffEmbed
        (n := n) (b := c) (c := b) (d := d)
        (triangleLeafWCoeffSwapEquiv R) =
      triangleLeafRootSwapYZEquiv
        (WDiffEmbed
          (n := n) (b := b) (c := c) (d := d) R) :=
            (triangleLeafRootSwapYZ_WDiffEmbed R).symm
    _ = triangleLeafRootSwapYZEquiv f := by rw [hR]

theorem triangleLeafRootSwapYZ_mem_WDiffSpace_iff
    {n b c d : ℕ} [NeZero n]
    (f : RootTarget n b c d) :
    triangleLeafRootSwapYZEquiv f ∈
        WDiffSpace (n := n) (b := c) (c := b) (d := d) ↔
      f ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  constructor
  · intro hf
    have hback :=
      triangleLeafRootSwapYZ_mem_WDiffSpace
        (n := n) (b := c) (c := b) (d := d)
        (triangleLeafRootSwapYZEquiv f) hf
    simpa [triangleLeafRootSwapYZEquiv] using hback
  · exact triangleLeafRootSwapYZ_mem_WDiffSpace f

noncomputable def triangleLeafWDiffSpaceSwapEquiv
    {n b c d : ℕ} [NeZero n] :
    WDiffSpace (n := n) (b := b) (c := c) (d := d) ≃ₗ[F]
      WDiffSpace (n := n) (b := c) (c := b) (d := d) where
  toFun R :=
    ⟨triangleLeafRootSwapYZEquiv R.1,
      (triangleLeafRootSwapYZ_mem_WDiffSpace_iff R.1).2 R.2⟩
  invFun R :=
    ⟨(triangleLeafRootSwapYZEquiv
        (n := n) (b := b) (c := c) (d := d)).symm R.1, by
      have h :=
        (triangleLeafRootSwapYZ_mem_WDiffSpace_iff
          (n := n) (b := b) (c := c) (d := d)
          ((triangleLeafRootSwapYZEquiv
            (n := n) (b := b) (c := c) (d := d)).symm R.1)).1
      rw [(triangleLeafRootSwapYZEquiv
        (n := n) (b := b) (c := c) (d := d)).apply_symm_apply] at h
      exact h R.2⟩
  left_inv R := by
    apply Subtype.ext
    exact
      (triangleLeafRootSwapYZEquiv
        (n := n) (b := b) (c := c) (d := d)).symm_apply_apply R.1
  right_inv R := by
    apply Subtype.ext
    exact
      (triangleLeafRootSwapYZEquiv
        (n := n) (b := b) (c := c) (d := d)).apply_symm_apply R.1
  map_add' R S := by
    apply Subtype.ext
    rfl
  map_smul' x R := by
    apply Subtype.ext
    rfl

@[simp] theorem triangleLeafBCFieldSwapEquiv_involutive
    {n a b c d : ℕ} [NeZero n]
    (X : BFun4 n a c d × CFun4 n a b d) :
    triangleLeafBCFieldSwapEquiv
        (n := n) (a := a) (b := c) (c := b) (d := d)
        (triangleLeafBCFieldSwapEquiv X) = X := by
  rcases X with ⟨B, C⟩
  rfl

theorem triangleLeafBCFieldSwapEquiv_mem_compatible
    {n a b c d : ℕ} [NeZero n]
    (X : BFun4 n a c d × CFun4 n a b d)
    (hX : X ∈ triangleLeafCompatibleSubmodule n a b c d) :
    triangleLeafBCFieldSwapEquiv X ∈
      triangleLeafCompatibleSubmodule n a c b d := by
  apply (triangleLeafCompatibleSubmodule_carrier_iff
    (n := n) (a := a) (b := c) (c := b) (d := d)
    (triangleLeafBCFieldSwapEquiv X)).mpr
  have hroot :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) X.1 +
          KCMap (n := n) (a := a) (b := b) (c := c) (d := d) X.2
        ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d) :=
    (triangleLeafCompatibleSubmodule_carrier_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) X).mp hX
  have hswap :=
    (triangleLeafRootSwapYZ_mem_WDiffSpace_iff
      (n := n) (b := b) (c := c) (d := d)
      (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) X.1 +
        KCMap (n := n) (a := a) (b := b) (c := c) (d := d) X.2)).2
      hroot
  rw [triangleLeafRootSwapYZ_KBMap_add_KCMap] at hswap
  exact hswap

theorem triangleLeafBCFieldSwapEquiv_mem_compatible_iff
    {n a b c d : ℕ} [NeZero n]
    (X : BFun4 n a c d × CFun4 n a b d) :
    triangleLeafBCFieldSwapEquiv X ∈
        triangleLeafCompatibleSubmodule n a c b d ↔
      X ∈ triangleLeafCompatibleSubmodule n a b c d := by
  constructor
  · intro hX
    have hback :=
      triangleLeafBCFieldSwapEquiv_mem_compatible
        (n := n) (a := a) (b := c) (c := b) (d := d)
        (triangleLeafBCFieldSwapEquiv X) hX
    rw [triangleLeafBCFieldSwapEquiv_involutive] at hback
    exact hback
  · exact triangleLeafBCFieldSwapEquiv_mem_compatible X

noncomputable def triangleLeafCompatibleSwapEquiv
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafCompatibleSubmodule n a b c d ≃ₗ[F]
      triangleLeafCompatibleSubmodule n a c b d where
  toFun X :=
    ⟨triangleLeafBCFieldSwapEquiv X.1,
      triangleLeafBCFieldSwapEquiv_mem_compatible X.1 X.2⟩
  invFun X :=
    ⟨triangleLeafBCFieldSwapEquiv
        (n := n) (a := a) (b := c) (c := b) (d := d) X.1,
      triangleLeafBCFieldSwapEquiv_mem_compatible
        (n := n) (a := a) (b := c) (c := b) (d := d) X.1 X.2⟩
  left_inv X := by
    apply Subtype.ext
    exact triangleLeafBCFieldSwapEquiv_involutive X.1
  right_inv X := by
    apply Subtype.ext
    exact
      triangleLeafBCFieldSwapEquiv_involutive
        (n := n) (a := a) (b := c) (c := b) (d := d) X.1
  map_add' X Y := by
    apply Subtype.ext
    rfl
  map_smul' x X := by
    apply Subtype.ext
    rfl

theorem Q1_triangleLeafBCFieldSwapEquiv
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) :
    Q1
        (n := n) (a := a) (b := c) (c := b) (d := d)
        (triangleLeafBCFieldSwapEquiv (B, C)).1
        (triangleLeafBCFieldSwapEquiv (B, C)).2 =
      Q1
        (n := n) (a := a) (b := b) (c := c) (d := d)
        B C := by
  unfold Q1 betaB gammaB deltaC etaC
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro z _
  refine Finset.sum_congr rfl ?_
  intro w _
  change
    C p y (vecSum z) w * B p (vecSum y) z w +
        C p y (vecSum z + 1) w * B p (vecSum y + 1) z w =
      B p (vecSum y) z w * C p y (vecSum z) w +
        B p (vecSum y + 1) z w * C p y (vecSum z + 1) w
  ring

theorem triangleLeafCompatibleQ_swap
    {n a b c d : ℕ} [NeZero n]
    (X : triangleLeafCompatibleSubmodule n a b c d) :
    triangleLeafCompatibleQ (triangleLeafCompatibleSwapEquiv X) =
      triangleLeafCompatibleQ X := by
  exact Q1_triangleLeafBCFieldSwapEquiv X.1.1 X.1.2

theorem leafCompatibleResidualSum_swap
    {n a b c d : ℕ} [NeZero n] :
    leafCompatibleResidualSum n a b c d =
      leafCompatibleResidualSum n a c b d := by
  rw [leafCompatibleResidualSum_eq_compatibleSubmoduleSignSum,
    leafCompatibleResidualSum_eq_compatibleSubmoduleSignSum]
  change
    (∑ X : triangleLeafCompatibleSubmodule n a b c d,
        bitSign (triangleLeafCompatibleQ X)) =
      ∑ X : triangleLeafCompatibleSubmodule n a c b d,
        bitSign (triangleLeafCompatibleQ X)
  have hsum :=
    (triangleLeafCompatibleSwapEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d)).toEquiv.sum_comp
      (fun X => bitSign (triangleLeafCompatibleQ X))
  calc
    (∑ X : triangleLeafCompatibleSubmodule n a b c d,
        bitSign (triangleLeafCompatibleQ X)) =
      ∑ X : triangleLeafCompatibleSubmodule n a b c d,
        bitSign
          (triangleLeafCompatibleQ
            (triangleLeafCompatibleSwapEquiv
              (n := n) (a := a) (b := b) (c := c) (d := d) X)) := by
                refine Finset.sum_congr rfl ?_
                intro X _
                rw [triangleLeafCompatibleQ_swap]
    _ =
      ∑ X : triangleLeafCompatibleSubmodule n a c b d,
        bitSign (triangleLeafCompatibleQ X) := hsum

theorem ThetaZ_swap_last
    (r s t n : ℕ) :
    ThetaZ r s t n = ThetaZ r t s n := by
  unfold ThetaZ
  by_cases hst : Even n ∧ 2 ≤ r ∧ 2 ≤ s ∧ 2 ≤ t
  · simp [hst]
  · have hts : ¬ (Even n ∧ 2 ≤ r ∧ 2 ≤ t ∧ 2 ≤ s) := by
      intro h
      exact hst ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩
    simp [hst, hts]

theorem CompatibleResidualSplitZ_swap
    (a b c d n : ℕ) :
    CompatibleResidualSplitZ a b c d n =
      CompatibleResidualSplitZ a c b d n := by
  unfold CompatibleResidualSplitZ LeafVisibleUnitZ LeafTailUnitZ
  rw [ThetaZ_swap_last (a + d) b c n]
  ring


end

end TriangleLeaf
end Core4loop
