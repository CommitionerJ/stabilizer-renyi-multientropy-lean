import Core4loop.TriangleLeaf.E6SecondQuotientCore
import Core4loop.TriangleLeaf.E6ThetaQuotient

/-!
# Triangle+leaf E6 second-quotient S2 certificate

This file proves the p-constant lift that annihilates the second quotient
image.  It is a logical-level 5 structural certificate.  It proves no
second-rank, residual signed-sum, raw `Delta`, support, `Gamma`, catalogue,
Diamond, K4, or Core5 theorem.
-/

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable abbrev triangleLeafE6PSumTarget
    (n d : ℕ) [NeZero n] :=
  WVec n d → LineZeroSum n

noncomputable def triangleLeafE6PSum
    {n a d : ℕ} [NeZero n] :
    BDiagCoeff n a d →ₗ[F] triangleLeafE6PSumTarget n d where
  toFun U := fun w => ∑ p : PVec n a, U p w
  map_add' U V := by
    funext w
    change (∑ p : PVec n a, (U p w + V p w)) =
      (∑ p : PVec n a, U p w) + ∑ p : PVec n a, V p w
    exact Finset.sum_add_distrib
  map_smul' r U := by
    funext w
    change (∑ p : PVec n a, r • U p w) =
      r • ∑ p : PVec n a, U p w
    rw [Finset.smul_sum]

noncomputable def triangleLeafE6PConcentrate
    {n a d : ℕ} [NeZero n] (p0 : PVec n a) :
    triangleLeafE6PSumTarget n d →ₗ[F] BDiagCoeff n a d where
  toFun V := fun p w => if p = p0 then V w else 0
  map_add' V W := by
    funext p w
    by_cases hp : p = p0 <;> simp [hp]
  map_smul' r V := by
    funext p w
    by_cases hp : p = p0 <;> simp [hp]

theorem triangleLeafE6PSum_concentrate
    {n a d : ℕ} [NeZero n] (p0 : PVec n a)
    (V : triangleLeafE6PSumTarget n d) :
    triangleLeafE6PSum (triangleLeafE6PConcentrate p0 V) = V := by
  funext w
  change (∑ p : PVec n a, if p = p0 then V w else 0) = V w
  rw [Finset.sum_eq_single p0]
  · simp
  · intro p _ hp
    simp [hp]
  · simp

theorem ker_triangleLeafE6PSum_le_ker_BDiagCurl
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    LinearMap.ker
        (triangleLeafE6PSum (n := n) (a := a) (d := d)) ≤
      LinearMap.ker
        (triangleLeafE6BDiagCurl
          (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  intro U hU
  apply LinearMap.mem_ker.mpr
  funext w
  apply Subtype.ext
  funext x t
  rw [triangleLeafE6BDiagCurl_pointwise]
  rw [Finset.sum_add_distrib]
  have hSum := LinearMap.mem_ker.mp hU
  have hw : triangleLeafE6PSum U w = 0 := congrFun hSum w
  change (∑ p : PVec n a, U p w) = 0 at hw
  have hval := congrArg Subtype.val hw
  simp only [Submodule.coe_sum, Submodule.coe_zero] at hval
  have h1 := congrFun (congrFun hval (t - x)) t
  have h2 := congrFun (congrFun hval (t - x + 1)) (t + 1)
  simp only [Finset.sum_apply, Pi.zero_apply] at h1 h2
  rw [h1, h2]
  simp

theorem ker_triangleLeafE6PSum_le_ker_theta
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    LinearMap.ker
        (triangleLeafE6PSum (n := n) (a := a) (d := d)) ≤
      LinearMap.ker
        (triangleLeafE6Theta
          (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  intro U hU
  apply LinearMap.mem_ker.mpr
  change Submodule.Quotient.mk
    (triangleLeafE6BDiagCurl
      (n := n) (a := a) (b := b) (c := c) (d := d) hb U) = 0
  rw [LinearMap.mem_ker.mp
    (ker_triangleLeafE6PSum_le_ker_BDiagCurl hb hU)]
  exact Submodule.Quotient.mk_zero _

theorem triangleLeafE6K1_eq_of_PSum_eq
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (k : triangleLeafE6K1 n a b c d)
    {U V : BDiagCoeff n a d}
    (hUV : triangleLeafE6PSum U = triangleLeafE6PSum V) :
    k.1 U = k.1 V := by
  have hSum :
      U + V ∈ LinearMap.ker
        (triangleLeafE6PSum (n := n) (a := a) (d := d)) := by
    apply LinearMap.mem_ker.mpr
    rw [LinearMap.map_add, hUV]
    funext w
    apply Subtype.ext
    funext s t
    exact F_add_self _
  have hTheta :
      U + V ∈ LinearMap.ker
        (triangleLeafE6Theta
          (n := n) (a := a) (b := b) (c := c) (d := d) hb) :=
    ker_triangleLeafE6PSum_le_ker_theta hb hSum
  have hRange :
      U + V ∈ LinearMap.range
        (triangleLeafBOnlyBDiagMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    rw [← ker_triangleLeafE6Theta_eq_range_BOnlyBDiag hb hc hd]
    exact hTheta
  rcases hRange with ⟨Y, hY⟩
  have hkRestrict :=
    congrArg
      (fun ell :
          Module.Dual F (triangleLeafBOnly n a b c d) => ell Y)
      (LinearMap.mem_ker.mp k.2)
  have hkRange :
      k.1
          (triangleLeafBOnlyBDiagMap
            (n := n) (a := a) (b := b) (c := c) (d := d) Y) =
        0 := by
    exact hkRestrict
  have hkAdd : k.1 U + k.1 V = 0 := by
    rw [← k.1.map_add, ← hY]
    exact hkRange
  calc
    k.1 U = k.1 U + (k.1 V + k.1 V) := by
      rw [F_add_self, add_zero]
    _ = (k.1 U + k.1 V) + k.1 V := by
      ac_rfl
    _ = k.1 V := by rw [hkAdd, zero_add]

noncomputable def triangleLeafE6AlphaSection
    {n a b d : ℕ} [NeZero n] (hb : 0 < b) :
    Module.Dual F (BDiagCoeff n a d) →ₗ[F] CFun4 n a b d := by
  letI : Module.Free F (Module.Dual F (BDiagCoeff n a d)) :=
    Module.Free.of_divisionRing F _
  exact
    Classical.choose
      ((triangleLeafBDiagAlpha
          (n := n) (a := a) (b := b) (d := d)).exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (triangleLeafBDiagAlpha_surjective
            (n := n) (a := a) (b := b) (d := d) hb)))

theorem triangleLeafE6Alpha_section
    {n a b d : ℕ} [NeZero n] (hb : 0 < b)
    (k : Module.Dual F (BDiagCoeff n a d)) :
    triangleLeafBDiagAlpha (triangleLeafE6AlphaSection hb k) = k := by
  letI : Module.Free F (Module.Dual F (BDiagCoeff n a d)) :=
    Module.Free.of_divisionRing F _
  unfold triangleLeafE6AlphaSection
  let e :=
    (triangleLeafBDiagAlpha
        (n := n) (a := a) (b := b) (d := d)).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (triangleLeafBDiagAlpha_surjective
          (n := n) (a := a) (b := b) (d := d) hb))
  change
    ((triangleLeafBDiagAlpha
        (n := n) (a := a) (b := b) (d := d)).comp
      (Classical.choose e)) k = k
  have hright := Classical.choose_spec e
  rw [hright]
  rfl

noncomputable def triangleLeafE6PSliceReplicate
    {n a b d : ℕ} [NeZero n] (p0 : PVec n a) :
    CFun4 n a b d →ₗ[F] CFun4 n a b d where
  toFun C := fun _ y r w => C p0 y r w
  map_add' C D := by
    funext p y r w
    change (C + D) p0 y r w = C p0 y r w + D p0 y r w
    rfl
  map_smul' x C := by
    funext p y r w
    change (x • C) p0 y r w = x • C p0 y r w
    rfl

private theorem triangleLeafBDiagAlpha_raw
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (U : BDiagCoeff n a d) :
    triangleLeafBDiagAlpha C U =
      ∑ p : PVec n a, ∑ y : YVec n b, ∑ r : I n, ∑ w : WVec n d,
        C p y r w * (U p w).1 (vecSum y) (vecSum y + r) := by
  rw [triangleLeafBDiagAlpha_apply]
  unfold coeffApply
  simp_rw [Fintype.sum_prod_type]
  rfl

theorem triangleLeafBDiagAlpha_PSliceReplicate
    {n a b d : ℕ} [NeZero n]
    (p0 : PVec n a) (C : CFun4 n a b d)
    (U : BDiagCoeff n a d) :
    triangleLeafBDiagAlpha
        (triangleLeafE6PSliceReplicate p0 C) U =
      triangleLeafBDiagAlpha C
        (triangleLeafE6PConcentrate p0 (triangleLeafE6PSum U)) := by
  calc
    triangleLeafBDiagAlpha
          (triangleLeafE6PSliceReplicate p0 C) U =
        ∑ p : PVec n a, ∑ y : YVec n b, ∑ r : I n, ∑ w : WVec n d,
          C p0 y r w * (U p w).1 (vecSum y) (vecSum y + r) := by
            rw [triangleLeafBDiagAlpha_raw]
            rfl
    _ = ∑ y : YVec n b, ∑ p : PVec n a, ∑ r : I n, ∑ w : WVec n d,
          C p0 y r w * (U p w).1 (vecSum y) (vecSum y + r) := by
            exact Finset.sum_comm
    _ = ∑ y : YVec n b, ∑ r : I n, ∑ p : PVec n a, ∑ w : WVec n d,
          C p0 y r w * (U p w).1 (vecSum y) (vecSum y + r) := by
            refine Finset.sum_congr rfl ?_
            intro y _
            exact Finset.sum_comm
    _ = ∑ y : YVec n b, ∑ r : I n, ∑ w : WVec n d, ∑ p : PVec n a,
          C p0 y r w * (U p w).1 (vecSum y) (vecSum y + r) := by
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro r _
            exact Finset.sum_comm
    _ = triangleLeafBDiagAlpha C
          (triangleLeafE6PConcentrate p0 (triangleLeafE6PSum U)) := by
            rw [triangleLeafBDiagAlpha_raw]
            simp only [triangleLeafE6PConcentrate, triangleLeafE6PSum,
              LinearMap.coe_mk, AddHom.coe_mk]
            symm
            rw [Finset.sum_eq_single p0]
            · simp only [if_pos, Submodule.coe_sum, Finset.sum_apply]
              refine Finset.sum_congr rfl ?_
              intro y _
              refine Finset.sum_congr rfl ?_
              intro r _
              refine Finset.sum_congr rfl ?_
              intro w _
              rw [Finset.mul_sum]
            · intro p _ hp
              simp [hp]
            · simp

noncomputable def triangleLeafE6K1PConstantLift
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    triangleLeafE6K1 n a b c d →ₗ[F] CFun4 n a b d :=
  (triangleLeafE6PSliceReplicate
      (zeroVec : PVec n a)).comp
    ((triangleLeafE6AlphaSection
        (n := n) (a := a) (b := b) (d := d) hb).comp
      (triangleLeafE6K1 n a b c d).subtype)

theorem triangleLeafBDiagAlpha_K1PConstantLift
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (k : triangleLeafE6K1 n a b c d) :
    triangleLeafBDiagAlpha
        (triangleLeafE6K1PConstantLift hb k) = k.1 := by
  apply LinearMap.ext
  intro U
  change
    triangleLeafBDiagAlpha
        (triangleLeafE6PSliceReplicate
          (zeroVec : PVec n a)
          (triangleLeafE6AlphaSection hb k.1)) U =
      k.1 U
  rw [triangleLeafBDiagAlpha_PSliceReplicate]
  rw [triangleLeafE6Alpha_section]
  exact
    triangleLeafE6K1_eq_of_PSum_eq hb hc hd k
      (triangleLeafE6PSum_concentrate
        (zeroVec : PVec n a) (triangleLeafE6PSum U))

theorem triangleLeafE6K1PConstantLift_apply_p
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (k : triangleLeafE6K1 n a b c d)
    (p q : PVec n a) (y : YVec n b) (r : I n) (w : WVec n d) :
    triangleLeafE6K1PConstantLift hb k p y r w =
      triangleLeafE6K1PConstantLift hb k q y r w :=
  rfl

theorem triangleLeafKCMap_PSliceReplicate
    {n a b c d : ℕ} [NeZero n]
    (p0 : PVec n a) (C : CFun4 n a b d)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    KCMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (triangleLeafE6PSliceReplicate p0 C) y z w =
      (Fintype.card (PVec n a) : F) *
        (C p0 y (vecSum z) w + C p0 y (vecSum z + 1) w) := by
  simp [KCMap, triangleLeafE6PSliceReplicate, dzC, deltaC, etaC,
    Finset.sum_const, nsmul_eq_mul]
  ring

theorem triangleLeafKCMap_K1PConstantLift_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (k : triangleLeafE6K1 n a b c d) :
    KCMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (triangleLeafE6K1PConstantLift hb k) = 0 := by
  have hcard : (Fintype.card (PVec n a) : F) = 0 := by
    exact
      natCast_card_vec_eq_zero_of_even_pos
        (n := n) (k := a - 1) hn (by omega)
  funext y z w
  change
    KCMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (triangleLeafE6PSliceReplicate
          (zeroVec : PVec n a)
          (triangleLeafE6AlphaSection hb k.1)) y z w =
      0
  rw [triangleLeafKCMap_PSliceReplicate, hcard, zero_mul]

theorem triangleLeafE6Obstruction_K1PConstantLift_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (_hc : 0 < c) (_hd : 0 < d)
    (k : triangleLeafE6K1 n a b c d) :
    triangleLeafE6Obstruction
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (triangleLeafE6K1PConstantLift hb k) = 0 := by
  change
    Submodule.Quotient.mk
      (KCMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (triangleLeafE6K1PConstantLift hb k)) = 0
  rw [triangleLeafKCMap_K1PConstantLift_eq_zero hn ha2 hb k]
  exact Submodule.Quotient.mk_zero _

theorem triangleLeafE6BarO_eq_zero_on_K1
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (k : triangleLeafE6K1 n a b c d) :
    triangleLeafE6BarO
        (n := n) (a := a) (b := b) (c := c) (d := d) hb k.1 =
      0 := by
  let C :=
    triangleLeafE6K1PConstantLift
      (n := n) (a := a) (b := b) (c := c) (d := d) hb k
  have hAlpha :
      triangleLeafBDiagAlpha
          (n := n) (a := a) (b := b) (d := d) C =
        k.1 := by
    exact triangleLeafBDiagAlpha_K1PConstantLift hb hc hd k
  have hObstruction :
      triangleLeafE6Obstruction
          (n := n) (a := a) (b := b) (c := c) (d := d) C =
        0 := by
    exact
      triangleLeafE6Obstruction_K1PConstantLift_eq_zero
        hn ha2 hb hc hd k
  calc
    triangleLeafE6BarO hb k.1 =
        triangleLeafE6BarO hb
          (triangleLeafBDiagAlpha
            (n := n) (a := a) (b := b) (d := d) C) := by
              rw [hAlpha]
    _ = rangeQuotientMap
          (triangleLeafE6Obstruction
            (n := n) (a := a) (b := b) (c := c) (d := d))
          (triangleLeafE6K0 n a b d) C := by
            exact triangleLeafE6BarO_apply_alpha hb C
    _ = 0 := by
      apply LinearMap.mem_ker.mp
      rw [ker_rangeQuotientMap]
      exact
        (le_sup_right :
          LinearMap.ker
              (triangleLeafE6Obstruction
                (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
            triangleLeafE6K0 n a b d ⊔
              LinearMap.ker
                (triangleLeafE6Obstruction
                  (n := n) (a := a) (b := b) (c := c) (d := d)))
          (LinearMap.mem_ker.mpr hObstruction)

theorem map_triangleLeafE6BarO_K1_eq_bot
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Submodule.map
        (triangleLeafE6BarO
          (n := n) (a := a) (b := b) (c := c) (d := d) hb)
        (triangleLeafE6K1 n a b c d) =
      ⊥ := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨k, hk, rfl⟩
    have hzero :=
      triangleLeafE6BarO_eq_zero_on_K1
        hn ha2 hb hc hd
        (⟨k, hk⟩ : triangleLeafE6K1 n a b c d)
    rw [hzero]
    exact Submodule.zero_mem _
  · exact bot_le

end

end TriangleLeaf
end Core4loop
