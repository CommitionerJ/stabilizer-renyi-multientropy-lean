import Core4loop.TriangleLeaf.E6ShearedCoeffCore
import Core4loop.TriangleLeaf.E6SecondQuotientCore

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Coordinate certificate for the common kernel of the TriangleLeaf E6
coefficient maps.

The proof deliberately tests the ambient `LineZeroSum` coefficient domain
with a genuine two-position pulse.  It does not assert that the dot pairing
restricted to `LineZeroSum` is nondegenerate (that assertion is false in
characteristic two).
-/

private theorem triangleLeafE6Alpha_raw
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (U : BDiagCoeff n a d) :
    triangleLeafBDiagAlpha C U =
      ∑ p : PVec n a, ∑ y : YVec n b, ∑ r : I n, ∑ w : WVec n d,
        C p y r w * (U p w).1 (vecSum y) (vecSum y + r) := by
  rw [triangleLeafBDiagAlpha_apply]
  unfold coeffApply
  simp_rw [Fintype.sum_prod_type]
  rfl

private theorem triangleLeafE6Alpha_fiber_pair
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (U : BDiagCoeff n a d)
    (p : PVec n a) (w : WVec n d) (u : I n) :
    (∑ y : YVec n b,
      C p y (u - vecSum y) w * (U p w).1 (vecSum y) u) =
      ∑ s : I n,
        triangleLeafE6CFiber C p s (u - s) w * (U p w).1 s u := by
  classical
  symm
  unfold triangleLeafE6CFiber
  calc
    (∑ s : I n,
      (∑ y : YVec n b,
        if vecSum y = s then C p y (u - s) w else 0) *
          (U p w).1 s u) =
      ∑ s : I n, ∑ y : YVec n b,
        (if vecSum y = s then C p y (u - s) w else 0) *
          (U p w).1 s u := by
      refine Finset.sum_congr rfl ?_
      intro s _
      rw [Finset.sum_mul]
    _ = ∑ y : YVec n b, ∑ s : I n,
        (if vecSum y = s then C p y (u - s) w else 0) *
          (U p w).1 s u := by
      exact Finset.sum_comm
    _ = ∑ y : YVec n b,
        C p y (u - vecSum y) w * (U p w).1 (vecSum y) u := by
      refine Finset.sum_congr rfl ?_
      intro y _
      rw [Finset.sum_eq_single (vecSum y)]
      · simp
      · intro s _ hs
        simp [hs.symm]
      · simp

private theorem triangleLeafE6Alpha_pair_block
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (U : BDiagCoeff n a d)
    (p : PVec n a) (w : WVec n d) :
    (∑ y : YVec n b, ∑ r : I n,
      C p y r w * (U p w).1 (vecSum y) (vecSum y + r)) =
      ∑ u : I n, ∑ s : I n,
        triangleLeafE6CFiber C p s (u - s) w * (U p w).1 s u := by
  calc
    (∑ y : YVec n b, ∑ r : I n,
      C p y r w * (U p w).1 (vecSum y) (vecSum y + r)) =
      ∑ y : YVec n b, ∑ u : I n,
        C p y (u - vecSum y) w * (U p w).1 (vecSum y) u := by
      refine Finset.sum_congr rfl ?_
      intro y _
      simpa using Equiv.sum_comp (Equiv.addLeft (vecSum y))
        (fun u : I n =>
          C p y (u - vecSum y) w * (U p w).1 (vecSum y) u)
    _ = ∑ u : I n, ∑ y : YVec n b,
        C p y (u - vecSum y) w * (U p w).1 (vecSum y) u := by
      exact Finset.sum_comm
    _ = ∑ u : I n, ∑ s : I n,
        triangleLeafE6CFiber C p s (u - s) w * (U p w).1 s u := by
      refine Finset.sum_congr rfl ?_
      intro u _
      exact triangleLeafE6Alpha_fiber_pair C U p w u

theorem triangleLeafE6Alpha_fiber_pairing
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (U : BDiagCoeff n a d) :
    triangleLeafBDiagAlpha C U =
      ∑ p : PVec n a, ∑ w : WVec n d, ∑ u : I n, ∑ s : I n,
        triangleLeafE6CFiber C p s (u - s) w * (U p w).1 s u := by
  rw [triangleLeafE6Alpha_raw]
  refine Finset.sum_congr rfl ?_
  intro p _
  calc
    (∑ y : YVec n b, ∑ r : I n, ∑ w : WVec n d,
      C p y r w * (U p w).1 (vecSum y) (vecSum y + r)) =
      ∑ y : YVec n b, ∑ w : WVec n d, ∑ r : I n,
        C p y r w * (U p w).1 (vecSum y) (vecSum y + r) := by
      refine Finset.sum_congr rfl ?_
      intro y _
      exact Finset.sum_comm
    _ = ∑ w : WVec n d, ∑ y : YVec n b, ∑ r : I n,
        C p y r w * (U p w).1 (vecSum y) (vecSum y + r) := by
      exact Finset.sum_comm
    _ = ∑ w : WVec n d, ∑ u : I n, ∑ s : I n,
        triangleLeafE6CFiber C p s (u - s) w * (U p w).1 s u := by
      refine Finset.sum_congr rfl ?_
      intro w _
      exact triangleLeafE6Alpha_pair_block C U p w

noncomputable def triangleLeafE6LinePairPulse
    {n : ℕ} [NeZero n] (s t u : I n) :
    LineZeroSum n :=
  ⟨fun q v =>
      if v = u then
        (if q = s then 1 else 0) + if q = t then 1 else 0
      else 0,
    by
      apply LinearMap.mem_ker.mpr
      unfold sigmaMapM
      funext v
      by_cases hv : v = u
      · subst hv
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
          Pi.zero_apply, if_pos]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_pos]
        exact F_add_self 1
      · simp [hv]⟩

noncomputable def triangleLeafE6BDiagPairPulse
    {n a d : ℕ} [NeZero n]
    (p0 : PVec n a) (w0 : WVec n d) (s t u : I n) :
    BDiagCoeff n a d :=
  fun p w =>
    if p = p0 then
      if w = w0 then triangleLeafE6LinePairPulse s t u else 0
    else 0

theorem triangleLeafE6Alpha_BDiagPairPulse
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d)
    (p0 : PVec n a) (w0 : WVec n d) (s t u : I n) :
    triangleLeafBDiagAlpha C
        (triangleLeafE6BDiagPairPulse p0 w0 s t u) =
      triangleLeafE6CFiber C p0 s (u - s) w0 +
        triangleLeafE6CFiber C p0 t (u - t) w0 := by
  classical
  rw [triangleLeafE6Alpha_fiber_pairing]
  rw [Finset.sum_eq_single p0]
  · rw [Finset.sum_eq_single w0]
    · rw [Finset.sum_eq_single u]
      · unfold triangleLeafE6BDiagPairPulse triangleLeafE6LinePairPulse
        simp only [if_pos, mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_eq_single s]
          · simp
          · intro q _ hq
            simp [hq]
          · simp
        · rw [Finset.sum_eq_single t]
          · simp
          · intro q _ hq
            simp [hq]
          · simp
      · intro v _ hv
        unfold triangleLeafE6BDiagPairPulse triangleLeafE6LinePairPulse
        simp [hv]
      · simp
    · intro w _ hw
      unfold triangleLeafE6BDiagPairPulse
      simp [hw]
    · simp
  · intro p _ hp
    unfold triangleLeafE6BDiagPairPulse
    simp [hp]
  · simp

theorem ker_triangleLeafBDiagAlpha_le_ker_triangleLeafE6Aback
    {n a b d : ℕ} [NeZero n] :
    LinearMap.ker
        (triangleLeafBDiagAlpha
          (n := n) (a := a) (b := b) (d := d)) ≤
      LinearMap.ker
        (triangleLeafE6Aback
          (n := n) (a := a) (b := b) (d := d)) := by
  intro C hC
  apply LinearMap.mem_ker.mpr
  funext p w
  apply Subtype.ext
  funext s u
  rw [triangleLeafE6Aback_apply]
  have hAlpha :
      triangleLeafBDiagAlpha
          (n := n) (a := a) (b := b) (d := d) C = 0 :=
    LinearMap.mem_ker.mp hC
  have hPulse :=
    LinearMap.congr_fun hAlpha
      (triangleLeafE6BDiagPairPulse p w s (s - 1) u)
  rw [triangleLeafE6Alpha_BDiagPairPulse] at hPulse
  have hcoord : u - (s - 1) = u - s + 1 := by abel
  simpa [hcoord] using hPulse

private theorem triangleLeafE6Aback_zero_fiber_constant
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d)
    (hA :
      triangleLeafE6Aback
          (n := n) (a := a) (b := b) (d := d) C = 0)
    (p : PVec n a) (w : WVec n d) (u : I n) :
    ∀ s : I n,
      triangleLeafE6CFiber C p s (u - s) w =
        triangleLeafE6CFiber C p 0 u w := by
  let f : I n → F :=
    fun s => triangleLeafE6CFiber C p s (u - s) w
  have hdiff : cycDiff (n := n) F f = 0 := by
    funext s
    have hs :=
      congrFun
        (congrFun
          (congrArg Subtype.val
            (congrFun (congrFun hA p) w))
          (s + 1)) u
    rw [triangleLeafE6Aback_apply] at hs
    simp only [Pi.zero_apply] at hs
    have hs1 : s + 1 - 1 = s := by abel
    have hu1 : u - (s + 1) + 1 = u - s := by abel
    rw [hs1, hu1] at hs
    change f s + f (s + 1) = 0
    simpa [f, add_comm] using hs
  simpa [f] using
    (cycDiff_eq_zero_iff_constant_apply F f).mp hdiff

theorem ker_triangleLeafE6Aback_le_ker_triangleLeafBDiagAlpha
    {n a b d : ℕ} [NeZero n] :
    LinearMap.ker
        (triangleLeafE6Aback
          (n := n) (a := a) (b := b) (d := d)) ≤
      LinearMap.ker
        (triangleLeafBDiagAlpha
          (n := n) (a := a) (b := b) (d := d)) := by
  intro C hC
  have hA :
      triangleLeafE6Aback
          (n := n) (a := a) (b := b) (d := d) C = 0 :=
    LinearMap.mem_ker.mp hC
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro U
  rw [triangleLeafE6Alpha_fiber_pairing]
  refine Finset.sum_eq_zero ?_
  intro p _
  refine Finset.sum_eq_zero ?_
  intro w _
  refine Finset.sum_eq_zero ?_
  intro u _
  have hconst :=
    triangleLeafE6Aback_zero_fiber_constant C hA p w u
  have hsum :
      ∑ s : I n, (U p w).1 s u = 0 := by
    have h := LinearMap.mem_ker.mp (U p w).2
    unfold sigmaMapM at h
    have hu := congrFun h u
    simpa only [LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
      Finset.sum_apply] using hu
  calc
    (∑ s : I n,
      triangleLeafE6CFiber C p s (u - s) w * (U p w).1 s u) =
        ∑ s : I n,
          triangleLeafE6CFiber C p 0 u w * (U p w).1 s u := by
      refine Finset.sum_congr rfl ?_
      intro s _
      rw [hconst s]
    _ = triangleLeafE6CFiber C p 0 u w *
        ∑ s : I n, (U p w).1 s u := by
      rw [Finset.mul_sum]
    _ = 0 := by rw [hsum, mul_zero]

theorem ker_triangleLeafE6Aback_eq_ker_triangleLeafBDiagAlpha
    {n a b d : ℕ} [NeZero n] :
    LinearMap.ker
        (triangleLeafE6Aback
          (n := n) (a := a) (b := b) (d := d)) =
      LinearMap.ker
        (triangleLeafBDiagAlpha
          (n := n) (a := a) (b := b) (d := d)) :=
  le_antisymm
    ker_triangleLeafE6Aback_le_ker_triangleLeafBDiagAlpha
    ker_triangleLeafBDiagAlpha_le_ker_triangleLeafE6Aback

theorem ker_triangleLeafE6AlphaShearCoeff_eq_ker_triangleLeafE6Aback
    {n a b d : ℕ} [NeZero n] :
    LinearMap.ker
        (triangleLeafE6AlphaShearCoeff
          (n := n) (a := a) (b := b) (d := d)) =
      LinearMap.ker
        (triangleLeafE6Aback
          (n := n) (a := a) (b := b) (d := d)) := by
  ext C
  constructor
  · intro hC
    apply LinearMap.mem_ker.mpr
    have hE := LinearMap.mem_ker.mp hC
    change triangleLeafE6DiagShear (triangleLeafE6Aback C) = 0 at hE
    have h := congrArg
      (triangleLeafE6DiagShear (n := n) (a := a) (d := d)) hE
    simpa [triangleLeafE6DiagShear_involutive] using h
  · intro hC
    apply LinearMap.mem_ker.mpr
    have hA := LinearMap.mem_ker.mp hC
    change triangleLeafE6DiagShear (triangleLeafE6Aback C) = 0
    rw [hA]
    exact
      (triangleLeafE6DiagShear
        (n := n) (a := a) (d := d)).map_zero

theorem ker_triangleLeafE6AlphaShearCoeff_eq_K0
    {n a b d : ℕ} [NeZero n] :
    LinearMap.ker
        (triangleLeafE6AlphaShearCoeff
          (n := n) (a := a) (b := b) (d := d)) =
      triangleLeafE6K0 n a b d := by
  rw [ker_triangleLeafE6AlphaShearCoeff_eq_ker_triangleLeafE6Aback,
    ker_triangleLeafE6Aback_eq_ker_triangleLeafBDiagAlpha]

private noncomputable def triangleLeafE6AbackSectionValue
    {n a b d : ℕ} [NeZero n] (hb : 0 < b)
    (U : BDiagCoeff n a d)
    (p : PVec n a) (y : YVec n b) (r : I n) (w : WVec n d) : F :=
  if y = vecSingle hb (vecSum y) then
    cycPrimitiveM (n := n) (Profile n) (U p w)
      (vecSum y + 1) (r + vecSum y)
  else 0

noncomputable def triangleLeafE6AbackSection
    {n a b d : ℕ} [NeZero n] (hb : 0 < b) :
    BDiagCoeff n a d →ₗ[F] CFun4 n a b d where
  toFun U p y r w :=
    triangleLeafE6AbackSectionValue hb U p y r w
  map_add' U V := by
    funext p y r w
    change
      (if y = vecSingle hb (vecSum y) then
        cycPrimitiveM (n := n) (Profile n) ((U + V) p w)
          (vecSum y + 1) (r + vecSum y)
      else 0) =
        (if y = vecSingle hb (vecSum y) then
          cycPrimitiveM (n := n) (Profile n) (U p w)
            (vecSum y + 1) (r + vecSum y)
        else 0) +
          if y = vecSingle hb (vecSum y) then
            cycPrimitiveM (n := n) (Profile n) (V p w)
              (vecSum y + 1) (r + vecSum y)
          else 0
    by_cases hy : y = vecSingle hb (vecSum y)
    · rw [if_pos hy, if_pos hy, if_pos hy]
      change
        cycPrimitiveM (n := n) (Profile n) (U p w + V p w)
            (vecSum y + 1) (r + vecSum y) =
          cycPrimitiveM (n := n) (Profile n) (U p w)
              (vecSum y + 1) (r + vecSum y) +
            cycPrimitiveM (n := n) (Profile n) (V p w)
              (vecSum y + 1) (r + vecSum y)
      exact congrFun
        (congrFun
          ((cycPrimitiveM (n := n) (Profile n)).map_add (U p w) (V p w))
          (vecSum y + 1)) (r + vecSum y)
    · rw [if_neg hy, if_neg hy, if_neg hy, add_zero]
  map_smul' x U := by
    funext p y r w
    change
      (if y = vecSingle hb (vecSum y) then
        cycPrimitiveM (n := n) (Profile n) ((x • U) p w)
          (vecSum y + 1) (r + vecSum y)
      else 0) =
        x *
          if y = vecSingle hb (vecSum y) then
            cycPrimitiveM (n := n) (Profile n) (U p w)
              (vecSum y + 1) (r + vecSum y)
          else 0
    by_cases hy : y = vecSingle hb (vecSum y)
    · rw [if_pos hy, if_pos hy]
      change
        cycPrimitiveM (n := n) (Profile n) (x • U p w)
            (vecSum y + 1) (r + vecSum y) =
          x *
            cycPrimitiveM (n := n) (Profile n) (U p w)
              (vecSum y + 1) (r + vecSum y)
      simpa only [smul_eq_mul] using
        congrFun
          (congrFun
            ((cycPrimitiveM (n := n) (Profile n)).map_smul x (U p w))
            (vecSum y + 1)) (r + vecSum y)
    · rw [if_neg hy, if_neg hy, mul_zero]

private theorem triangleLeafE6CFiber_AbackSection
    {n a b d : ℕ} [NeZero n] (hb : 0 < b)
    (U : BDiagCoeff n a d)
    (p : PVec n a) (s r : I n) (w : WVec n d) :
    triangleLeafE6CFiber
        (triangleLeafE6AbackSection (n := n) (a := a) (d := d) hb U)
        p s r w =
      cycPrimitiveM (n := n) (Profile n) (U p w) (s + 1) (r + s) := by
  classical
  change
    (∑ y : YVec n b,
      if vecSum y = s then
        triangleLeafE6AbackSectionValue hb U p y r w
      else 0) = _
  rw [Finset.sum_eq_single (vecSingle hb s)]
  · simp [triangleLeafE6AbackSectionValue, vecSum_vecSingle]
  · intro y _ hy
    by_cases hys : vecSum y = s
    · simp only [hys, if_pos]
      have hy' : y ≠ vecSingle hb (vecSum y) := by
        simpa [hys] using hy
      simp [triangleLeafE6AbackSectionValue, hy']
    · simp [hys]
  · simp

theorem triangleLeafE6Aback_section
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (U : BDiagCoeff n a d) :
    triangleLeafE6Aback
        (triangleLeafE6AbackSection
          (n := n) (a := a) (d := d) hb U) =
      U := by
  funext p w
  apply Subtype.ext
  have hprimitive :=
    congrArg Subtype.val
      (cycDiff_cycPrimitiveM (n := n) (Profile n) (U p w))
  change
    cycDiff (n := n) (Profile n)
        (cycPrimitiveM (n := n) (Profile n) (U p w)) =
      (U p w).1 at hprimitive
  change
    cycDiff (n := n) (Profile n)
        (fun q u =>
          triangleLeafE6CFiber
            (triangleLeafE6AbackSection
              (n := n) (a := a) (d := d) hb U)
            p (q - 1) (u - (q - 1)) w) =
      (U p w).1
  simp_rw [triangleLeafE6CFiber_AbackSection]
  simpa only [sub_add_cancel] using hprimitive

theorem triangleLeafE6Aback_surjective
    {n a b d : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Surjective
      (triangleLeafE6Aback
        (n := n) (a := a) (b := b) (d := d)) := by
  intro U
  exact ⟨triangleLeafE6AbackSection hb U,
    triangleLeafE6Aback_section hb U⟩

noncomputable def triangleLeafE6AlphaShearCoeffSection
    {n a b d : ℕ} [NeZero n] (hb : 0 < b) :
    BDiagCoeff n a d →ₗ[F] CFun4 n a b d :=
  (triangleLeafE6AbackSection
    (n := n) (a := a) (d := d) hb).comp
      (triangleLeafE6DiagShearEquiv
        (n := n) (a := a) (d := d)).toLinearMap

theorem triangleLeafE6AlphaShearCoeff_section
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (U : BDiagCoeff n a d) :
    triangleLeafE6AlphaShearCoeff
        (triangleLeafE6AlphaShearCoeffSection
          (n := n) (a := a) (d := d) hb U) =
      U := by
  change
    triangleLeafE6DiagShear
        (triangleLeafE6Aback
          (triangleLeafE6AbackSection hb
            (triangleLeafE6DiagShear U))) =
      U
  rw [triangleLeafE6Aback_section,
    triangleLeafE6DiagShear_involutive]

theorem triangleLeafE6AlphaShearCoeff_surjective
    {n a b d : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Surjective
      (triangleLeafE6AlphaShearCoeff
        (n := n) (a := a) (b := b) (d := d)) := by
  intro U
  exact ⟨triangleLeafE6AlphaShearCoeffSection hb U,
    triangleLeafE6AlphaShearCoeff_section hb U⟩

end

end TriangleLeaf
end Core4loop
