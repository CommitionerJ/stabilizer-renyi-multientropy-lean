import Core4loop.TriangleLeaf.E6CoeffPairingCore
import Core4loop.ZeroSumSpaces.ProfileMRange

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Neutral sheared coefficient coordinates for the TriangleLeaf E6 route.

`triangleLeafE6Aback` is the literal unsheared Q1 coefficient.  The S1
coordinate is `triangleLeafE6AlphaShearCoeff`, obtained only after the
involutive diagonal shear.
-/

noncomputable def triangleLeafE6CFiber
    {n a b d : ℕ} [NeZero n] :
    CFun4 n a b d →ₗ[F]
      (PVec n a → I n → I n → WVec n d → F) where
  toFun C := fun p s r w =>
    ∑ y : YVec n b, if vecSum y = s then C p y r w else 0
  map_add' C D := by
    funext p s r w
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases hy : vecSum y = s <;> simp [hy]
  map_smul' x C := by
    funext p s r w
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases hy : vecSum y = s <;> simp [hy, mul_zero]

@[simp]
theorem triangleLeafE6CFiber_apply
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d)
    (p : PVec n a) (s r : I n) (w : WVec n d) :
    triangleLeafE6CFiber
        (n := n) (a := a) (b := b) (d := d) C p s r w =
      ∑ y : YVec n b, if vecSum y = s then C p y r w else 0 :=
  rfl

noncomputable def triangleLeafE6Aback
    {n a b d : ℕ} [NeZero n] :
    CFun4 n a b d →ₗ[F] BDiagCoeff n a d where
  toFun C := fun p w =>
    ⟨cycDiff (n := n) (Profile n)
        (fun q u =>
          triangleLeafE6CFiber
            (n := n) (a := a) (b := b) (d := d)
            C p (q - 1) (u - (q - 1)) w),
      cycDiff_mem_ZeroSumProfileM _⟩
  map_add' C D := by
    funext p w
    apply Subtype.ext
    change
      cycDiff (n := n) (Profile n)
          (fun q u =>
            triangleLeafE6CFiber
              (n := n) (a := a) (b := b) (d := d)
              (C + D) p (q - 1) (u - (q - 1)) w) =
        cycDiff (n := n) (Profile n)
            (fun q u =>
              triangleLeafE6CFiber
                (n := n) (a := a) (b := b) (d := d)
                C p (q - 1) (u - (q - 1)) w) +
          cycDiff (n := n) (Profile n)
            (fun q u =>
              triangleLeafE6CFiber
                (n := n) (a := a) (b := b) (d := d)
                D p (q - 1) (u - (q - 1)) w)
    rw [← (cycDiff (n := n) (Profile n)).map_add]
    congr
    funext q u
    simp only [map_add, Pi.add_apply]
  map_smul' x C := by
    funext p w
    apply Subtype.ext
    change
      cycDiff (n := n) (Profile n)
          (fun q u =>
            triangleLeafE6CFiber
              (n := n) (a := a) (b := b) (d := d)
              (x • C) p (q - 1) (u - (q - 1)) w) =
        x •
          cycDiff (n := n) (Profile n)
            (fun q u =>
              triangleLeafE6CFiber
                (n := n) (a := a) (b := b) (d := d)
                C p (q - 1) (u - (q - 1)) w)
    rw [← (cycDiff (n := n) (Profile n)).map_smul]
    congr
    funext q u
    simp only [map_smul, Pi.smul_apply]

@[simp]
theorem triangleLeafE6Aback_apply
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d)
    (p : PVec n a) (w : WVec n d) (s u : I n) :
    (triangleLeafE6Aback
        (n := n) (a := a) (b := b) (d := d) C p w).1 s u =
      triangleLeafE6CFiber
          (n := n) (a := a) (b := b) (d := d)
          C p s (u - s) w +
        triangleLeafE6CFiber
          (n := n) (a := a) (b := b) (d := d)
          C p (s - 1) (u - s + 1) w := by
  change
    triangleLeafE6CFiber
          (n := n) (a := a) (b := b) (d := d)
          C p (s - 1) (u - (s - 1)) w +
        triangleLeafE6CFiber
          (n := n) (a := a) (b := b) (d := d)
          C p (s + 1 - 1) (u - (s + 1 - 1)) w =
      _
  have hs : s + 1 - 1 = s := by abel
  have hu : u - (s - 1) = u - s + 1 := by abel
  rw [hs, hu]
  abel

noncomputable def triangleLeafE6DiagShear
    {n a d : ℕ} [NeZero n] :
    BDiagCoeff n a d →ₗ[F] BDiagCoeff n a d where
  toFun U := fun p w =>
    ⟨fun s u => (U p w).1 (u - s) u, by
      apply LinearMap.mem_ker.mpr
      unfold sigmaMapM
      funext u
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
        Pi.zero_apply]
      have h := LinearMap.mem_ker.mp (U p w).2
      unfold sigmaMapM at h
      have hu := congrFun h u
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
        Finset.sum_apply] at hu
      simpa using
        ((Equiv.subLeft u).sum_comp
          (fun s : I n => (U p w).1 s u)).trans hu⟩
  map_add' U V := by
    funext p w
    apply Subtype.ext
    funext s u
    rfl
  map_smul' x U := by
    funext p w
    apply Subtype.ext
    funext s u
    rfl

@[simp]
theorem triangleLeafE6DiagShear_apply
    {n a d : ℕ} [NeZero n]
    (U : BDiagCoeff n a d)
    (p : PVec n a) (w : WVec n d) (s u : I n) :
    (triangleLeafE6DiagShear
        (n := n) (a := a) (d := d) U p w).1 s u =
      (U p w).1 (u - s) u :=
  rfl

theorem triangleLeafE6DiagShear_involutive
    {n a d : ℕ} [NeZero n]
    (U : BDiagCoeff n a d) :
    triangleLeafE6DiagShear
        (n := n) (a := a) (d := d)
        (triangleLeafE6DiagShear
          (n := n) (a := a) (d := d) U) =
      U := by
  funext p w
  apply Subtype.ext
  funext s u
  change (U p w).1 (u - (u - s)) u = (U p w).1 s u
  have hcoord : u - (u - s) = s := by abel
  rw [hcoord]

noncomputable def triangleLeafE6DiagShearEquiv
    {n a d : ℕ} [NeZero n] :
    BDiagCoeff n a d ≃ₗ[F] BDiagCoeff n a d where
  toFun :=
    triangleLeafE6DiagShear (n := n) (a := a) (d := d)
  invFun :=
    triangleLeafE6DiagShear (n := n) (a := a) (d := d)
  left_inv := triangleLeafE6DiagShear_involutive
  right_inv := triangleLeafE6DiagShear_involutive
  map_add' :=
    (triangleLeafE6DiagShear (n := n) (a := a) (d := d)).map_add
  map_smul' :=
    (triangleLeafE6DiagShear (n := n) (a := a) (d := d)).map_smul

noncomputable def triangleLeafE6AlphaShearCoeff
    {n a b d : ℕ} [NeZero n] :
    CFun4 n a b d →ₗ[F] BDiagCoeff n a d :=
  (triangleLeafE6DiagShearEquiv
    (n := n) (a := a) (d := d)).toLinearMap.comp
      (triangleLeafE6Aback
        (n := n) (a := a) (b := b) (d := d))

@[simp]
theorem triangleLeafE6AlphaShearCoeff_apply
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d)
    (p : PVec n a) (w : WVec n d) (s u : I n) :
    (triangleLeafE6AlphaShearCoeff
        (n := n) (a := a) (b := b) (d := d) C p w).1 s u =
      triangleLeafE6CFiber
          (n := n) (a := a) (b := b) (d := d)
          C p (u - s) s w +
        triangleLeafE6CFiber
          (n := n) (a := a) (b := b) (d := d)
          C p (u - s - 1) (s + 1) w := by
  change
    (triangleLeafE6Aback
      (n := n) (a := a) (b := b) (d := d) C p w).1 (u - s) u =
      _
  rw [triangleLeafE6Aback_apply]
  have hus : u - (u - s) = s := by abel
  rw [hus]

end

end TriangleLeaf
end Core4loop
