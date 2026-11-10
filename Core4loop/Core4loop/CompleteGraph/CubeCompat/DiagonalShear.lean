import Core4loop.CompleteGraph.ScalarCycle.CycleCertificate
import Core4loop.SquareDiagonal.EvenP.CubeOrbit

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.CompleteGraph.CubeCompat

open Core4loop.CompleteGraph.ScalarCycle
open Core4loop.SquareDiagonal.EvenP

noncomputable section

noncomputable def k4CubeDiagonalShear
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun x y z => f x (y - x - z) z
  invFun g := fun i j k => g i (i + j + k) k
  left_inv f := by
    funext i j k
    apply congrArg (fun t => f i t k)
    abel
  right_inv g := by
    funext x y z
    apply congrArg (fun t => g x t z)
    abel
  map_add' f g := by
    funext x y z
    rfl
  map_smul' r f := by
    funext x y z
    rfl

theorem k4CubeDiagonalShear_compat
    {n : Nat} [NeZero n]
    (B W : CyclicCube n) :
    cubeDiffP B + cubeDiffR W = 0 ↔
      k4Closure
        (k4CubeDiagonalShear B) 0 (k4CubeDiagonalShear W) := by
  constructor
  · intro h x y z
    have hpoint :=
      congrFun (congrFun (congrFun h x) (y - x - z)) z
    simp only [Pi.add_apply, Pi.zero_apply] at hpoint
    have hP :
        cubeDiffP B x (y - x - z) z =
          B x (y - x - z) z +
            B (x + 1) ((y - x - z) - 1) z := by
      change
        B x (y - x - z) z +
            B (x + 1) ((y - x - z) + (-1)) (z + 0) = _
      simp [sub_eq_add_neg]
    have hR :
        cubeDiffR W x (y - x - z) z =
          W x (y - x - z) z +
            W x ((y - x - z) - 1) (z + 1) := by
      change
        W x (y - x - z) z +
            W (x + 0) ((y - x - z) + (-1)) (z + 1) = _
      simp [sub_eq_add_neg]
    rw [hP, hR] at hpoint
    change
      (B x (y - x - z) z +
          B (x + 1) (y - (x + 1) - z) z) +
        (0 + 0) +
        (W x (y - x - z) z +
          W x (y - x - (z + 1)) (z + 1)) = 0
    have hx : y - (x + 1) - z = (y - x - z) - 1 := by
      abel
    have hz : y - x - (z + 1) = (y - x - z) - 1 := by
      abel
    rw [hx, hz, zero_add]
    simpa only [add_zero] using hpoint
  · intro h
    funext i j k
    have hpoint := h i (i + j + k) k
    change
      (B i ((i + j + k) - i - k) k +
          B (i + 1) ((i + j + k) - (i + 1) - k) k) +
        (0 + 0) +
        (W i ((i + j + k) - i - k) k +
          W i ((i + j + k) - i - (k + 1)) (k + 1)) = 0 at hpoint
    have h0 : (i + j + k) - i - k = j := by
      abel
    have hP : (i + j + k) - (i + 1) - k = j - 1 := by
      abel
    have hR : (i + j + k) - i - (k + 1) = j - 1 := by
      abel
    rw [h0, hP, hR, zero_add, add_zero] at hpoint
    simp only [Pi.add_apply, Pi.zero_apply]
    have hDiffP :
        cubeDiffP B i j k =
          B i j k + B (i + 1) (j - 1) k := by
      change
        B i j k + B (i + 1) (j + (-1)) (k + 0) = _
      simp [sub_eq_add_neg]
    have hDiffR :
        cubeDiffR W i j k =
          W i j k + W i (j - 1) (k + 1) := by
      change
        W i j k + W (i + 0) (j + (-1)) (k + 1) = _
      simp [sub_eq_add_neg]
    rw [hDiffP, hDiffR]
    exact hpoint

end

end Core4loop.CompleteGraph.CubeCompat
