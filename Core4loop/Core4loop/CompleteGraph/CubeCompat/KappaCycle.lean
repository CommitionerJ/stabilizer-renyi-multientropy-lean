import Core4loop.CompleteGraph.CubeCompat.DiagonalShear

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.CubeCompat

open Core4loop.CompleteGraph.ScalarCycle
open Core4loop.SquareDiagonal.EvenP

noncomputable section

attribute [local instance] Fintype.ofFinite

private abbrev K4CubeIndex (n : Nat) := I n × I n × I n

private def k4CubeIndexShear
    (n : Nat) [NeZero n] :
    K4CubeIndex n ≃ K4CubeIndex n where
  toFun q := (q.1, q.1 + q.2.1 + q.2.2, q.2.2)
  invFun q := (q.1, q.2.1 - q.1 - q.2.2, q.2.2)
  left_inv q := by
    rcases q with ⟨i, j, k⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp only [sub_eq_add_neg]
        abel
      · rfl
  right_inv q := by
    rcases q with ⟨x, y, z⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp only [sub_eq_add_neg]
        abel
      · rfl

private def k4CubeIndexShearPhase
    (n : Nat) [NeZero n] :
    K4CubeIndex n ≃ K4CubeIndex n where
  toFun q := (q.1, q.1 + q.2.1 + q.2.2 + 1, q.2.2)
  invFun q := (q.1, q.2.1 - q.1 - q.2.2 - 1, q.2.2)
  left_inv q := by
    rcases q with ⟨i, j, k⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp only [sub_eq_add_neg]
        abel
      · rfl
  right_inv q := by
    rcases q with ⟨x, y, z⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp only [sub_eq_add_neg]
        abel
      · rfl

noncomputable def k4CubeKappa
    {n : Nat} [NeZero n]
    (B W : CyclicCube n) : F :=
  ∑ q : K4CubeIndex n,
    (B q.1 q.2.1 q.2.2 * W q.1 q.2.1 q.2.2
      + B (q.1 + 1) q.2.1 q.2.2 *
          W q.1 q.2.1 (q.2.2 + 1))

private theorem k4CubeKappa_shear
    {n : Nat} [NeZero n]
    (B W : CyclicCube n) :
    k4CubeKappa B W =
      ∑ q : K4CubeIndex n,
        (k4CubeDiagonalShear B q.1 q.2.1 q.2.2 *
            k4CubeDiagonalShear W q.1 q.2.1 q.2.2
          + k4CubeDiagonalShear B (q.1 + 1) q.2.1 q.2.2 *
              k4CubeDiagonalShear W q.1 q.2.1 (q.2.2 + 1)) := by
  unfold k4CubeKappa
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · apply Fintype.sum_equiv (k4CubeIndexShear n)
    intro q
    change
      B q.1 q.2.1 q.2.2 * W q.1 q.2.1 q.2.2 =
        B q.1 ((q.1 + q.2.1 + q.2.2) - q.1 - q.2.2) q.2.2 *
          W q.1 ((q.1 + q.2.1 + q.2.2) - q.1 - q.2.2) q.2.2
    have hj : (q.1 + q.2.1 + q.2.2) - q.1 - q.2.2 = q.2.1 := by
      abel
    rw [hj]
  · apply Fintype.sum_equiv (k4CubeIndexShearPhase n)
    intro q
    change
      B (q.1 + 1) q.2.1 q.2.2 *
          W q.1 q.2.1 (q.2.2 + 1) =
        B (q.1 + 1)
            ((q.1 + q.2.1 + q.2.2 + 1) - (q.1 + 1) - q.2.2)
            q.2.2 *
          W q.1
            ((q.1 + q.2.1 + q.2.2 + 1) - q.1 - (q.2.2 + 1))
            (q.2.2 + 1)
    have hjB :
        (q.1 + q.2.1 + q.2.2 + 1) - (q.1 + 1) - q.2.2 =
          q.2.1 := by
      abel
    have hjW :
        (q.1 + q.2.1 + q.2.2 + 1) - q.1 - (q.2.2 + 1) =
          q.2.1 := by
      abel
    rw [hjB, hjW]

private theorem cubePair_eq_cubeDot
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubePair X Y = cubeDot X Y := by
  unfold cubePair cubeDot
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  calc
    (∑ y : I n, ∑ z : I n, ∑ x : I n,
        X x y z * Y x y z) =
        ∑ y : I n, ∑ x : I n, ∑ z : I n,
          X x y z * Y x y z := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = ∑ x : I n, ∑ y : I n, ∑ z : I n,
          X x y z * Y x y z := by
      rw [Finset.sum_comm]

private theorem cubeDot_shiftZ_self
    {n : Nat} [NeZero n] (W : CyclicCube n) :
    cubeDot (fun x y z => W x y (z + 1))
        (fun x y z => W x y (z + 1)) =
      cubeDot W W := by
  unfold cubeDot
  let e : K4CubeIndex n ≃ K4CubeIndex n :=
    Equiv.prodCongr (Equiv.refl (I n))
      (Equiv.prodCongr (Equiv.refl (I n)) (Equiv.addRight (1 : I n)))
  apply Fintype.sum_equiv e
  intro q
  simp [e]

private theorem k4CubeKappa_sheared_eq_cycleQ
    {n : Nat} [NeZero n]
    (B W : CyclicCube n)
    (hcl : k4Closure B 0 W) :
    (∑ q : K4CubeIndex n,
        (B q.1 q.2.1 q.2.2 * W q.1 q.2.1 q.2.2
          + B (q.1 + 1) q.2.1 q.2.2 *
              W q.1 q.2.1 (q.2.2 + 1))) =
      cycleQ B 0 W := by
  rw [cycleQ, cubePair_eq_cubeDot]
  simp only [add_zero]
  rw [show cubePair (0 : CyclicCube n) (cubeTyInvTzSum W) = 0 by
    simp [cubePair]]
  rw [add_zero]
  unfold cubeDot
  have hpoint :
      ∀ q : K4CubeIndex n,
        (B q.1 q.2.1 q.2.2 + W q.1 q.2.1 q.2.2) *
            (B q.1 q.2.1 q.2.2 + B (q.1 + 1) q.2.1 q.2.2) =
          (B q.1 q.2.1 q.2.2 * W q.1 q.2.1 q.2.2
            + B (q.1 + 1) q.2.1 q.2.2 *
                W q.1 q.2.1 (q.2.2 + 1))
          + (W q.1 q.2.1 q.2.2 * W q.1 q.2.1 q.2.2
            + W q.1 q.2.1 (q.2.2 + 1) *
                W q.1 q.2.1 (q.2.2 + 1)) := by
    intro q
    have h := hcl q.1 q.2.1 q.2.2
    simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ,
      Pi.zero_apply, add_zero] at h
    have hshift :
        B (q.1 + 1) q.2.1 q.2.2 =
          B q.1 q.2.1 q.2.2 +
            W q.1 q.2.1 q.2.2 +
            W q.1 q.2.1 (q.2.2 + 1) := by
      calc
        B (q.1 + 1) q.2.1 q.2.2 =
            B (q.1 + 1) q.2.1 q.2.2 + 0 := by rw [add_zero]
        _ = B (q.1 + 1) q.2.1 q.2.2 +
            ((B q.1 q.2.1 q.2.2 +
              B (q.1 + 1) q.2.1 q.2.2) +
              (W q.1 q.2.1 q.2.2 +
                W q.1 q.2.1 (q.2.2 + 1))) := by rw [h]
        _ = (B (q.1 + 1) q.2.1 q.2.2 +
              B (q.1 + 1) q.2.1 q.2.2) +
            (B q.1 q.2.1 q.2.2 +
              (W q.1 q.2.1 q.2.2 +
                W q.1 q.2.1 (q.2.2 + 1))) := by abel
        _ = _ := by
          rw [F_add_self, zero_add]
          exact (add_assoc _ _ _).symm
    rw [hshift]
    ring_nf
    simp only [show (2 : F) = 0 by decide,
      show (3 : F) = 1 by decide, mul_zero, mul_one, add_zero]
  simp only [Pi.add_apply, cyclicDiffX]
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  have hsq :
      (∑ q : K4CubeIndex n,
        W q.1 q.2.1 (q.2.2 + 1) *
          W q.1 q.2.1 (q.2.2 + 1)) =
      ∑ q : K4CubeIndex n,
        W q.1 q.2.1 q.2.2 * W q.1 q.2.1 q.2.2 := by
    simpa only [cubeDot] using cubeDot_shiftZ_self W
  rw [hsq]
  simp only [F_add_self, add_zero]

theorem k4CubeKappa_eq_cycleQ_zeroC_of_closure
    {n : Nat} [NeZero n]
    (B W : CyclicCube n)
    (hcl : k4Closure B 0 W) :
    k4CubeKappa B W = cycleQ B 0 W :=
  k4CubeKappa_sheared_eq_cycleQ B W hcl

theorem k4CubeKappa_eq_cycleQ_zeroC
    {n : Nat} [NeZero n]
    (B W : CyclicCube n)
    (h : cubeDiffP B + cubeDiffR W = 0) :
    k4CubeKappa B W =
      cycleQ (k4CubeDiagonalShear B) 0
        (k4CubeDiagonalShear W) := by
  rw [k4CubeKappa_shear]
  exact k4CubeKappa_sheared_eq_cycleQ
    (k4CubeDiagonalShear B) (k4CubeDiagonalShear W)
    ((k4CubeDiagonalShear_compat B W).mp h)

theorem k4CubeKappa_zero_of_compat
    {n : Nat} [NeZero n] (hn2 : 2 <= n)
    (B W : CyclicCube n)
    (h : cubeDiffP B + cubeDiffR W = 0) :
    k4CubeKappa B W = 0 := by
  rw [k4CubeKappa_eq_cycleQ_zeroC B W h]
  exact cycleQ_zero_of_closure hn2
    (k4CubeDiagonalShear B) 0 (k4CubeDiagonalShear W)
    ((k4CubeDiagonalShear_compat B W).mp h)


end

end Core4loop.CompleteGraph.CubeCompat
