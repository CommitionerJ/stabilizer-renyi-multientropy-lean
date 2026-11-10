import Core4loop.TriangleLeaf.E6QZero

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
The all-parameter structural self-duality certificate for the TriangleLeaf
E6 branch.  This module contains no rank or signed-sum evaluation.
-/

theorem triangleLeafBOnly_le_triangleLeafE5LB
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafBOnly n a b c d ≤
      triangleLeafE5LB n a b c d := by
  intro y hy
  apply LinearMap.mem_ker.mpr
  ext z
  have hyC := LinearMap.mem_ker.mp hy
  have hzC := LinearMap.mem_ker.mp z.2
  change y.1.2 = 0 at hyC
  change z.1.1.2 = 0 at hzC
  change Q1 y.1.1 z.1.1.2 + Q1 z.1.1.1 y.1.2 = 0
  rw [hyC, hzC]
  unfold Q1 deltaC etaC
  simp

theorem triangleLeafE5LB_selfDual_of_q_zero
    {n a b c d : ℕ} [NeZero n]
    (hq_zero : ∀ X : triangleLeafE5LB n a b c d,
      triangleLeafCompatibleQ X.1 = 0) :
    ∀ x : triangleLeafCompatibleSubmodule n a b c d,
      ((triangleLeafCompatiblePolar x).comp
          (triangleLeafE5LB n a b c d).subtype = 0 ↔
        x ∈ triangleLeafE5LB n a b c d) := by
  intro x
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    ext y
    let yL : triangleLeafE5LB n a b c d :=
      ⟨y.1, triangleLeafBOnly_le_triangleLeafE5LB y.2⟩
    have hpoint := DFunLike.congr_fun hx yL
    change triangleLeafCompatiblePolar x y.1 = 0 at hpoint
    exact hpoint
  · intro hx
    ext y
    let xL : triangleLeafE5LB n a b c d := ⟨x, hx⟩
    have hqX := hq_zero xL
    have hqY := hq_zero y
    have hqXY := hq_zero (xL + y)
    have hadd := triangleLeafCompatibleQ_add xL.1 y.1
    have hqXY' :
        triangleLeafCompatibleQ (xL.1 + y.1) = 0 := by
      simpa using hqXY
    rw [hqXY', hqX, hqY] at hadd
    have hp : triangleLeafCompatiblePolar xL.1 y.1 = 0 := by
      simpa using hadd.symm
    change triangleLeafCompatiblePolar x y.1 = 0
    exact hp

theorem triangleLeafE5LB_selfDual_even_large
    {n a b c d : ℕ} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    ∀ x : triangleLeafCompatibleSubmodule n a b c d,
      ((triangleLeafCompatiblePolar x).comp
          (triangleLeafE5LB n a b c d).subtype = 0 ↔
        x ∈ triangleLeafE5LB n a b c d) :=
  triangleLeafE5LB_selfDual_of_q_zero
    (triangleLeafE5LB_q_zero_even_large hn2 hn ha2 hb2 hc2 hd2)

end

end TriangleLeaf
end Core4loop
