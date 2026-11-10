import Core4loop.QuadraticSignSum
import Core4loop.SquareDiagonal.BWSupport

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

abbrev SqdiagBWAAdjointGraph
    (n a b c d : ℕ) [NeZero n] :=
  sqdiagBWAAdjointGraphSubmodule
    (n := n) (a := a) (b := b) (c := c) (d := d)

noncomputable instance instFintypeSqdiagBWAAdjointGraph
    {n a b c d : ℕ} [NeZero n] :
    Fintype (SqdiagBWAAdjointGraph n a b c d) :=
  Fintype.ofInjective
    (fun x : SqdiagBWAAdjointGraph n a b c d =>
      (x : (BFun4 n a c d × WFun4 n a b c) × RootTarget n b c d))
    (by
      intro x y hxy
      exact Subtype.ext hxy)

lemma sqdiagRootCoeffApply_comm
    {n b c d : ℕ} [NeZero n]
    (A R : RootTarget n b c d) :
    sqdiagRootCoeffApply A R = sqdiagRootCoeffApply R A := by
  unfold sqdiagRootCoeffApply
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro z _
  refine Finset.sum_congr rfl ?_
  intro w _
  rw [mul_comm]

lemma sqdiagRootCoeffApply_add_left
    {n b c d : ℕ} [NeZero n]
    (A A' R : RootTarget n b c d) :
    sqdiagRootCoeffApply (A + A') R =
      sqdiagRootCoeffApply A R + sqdiagRootCoeffApply A' R := by
  simpa using
    (sqdiagRootCoeffLinearMap
      (n := n) (b := b) (c := c) (d := d) R).map_add A A'

lemma sqdiagRootCoeffApply_add_right
    {n b c d : ℕ} [NeZero n]
    (A R R' : RootTarget n b c d) :
    sqdiagRootCoeffApply A (R + R') =
      sqdiagRootCoeffApply A R + sqdiagRootCoeffApply A R' := by
  calc
    sqdiagRootCoeffApply A (R + R') =
        sqdiagRootCoeffApply (R + R') A := by
          rw [sqdiagRootCoeffApply_comm]
    _ = sqdiagRootCoeffApply R A + sqdiagRootCoeffApply R' A := by
          rw [sqdiagRootCoeffApply_add_left]
    _ = sqdiagRootCoeffApply A R + sqdiagRootCoeffApply A R' := by
          rw [sqdiagRootCoeffApply_comm R A, sqdiagRootCoeffApply_comm R' A]

lemma sqdiagRootCoeffApply_smul_left
    {n b c d : ℕ} [NeZero n]
    (r : F) (A R : RootTarget n b c d) :
    sqdiagRootCoeffApply (r • A) R =
      r • sqdiagRootCoeffApply A R := by
  change sqdiagRootCoeffApply (r • A) R = r * sqdiagRootCoeffApply A R
  exact
    (sqdiagRootCoeffLinearMap
      (n := n) (b := b) (c := c) (d := d) R).map_smul r A

lemma sqdiagRootCoeffApply_smul_right
    {n b c d : ℕ} [NeZero n]
    (r : F) (A R : RootTarget n b c d) :
    sqdiagRootCoeffApply A (r • R) =
      r • sqdiagRootCoeffApply A R := by
  calc
    sqdiagRootCoeffApply A (r • R) =
        sqdiagRootCoeffApply (r • R) A := by
          rw [sqdiagRootCoeffApply_comm]
    _ = r • sqdiagRootCoeffApply R A := by
          rw [sqdiagRootCoeffApply_smul_left]
    _ = r • sqdiagRootCoeffApply A R := by
          rw [sqdiagRootCoeffApply_comm R A]

noncomputable def sqdiagBWAAdjointGraphSourceMap
    {n a b c d : ℕ} [NeZero n] :
    SqdiagBWAAdjointGraph n a b c d →ₗ[F]
      BFun4 n a c d × WFun4 n a b c where
  toFun x := x.1.1
  map_add' x y := rfl
  map_smul' r x := rfl

noncomputable def sqdiagBWAAdjointGraphAMap
    {n a b c d : ℕ} [NeZero n] :
    SqdiagBWAAdjointGraph n a b c d →ₗ[F]
      RootTarget n b c d where
  toFun x := x.1.2
  map_add' x y := rfl
  map_smul' r x := rfl

noncomputable def sqdiagBWAAdjointGraphRootMap
    {n a b c d : ℕ} [NeZero n] :
    SqdiagBWAAdjointGraph n a b c d →ₗ[F] RootTarget n b c d :=
  (K_yw (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagBWAAdjointGraphSourceMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

@[simp]
theorem sqdiagBWAAdjointGraphSourceMap_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d) :
    sqdiagBWAAdjointGraphSourceMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x = x.1.1 := rfl

@[simp]
theorem sqdiagBWAAdjointGraphAMap_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d) :
    sqdiagBWAAdjointGraphAMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x = x.1.2 := rfl

@[simp]
theorem sqdiagBWAAdjointGraphRootMap_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d) :
    sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x =
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 := rfl

noncomputable def sqdiagBWAAdjointGraphQ
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d) : F :=
  sqdiagRootCoeffApply
    (sqdiagBWAAdjointGraphAMap
      (n := n) (a := a) (b := b) (c := c) (d := d) x)
    (sqdiagBWAAdjointGraphRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d) x)

set_option maxHeartbeats 800000 in
noncomputable def sqdiagBWAAdjointGraphPolar
    {n a b c d : ℕ} [NeZero n] :
    SqdiagBWAAdjointGraph n a b c d →ₗ[F]
      SqdiagBWAAdjointGraph n a b c d →ₗ[F] F where
  toFun := fun x =>
  {
    toFun := fun y =>
      sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x)
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y) +
        sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y)
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x)
    map_add' := by
      intro y z
      change
        sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) (y + z)) +
          sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) (y + z))
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
        =
        (sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) y) +
          sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) y)
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x)) +
        (sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) z) +
          sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) z)
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x))
      rw [
        (sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
        (sqdiagBWAAdjointGraphAMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
        sqdiagRootCoeffApply_add_right,
        sqdiagRootCoeffApply_add_left]
      abel
    map_smul' := by
      intro r y
      change
        sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) (r • y)) +
          sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) (r • y))
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
        =
          r •
            (sqdiagRootCoeffApply
                (sqdiagBWAAdjointGraphAMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) x)
                (sqdiagBWAAdjointGraphRootMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) y) +
              sqdiagRootCoeffApply
                (sqdiagBWAAdjointGraphAMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) y)
                (sqdiagBWAAdjointGraphRootMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) x))
      rw [
        (sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul,
        (sqdiagBWAAdjointGraphAMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul,
        sqdiagRootCoeffApply_smul_right,
        sqdiagRootCoeffApply_smul_left]
      simp [smul_eq_mul, mul_add]
  }
  map_add' := by
    intro x y
    ext z
    change
      sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) (x + y))
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) z) +
        sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) z)
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) (x + y))
      =
      (sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x)
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) z) +
        sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) z)
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x)) +
      (sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y)
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) z) +
        sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) z)
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y))
    rw [
      (sqdiagBWAAdjointGraphAMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
      (sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
      sqdiagRootCoeffApply_add_left,
      sqdiagRootCoeffApply_add_right]
    abel
  map_smul' := by
    intro r x
    ext y
    change
      sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) (r • x))
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y) +
        sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y)
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) (r • x))
      =
        r •
          (sqdiagRootCoeffApply
              (sqdiagBWAAdjointGraphAMap
                (n := n) (a := a) (b := b) (c := c) (d := d) x)
              (sqdiagBWAAdjointGraphRootMap
                (n := n) (a := a) (b := b) (c := c) (d := d) y) +
            sqdiagRootCoeffApply
              (sqdiagBWAAdjointGraphAMap
                (n := n) (a := a) (b := b) (c := c) (d := d) y)
              (sqdiagBWAAdjointGraphRootMap
                (n := n) (a := a) (b := b) (c := c) (d := d) x))
    rw [
      (sqdiagBWAAdjointGraphAMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul,
      (sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul,
      sqdiagRootCoeffApply_smul_left,
      sqdiagRootCoeffApply_smul_right]
    simp [smul_eq_mul, mul_add]

@[simp]
theorem sqdiagBWAAdjointGraphPolar_apply
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagBWAAdjointGraph n a b c d) :
    sqdiagBWAAdjointGraphPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y =
      sqdiagRootCoeffApply x.1.2
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1) +
        sqdiagRootCoeffApply y.1.2
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1) := rfl

set_option maxHeartbeats 800000 in
lemma sqdiagBWAAdjointGraphQ_add
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagBWAAdjointGraph n a b c d) :
    sqdiagBWAAdjointGraphQ (x + y) =
      sqdiagBWAAdjointGraphQ x +
      sqdiagBWAAdjointGraphQ y +
    sqdiagBWAAdjointGraphPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y := by
  change
    sqdiagRootCoeffApply
        (sqdiagBWAAdjointGraphAMap
          (n := n) (a := a) (b := b) (c := c) (d := d) (x + y))
        (sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) (x + y))
    =
      sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x)
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x) +
        sqdiagRootCoeffApply
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y)
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y) +
        (sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) y) +
          sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) y)
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x))
  rw [
    (sqdiagBWAAdjointGraphAMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
    (sqdiagBWAAdjointGraphRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
    sqdiagRootCoeffApply_add_left,
    sqdiagRootCoeffApply_add_right,
    sqdiagRootCoeffApply_add_right]
  abel

theorem sqdiagBWAAdjointGraphRootSignSum_eq_submodule_sum
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      ∑ x : SqdiagBWAAdjointGraph n a b c d,
        bitSign (sqdiagBWAAdjointGraphQ x) := by
  unfold sqdiagBWAAdjointGraphRootSignSum
  simpa [sqdiagBWAAdjointGraphQ] using
    (sqdiagBWAAdjointGraphSupportEquivSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d)).sum_comp
      (fun x : SqdiagBWAAdjointGraph n a b c d =>
        bitSign (sqdiagBWAAdjointGraphQ x))

end

end SquareDiagonal
end Core4loop
