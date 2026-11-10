import Core4loop.SquareDiagonal.BWAdjointImage
import Core4loop.Square.Rank.Maps
import Core4loop.Square.Rank.IntersectionModel

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

noncomputable def sqdiagReducedRelationAmbientMap
    {n a b c d : ℕ} [NeZero n] :
    (↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ×
      ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)))) →ₗ[F]
      RootTarget n b c d × CFun4 n a b d where
  toFun x := (x.1.1, x.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def sqdiagReducedRelationSubmodule
    {n a b c d : ℕ} [NeZero n] :
    Submodule F
      (↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ×
       ↑(LinearMap.range
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))) :=
  (LinearMap.range
      (SquareCombined
        (n := n) (a := a) (b := b) (c := c) (d := d))).comap
    (sqdiagReducedRelationAmbientMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

abbrev SqdiagReducedRelation
    (n a b c d : ℕ) [NeZero n] :=
  ↑(sqdiagReducedRelationSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def sqdiagAdjointRangePair
    {n a b c d : ℕ} [NeZero n]
    (R : ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d))) :
    ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) →ₗ[F] F :=
  let L : RootTarget n b c d →ₗ[F] CFun4 n a b d :=
    sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d)
  let M : RootTarget n b c d →ₗ[F] F :=
    sqdiagRootCoeffLinearMap (n := n) (b := b) (c := c) (d := d) R.1
  let hker : LinearMap.ker L ≤ LinearMap.ker M := by
    intro A hA
    rw [LinearMap.mem_ker]
    have hzero :
        (M.comp (LinearMap.ker L).subtype) = 0 := by
      dsimp [M, L]
      exact
        sqdiagRootCoeffLinearMap_comp_ker_KCAdjointMap_eq_zero_of_mem_ZDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) R.1 R.2
    have happ :=
      congrArg
        (fun T : LinearMap.ker L →ₗ[F] F => T ⟨A, hA⟩)
        hzero
    simpa [M] using happ
  ((LinearMap.ker L).liftQ M hker).comp L.quotKerEquivRange.symm.toLinearMap

@[simp]
theorem sqdiagAdjointRangePair_mk_apply
    {n a b c d : ℕ} [NeZero n]
    (R : ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)))
    (A : RootTarget n b c d) :
    sqdiagAdjointRangePair
        (n := n) (a := a) (b := b) (c := c) (d := d) R
      ⟨sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d) A,
        ⟨A, rfl⟩⟩ =
    sqdiagRootCoeffApply A R.1 := by
  let L : RootTarget n b c d →ₗ[F] CFun4 n a b d :=
    sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d)
  let M : RootTarget n b c d →ₗ[F] F :=
    sqdiagRootCoeffLinearMap (n := n) (b := b) (c := c) (d := d) R.1
  let hker : LinearMap.ker L ≤ LinearMap.ker M := by
    intro A hA
    rw [LinearMap.mem_ker]
    have hzero :
        (M.comp (LinearMap.ker L).subtype) = 0 := by
      dsimp [M, L]
      exact
        sqdiagRootCoeffLinearMap_comp_ker_KCAdjointMap_eq_zero_of_mem_ZDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) R.1 R.2
    have happ :=
      congrArg
        (fun T : LinearMap.ker L →ₗ[F] F => T ⟨A, hA⟩)
        hzero
    simpa [M] using happ
  change
    ((LinearMap.ker L).liftQ M hker)
      (L.quotKerEquivRange.symm ⟨L A, ⟨A, rfl⟩⟩) =
    M A
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

theorem sqdiagAdjointRangePair_add_root
    {n a b c d : ℕ} [NeZero n]
    (R S : ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)))
    (C : ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)))) :
    sqdiagAdjointRangePair
        (n := n) (a := a) (b := b) (c := c) (d := d) (R + S) C =
      sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d) R C +
        sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d) S C := by
  rcases C.2 with ⟨A, hA⟩
  have hC :
      C =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) A,
          ⟨A, rfl⟩⟩ := by
    apply Subtype.ext
    exact hA.symm
  rw [hC]
  rw [sqdiagAdjointRangePair_mk_apply,
    sqdiagAdjointRangePair_mk_apply,
    sqdiagAdjointRangePair_mk_apply]
  simpa using
    sqdiagRootCoeffApply_add_right
      (n := n) (b := b) (c := c) (d := d) A R.1 S.1

theorem sqdiagAdjointRangePair_smul_root
    {n a b c d : ℕ} [NeZero n]
    (r : F)
    (R : ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)))
    (C : ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)))) :
    sqdiagAdjointRangePair
        (n := n) (a := a) (b := b) (c := c) (d := d) (r • R) C =
      r • sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d) R C := by
  rcases C.2 with ⟨A, hA⟩
  have hC :
      C =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) A,
          ⟨A, rfl⟩⟩ := by
    apply Subtype.ext
    exact hA.symm
  rw [hC]
  rw [sqdiagAdjointRangePair_mk_apply,
    sqdiagAdjointRangePair_mk_apply]
  simpa using
    sqdiagRootCoeffApply_smul_right
      (n := n) (b := b) (c := c) (d := d) r A R.1

theorem sqdiagAdjointRangePair_eq_zero_of_root_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (R : ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)))
    (C : ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d))))
    (hR : R.1 = 0) :
    sqdiagAdjointRangePair
        (n := n) (a := a) (b := b) (c := c) (d := d) R C = 0 := by
  rcases C.2 with ⟨A, hA⟩
  have hC :
      C =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) A,
          ⟨A, rfl⟩⟩ := by
    apply Subtype.ext
    exact hA.symm
  rw [hC, sqdiagAdjointRangePair_mk_apply]
  simp [hR, sqdiagRootCoeffApply]

noncomputable def sqdiagAdjointImageEquivReducedRelation
    {n a b c d : ℕ} [NeZero n] :
    SqdiagBWZAdjointImage n a b c d ≃ₗ[F]
      SqdiagReducedRelation n a b c d where
  toFun x :=
    let htarget :
        x.1.1 ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
          ∃ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              x.1.2 :=
      (sqdiagZAdjointTargetSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2.2
    ⟨(⟨x.1.1, htarget.1⟩, ⟨x.1.2, htarget.2⟩), x.2.1⟩
  invFun x :=
    ⟨(x.1.1.1, x.1.2.1),
      by
        constructor
        · exact x.2
        · apply (sqdiagZAdjointTargetSubmodule_mem_iff
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (x.1.1.1, x.1.2.1)).mpr
          exact ⟨x.1.1.2, x.1.2.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' _ _ := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' _ _ := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The reduced relation is a nested subtype/comap; build-mode instance synthesis needs more budget.
noncomputable def sqdiagReducedRelationRootMap
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRelation n a b c d →ₗ[F]
      ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun x := x.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- This kernel reuses the same nested reduced-relation module instance as the root map.
abbrev sqdiagReducedRelationVertical
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (SqdiagReducedRelation n a b c d) :=
  LinearMap.ker
    (sqdiagReducedRelationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def sqdiagReducedRelationCoeffMap
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRelation n a b c d →ₗ[F]
      ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) where
  toFun x := x.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def sqdiagReducedRelationQ
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagReducedRelation n a b c d) : F :=
  sqdiagAdjointRangePair
    (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2

theorem sqdiagReducedRelationQ_eq_zero_of_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVertical n a b c d) :
    sqdiagReducedRelationQ x = 0 := by
  rcases x.1.2.2 with ⟨A, hA⟩
  unfold sqdiagReducedRelationQ
  have hcoeff :
      x.1.2 =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) A,
          ⟨A, rfl⟩⟩ := by
    apply Subtype.ext
    simpa [sqdiagKCAdjointMap_apply] using hA.symm
  have hroot :
      x.1.1.1 = 0 := by
    exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)
  rw [hcoeff]
  rw [sqdiagAdjointRangePair_mk_apply]
  simp [hroot, sqdiagRootCoeffApply]

noncomputable def sqdiagReducedRelationPolar
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagReducedRelation n a b c d) : F :=
  sqdiagAdjointRangePair
      (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1 x.1.2 +
    sqdiagAdjointRangePair
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 y.1.2

set_option synthInstance.maxHeartbeats 200000 in
-- The nested reduced relation subtype makes the bundled bilinear-map instances expensive to infer.
noncomputable def sqdiagReducedRelationPolarLinear
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRelation n a b c d →ₗ[F]
      SqdiagReducedRelation n a b c d →ₗ[F] F where
  toFun x :=
    { toFun := fun y =>
        sqdiagReducedRelationPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) x y
      map_add' := by
        intro y z
        unfold sqdiagReducedRelationPolar
        change
          sqdiagAdjointRangePair
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (y.1.1 + z.1.1) x.1.2 +
            sqdiagAdjointRangePair
              (n := n) (a := a) (b := b) (c := c) (d := d)
              x.1.1 (y.1.2 + z.1.2) =
          (sqdiagAdjointRangePair
              (n := n) (a := a) (b := b) (c := c) (d := d)
              y.1.1 x.1.2 +
            sqdiagAdjointRangePair
              (n := n) (a := a) (b := b) (c := c) (d := d)
              x.1.1 y.1.2) +
          (sqdiagAdjointRangePair
              (n := n) (a := a) (b := b) (c := c) (d := d)
              z.1.1 x.1.2 +
            sqdiagAdjointRangePair
              (n := n) (a := a) (b := b) (c := c) (d := d)
              x.1.1 z.1.2)
        rw [sqdiagAdjointRangePair_add_root,
          (sqdiagAdjointRangePair
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1).map_add]
        abel
      map_smul' := by
        intro r y
        unfold sqdiagReducedRelationPolar
        change
          sqdiagAdjointRangePair
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (r • y.1.1) x.1.2 +
            sqdiagAdjointRangePair
              (n := n) (a := a) (b := b) (c := c) (d := d)
              x.1.1 (r • y.1.2) =
          r •
            (sqdiagAdjointRangePair
                (n := n) (a := a) (b := b) (c := c) (d := d)
                y.1.1 x.1.2 +
              sqdiagAdjointRangePair
                (n := n) (a := a) (b := b) (c := c) (d := d)
                x.1.1 y.1.2)
        rw [sqdiagAdjointRangePair_smul_root,
          (sqdiagAdjointRangePair
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1).map_smul]
        simp [smul_eq_mul, mul_add] }
  map_add' := by
    intro x y
    ext z
    unfold sqdiagReducedRelationPolar
    change
      sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d)
          z.1.1 (x.1.2 + y.1.2) +
        sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (x.1.1 + y.1.1) z.1.2 =
      (sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d)
          z.1.1 x.1.2 +
        sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d)
          x.1.1 z.1.2) +
      (sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d)
          z.1.1 y.1.2 +
        sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d)
          y.1.1 z.1.2)
    rw [(sqdiagAdjointRangePair
        (n := n) (a := a) (b := b) (c := c) (d := d) z.1.1).map_add,
      sqdiagAdjointRangePair_add_root]
    abel
  map_smul' := by
    intro r x
    ext z
    unfold sqdiagReducedRelationPolar
    change
      sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d)
          z.1.1 (r • x.1.2) +
        sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (r • x.1.1) z.1.2 =
      r •
        (sqdiagAdjointRangePair
            (n := n) (a := a) (b := b) (c := c) (d := d)
            z.1.1 x.1.2 +
          sqdiagAdjointRangePair
            (n := n) (a := a) (b := b) (c := c) (d := d)
            x.1.1 z.1.2)
    rw [(sqdiagAdjointRangePair
        (n := n) (a := a) (b := b) (c := c) (d := d) z.1.1).map_smul,
      sqdiagAdjointRangePair_smul_root]
    simp [smul_eq_mul, mul_add]

@[simp]
theorem sqdiagReducedRelationPolarLinear_apply
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagReducedRelation n a b c d) :
    sqdiagReducedRelationPolarLinear
        (n := n) (a := a) (b := b) (c := c) (d := d) x y =
      sqdiagReducedRelationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The target dual is over the vertical kernel subtype, so instance synthesis needs extra budget.
noncomputable def sqdiagReducedRelationPolarToVertical
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRelation n a b c d →ₗ[F]
      Module.Dual F (sqdiagReducedRelationVertical n a b c d) where
  toFun x :=
    (sqdiagReducedRelationPolarLinear
      (n := n) (a := a) (b := b) (c := c) (d := d) x).comp
      (sqdiagReducedRelationVertical n a b c d).subtype
  map_add' x y := by
    ext z
    change
      sqdiagReducedRelationPolarLinear
          (n := n) (a := a) (b := b) (c := c) (d := d) (x + y) z.1 =
        sqdiagReducedRelationPolarLinear
            (n := n) (a := a) (b := b) (c := c) (d := d) x z.1 +
          sqdiagReducedRelationPolarLinear
            (n := n) (a := a) (b := b) (c := c) (d := d) y z.1
    exact
      congrArg
        (fun L : SqdiagReducedRelation n a b c d →ₗ[F] F => L z.1)
        ((sqdiagReducedRelationPolarLinear
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x y)
  map_smul' r x := by
    ext z
    change
      sqdiagReducedRelationPolarLinear
          (n := n) (a := a) (b := b) (c := c) (d := d) (r • x) z.1 =
        r •
          sqdiagReducedRelationPolarLinear
            (n := n) (a := a) (b := b) (c := c) (d := d) x z.1
    exact
      congrArg
        (fun L : SqdiagReducedRelation n a b c d →ₗ[F] F => L z.1)
        ((sqdiagReducedRelationPolarLinear
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x)

set_option synthInstance.maxHeartbeats 200000 in
-- This kernel depends on the vertical-dual map over nested reduced-relation subtypes.
abbrev sqdiagReducedRelationVerticalOrthogonal
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (SqdiagReducedRelation n a b c d) :=
  LinearMap.ker
    (sqdiagReducedRelationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d))

theorem sqdiagReducedRelationPolar_eq_zero_of_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVertical n a b c d)
    (hy : y ∈ sqdiagReducedRelationVertical n a b c d) :
    sqdiagReducedRelationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y = 0 := by
  have hxroot : x.1.1.1 = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hx)
  have hyroot : y.1.1.1 = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hy)
  unfold sqdiagReducedRelationPolar
  rw [sqdiagAdjointRangePair_eq_zero_of_root_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1 x.1.2 hyroot,
    sqdiagAdjointRangePair_eq_zero_of_root_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 y.1.2 hxroot]
  simp

theorem sqdiagReducedRelationPolar_eq_rootCoeffApply_of_right_vertical_coeff_eq
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagReducedRelation n a b c d)
    (hy : y ∈ sqdiagReducedRelationVertical n a b c d)
    (A : RootTarget n b c d)
    (hcoeff :
      y.1.2 =
        ⟨sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d) A,
          ⟨A, rfl⟩⟩) :
    sqdiagReducedRelationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y =
      sqdiagRootCoeffApply A x.1.1.1 := by
  have hyroot : y.1.1.1 = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hy)
  unfold sqdiagReducedRelationPolar
  rw [sqdiagAdjointRangePair_eq_zero_of_root_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1 x.1.2 hyroot,
    hcoeff,
    sqdiagAdjointRangePair_mk_apply]
  simp

set_option synthInstance.maxHeartbeats 500000 in
-- A vertical reduced relation is invisible to the polar map restricted to vertical tests.
theorem sqdiagReducedRelationPolarToVertical_eq_zero_of_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVertical n a b c d) :
    sqdiagReducedRelationPolarToVertical
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  ext y
  change
    sqdiagReducedRelationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 = 0
  exact
    sqdiagReducedRelationPolar_eq_zero_of_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 hx y.2

set_option synthInstance.maxHeartbeats 500000 in
-- Therefore the polar-to-vertical map factors through the reduced root map.
theorem sqdiagReducedRelationRootMap_ker_le_polarToVertical_ker
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
      LinearMap.ker
        (sqdiagReducedRelationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro x hx
  rw [LinearMap.mem_ker]
  exact
    sqdiagReducedRelationPolarToVertical_eq_zero_of_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) x hx

set_option maxHeartbeats 800000 in
-- The induced map from root image to vertical dual realizes exactly the polar image.
set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRelationRootRangeToPolarVertical
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) →ₗ[F]
      Module.Dual F (sqdiagReducedRelationVertical n a b c d) :=
  let root :=
    sqdiagReducedRelationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let polar :=
    sqdiagReducedRelationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let hker : LinearMap.ker root ≤ LinearMap.ker polar :=
    sqdiagReducedRelationRootMap_ker_le_polarToVertical_ker
      (n := n) (a := a) (b := b) (c := c) (d := d)
  ((LinearMap.ker root).liftQ polar hker).comp
    root.quotKerEquivRange.symm.toLinearMap

set_option maxHeartbeats 800000 in
-- Factoring through the root image does not change the polar image.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRootRangeToPolarVertical_range_eq_polarToVertical_range
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      LinearMap.range
        (sqdiagReducedRelationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  let root :=
    sqdiagReducedRelationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let polar :=
    sqdiagReducedRelationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let hker : LinearMap.ker root ≤ LinearMap.ker polar :=
    sqdiagReducedRelationRootMap_ker_le_polarToVertical_ker
      (n := n) (a := a) (b := b) (c := c) (d := d)
  change
    LinearMap.range
        (((LinearMap.ker root).liftQ polar hker).comp
          root.quotKerEquivRange.symm.toLinearMap) =
      LinearMap.range polar
  apply le_antisymm
  · intro φ hφ
    rcases hφ with ⟨R, hRφ⟩
    rcases R.2 with ⟨x, hxR⟩
    refine ⟨x, ?_⟩
    rw [← hRφ]
    have hR : R = ⟨root x, ⟨x, rfl⟩⟩ := by
      apply Subtype.ext
      exact hxR.symm
    rw [hR]
    change
      polar x =
        ((LinearMap.ker root).liftQ polar hker)
          (root.quotKerEquivRange.symm ⟨root x, ⟨x, rfl⟩⟩)
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    simpa using
      (Submodule.liftQ_apply
        (p := LinearMap.ker root) (f := polar) (h := hker) x).symm
  · intro φ hφ
    rcases hφ with ⟨x, hxφ⟩
    refine ⟨⟨root x, ⟨x, rfl⟩⟩, ?_⟩
    rw [← hxφ]
    change
      ((LinearMap.ker root).liftQ polar hker)
          (root.quotKerEquivRange.symm ⟨root x, ⟨x, rfl⟩⟩) =
        polar x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    simpa using
      (Submodule.liftQ_apply
        (p := LinearMap.ker root) (f := polar) (h := hker) x)

set_option maxHeartbeats 800000 in
-- On an element represented by a reduced relation, the induced map is the restricted polar map.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRootRangeToPolarVertical_apply_root
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagReducedRelation n a b c d) :
    sqdiagReducedRelationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ⟨sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x,
          ⟨x, rfl⟩⟩ =
      sqdiagReducedRelationPolarToVertical
        (n := n) (a := a) (b := b) (c := c) (d := d) x := by
  let root :=
    sqdiagReducedRelationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let polar :=
    sqdiagReducedRelationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let hker : LinearMap.ker root ≤ LinearMap.ker polar :=
    sqdiagReducedRelationRootMap_ker_le_polarToVertical_ker
      (n := n) (a := a) (b := b) (c := c) (d := d)
  change
    ((LinearMap.ker root).liftQ polar hker)
        (root.quotKerEquivRange.symm ⟨root x, ⟨x, rfl⟩⟩) =
      polar x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  simpa using
    (Submodule.liftQ_apply
      (p := LinearMap.ker root) (f := polar) (h := hker) x)

@[simp]
theorem sqdiagReducedRelationRootRangeToPolarVertical_apply_root_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagReducedRelation n a b c d)
    (y : sqdiagReducedRelationVertical n a b c d) :
    sqdiagReducedRelationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ⟨sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x,
          ⟨x, rfl⟩⟩ y =
      sqdiagReducedRelationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 := by
  rw [sqdiagReducedRelationRootRangeToPolarVertical_apply_root
    (n := n) (a := a) (b := b) (c := c) (d := d) x]
  rfl

set_option maxHeartbeats 800000 in
-- One half of the desired rank match: the polar image cannot exceed the root image.
set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagReducedRelation_polarRange_le_rootRange
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
      Module.finrank F
        (LinearMap.range
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  rw [← sqdiagReducedRelationRootRangeToPolarVertical_range_eq_polarToVertical_range
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact
    LinearMap.finrank_range_le
      (sqdiagReducedRelationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d))

set_option synthInstance.maxHeartbeats 200000 in
-- The target is a kernel into the dual of the nested vertical subtype.
theorem sqdiagReducedRelationVertical_le_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n] :
    sqdiagReducedRelationVertical n a b c d ≤
      sqdiagReducedRelationVerticalOrthogonal n a b c d := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change
    sqdiagReducedRelationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 = 0
  exact sqdiagReducedRelationPolar_eq_zero_of_mem_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 hx y.2

set_option synthInstance.maxHeartbeats 200000 in
-- Equal dimension turns the already-proved vertical inclusion into equality.
theorem sqdiagReducedRelationVerticalOrthogonal_le_vertical_of_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d)) :
    sqdiagReducedRelationVerticalOrthogonal n a b c d ≤
      sqdiagReducedRelationVertical n a b c d := by
  have hEq :
      sqdiagReducedRelationVertical n a b c d =
        sqdiagReducedRelationVerticalOrthogonal n a b c d := by
    refine
      Submodule.eq_of_le_of_finrank_eq
        (S₁ := sqdiagReducedRelationVertical n a b c d)
        (S₂ := sqdiagReducedRelationVerticalOrthogonal n a b c d) ?_ ?_
    · exact sqdiagReducedRelationVertical_le_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d)
    · exact hfin.symm
  intro x hx
  rw [hEq]
  exact hx

set_option synthInstance.maxHeartbeats 200000 in
-- Reduced phase vanishes once the vertical orthogonal has no larger dimension.
theorem sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ x = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_mem_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d) x
    (sqdiagReducedRelationVerticalOrthogonal_le_vertical_of_finrank_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) hfin hx)

set_option synthInstance.maxHeartbeats 200000 in
-- Rank-nullity for the reduced polar map over nested reduced-relation subtypes.
theorem finrank_sqdiagReducedRelation_eq_verticalOrthogonal_add_polarRange
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagReducedRelation n a b c d) =
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationPolarToVertical
              (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  let f :=
    sqdiagReducedRelationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h :=
    LinearMap.finrank_range_add_finrank_ker f
  change
    Module.finrank F (SqdiagReducedRelation n a b c d) =
      Module.finrank F (LinearMap.ker f) +
      Module.finrank F (LinearMap.range f)
  exact h.symm.trans (Nat.add_comm _ _)

set_option synthInstance.maxHeartbeats 500000 in
-- Rank-nullity for the reduced root map identifies the vertical kernel term.
theorem finrank_sqdiagReducedRelation_eq_vertical_add_rootRange
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagReducedRelation n a b c d) =
      Module.finrank F (sqdiagReducedRelationVertical n a b c d) +
        Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  let f :=
    sqdiagReducedRelationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h :=
    LinearMap.finrank_range_add_finrank_ker f
  change
    Module.finrank F (SqdiagReducedRelation n a b c d) =
      Module.finrank F (LinearMap.ker f) +
      Module.finrank F (LinearMap.range f)
  exact h.symm.trans (Nat.add_comm _ _)

abbrev sqdiagReducedRelationPolarRootRankMatch
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F
      (LinearMap.range
        (sqdiagReducedRelationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d))) =
    Module.finrank F
      (LinearMap.range
        (sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)))

abbrev sqdiagReducedRelationRootRankLePolarRank
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F
      (LinearMap.range
        (sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
    Module.finrank F
      (LinearMap.range
        (sqdiagReducedRelationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))

set_option synthInstance.maxHeartbeats 500000 in
-- Equal root and polar image ranks turn the reduced phase condition into a dimension statement.
theorem sqdiagReducedRelationVerticalOrthogonal_finrank_eq_vertical_of_polarRange_finrank_eq_rootRange
    {n a b c d : ℕ} [NeZero n]
    (hrange :
      Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationPolarToVertical
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))) :
    Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
      Module.finrank F (sqdiagReducedRelationVertical n a b c d) := by
  have hpolar :=
    finrank_sqdiagReducedRelation_eq_verticalOrthogonal_add_polarRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hroot :=
    finrank_sqdiagReducedRelation_eq_vertical_add_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  omega

set_option synthInstance.maxHeartbeats 500000 in
-- The reduced Q-form vanishes when the polar image and root image have the same rank.
theorem sqdiagReducedRelationQ_eq_zero_of_polarRange_finrank_eq_rootRange
    {n a b c d : ℕ} [NeZero n]
    (hrange :
      Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationPolarToVertical
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d))))
    (z : SqdiagReducedRelation n a b c d)
    (hz : z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ z = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_finrank_eq
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRelationVerticalOrthogonal_finrank_eq_vertical_of_polarRange_finrank_eq_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hrange)
    z hz

set_option maxHeartbeats 800000 in
-- The remaining phase-rank task is the reverse inequality.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationPolarRootRankMatch_of_rootRange_finrank_le_polarRange
    {n a b c d : ℕ} [NeZero n]
    (hle :
      Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
        Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationPolarToVertical
              (n := n) (a := a) (b := b) (c := c) (d := d)))) :
    sqdiagReducedRelationPolarRootRankMatch n a b c d := by
  exact
    le_antisymm
      (finrank_sqdiagReducedRelation_polarRange_le_rootRange
        (n := n) (a := a) (b := b) (c := c) (d := d))
      hle

set_option maxHeartbeats 800000 in
-- The reverse rank inequality is enough to make the reduced Q-form vanish on the orthogonal.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationQ_eq_zero_of_rootRange_finrank_le_polarRange
    {n a b c d : ℕ} [NeZero n]
    (hle :
      Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
        Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationPolarToVertical
              (n := n) (a := a) (b := b) (c := c) (d := d))))
    (z : SqdiagReducedRelation n a b c d)
    (hz : z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ z = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_polarRange_finrank_eq_rootRange
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRelationPolarRootRankMatch_of_rootRange_finrank_le_polarRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hle)
    z hz

set_option maxHeartbeats 800000 in
-- It is enough to show that the induced map from root image to vertical dual is injective.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
    {n a b c d : ℕ} [NeZero n]
    (hinj :
      Function.Injective
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRootRankLePolarRank n a b c d := by
  change
    Module.finrank F
        (LinearMap.range
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
      Module.finrank F
        (LinearMap.range
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)))
  rw [← sqdiagReducedRelationRootRangeToPolarVertical_range_eq_polarToVertical_range
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact
    le_of_eq
      (LinearMap.finrank_range_of_inj hinj).symm

set_option maxHeartbeats 800000 in
-- Injectivity of the induced root-to-polar map makes the reduced Q-form vanish on the orthogonal.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationQ_eq_zero_of_rootRangeToPolarVertical_injective
    {n a b c d : ℕ} [NeZero n]
    (hinj :
      Function.Injective
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (z : SqdiagReducedRelation n a b c d)
    (hz : z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ z = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_rootRange_finrank_le_polarRange
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRelationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
      (n := n) (a := a) (b := b) (c := c) (d := d) hinj)
    z hz

set_option maxHeartbeats 800000 in
-- Equivalently, injectivity is the reverse kernel inclusion for the factored polar map.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRootRangeToPolarVertical_injective_of_polarToVertical_ker_le_rootMap_ker
    {n a b c d : ℕ} [NeZero n]
    (hker :
      LinearMap.ker
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    Function.Injective
      (sqdiagReducedRelationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  let root :=
    sqdiagReducedRelationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let polar :=
    sqdiagReducedRelationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let f :=
    sqdiagReducedRelationRootRangeToPolarVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hfker : LinearMap.ker f = ⊥ := by
    apply le_antisymm
    · intro R hR
      rcases R.2 with ⟨x, hxR⟩
      have hRrepr : R = ⟨root x, ⟨x, rfl⟩⟩ := by
        apply Subtype.ext
        exact hxR.symm
      have hpolar : polar x = 0 := by
        have hmap0 : f ⟨root x, ⟨x, rfl⟩⟩ = 0 := by
          simpa [hRrepr] using (LinearMap.mem_ker.mp hR)
        simpa [root, polar, f] using
          (sqdiagReducedRelationRootRangeToPolarVertical_apply_root
            (n := n) (a := a) (b := b) (c := c) (d := d) x).symm.trans hmap0
      have hxroot : root x = 0 := by
        exact LinearMap.mem_ker.mp (hker (LinearMap.mem_ker.mpr hpolar))
      have hRzero : R = 0 := by
        apply Subtype.ext
        rw [← hxR]
        exact hxroot
      simpa [hRzero]
    · exact bot_le
  exact LinearMap.ker_eq_bot.mp hfker

set_option maxHeartbeats 800000 in
-- WARNING: reduced root-to-polar injectivity is false in the positive family.
-- Smallest counterexample: n = 2, a = b = c = d = 1. In that model,
-- dim rootRange = 3, rank polar = 2, and dim verticalOrthogonal / vertical = 1,
-- while Q still vanishes on verticalOrthogonal. Production proofs must retain
-- this quotient; the injectivity statements below are diagnostic/conditional.
-- The induced-map injectivity is exactly the missing reverse kernel inclusion.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_polarToVertical_ker_le_rootMap_ker
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      LinearMap.ker
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  constructor
  · intro hinj x hx
    rw [LinearMap.mem_ker] at hx ⊢
    let root :=
      sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
    let f :=
      sqdiagReducedRelationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)
    have hmap0 : f ⟨root x, ⟨x, rfl⟩⟩ = 0 := by
      simpa [f, root] using
        (sqdiagReducedRelationRootRangeToPolarVertical_apply_root
          (n := n) (a := a) (b := b) (c := c) (d := d) x).trans hx
    have hrootRange0 : (⟨root x, ⟨x, rfl⟩⟩ : LinearMap.range root) = 0 := by
      apply hinj
      simpa using hmap0
    exact congrArg Subtype.val hrootRange0
  · intro hker
    exact
      sqdiagReducedRelationRootRangeToPolarVertical_injective_of_polarToVertical_ker_le_rootMap_ker
        (n := n) (a := a) (b := b) (c := c) (d := d) hker

set_option maxHeartbeats 800000 in
-- The same condition expressed directly as a vertical-orthogonal containment.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      sqdiagReducedRelationVerticalOrthogonal n a b c d ≤
        sqdiagReducedRelationVertical n a b c d := by
  simpa [sqdiagReducedRelationVerticalOrthogonal, sqdiagReducedRelationVertical] using
    sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_polarToVertical_ker_le_rootMap_ker
      (n := n) (a := a) (b := b) (c := c) (d := d)

set_option maxHeartbeats 800000 in
-- Since vertical is already contained in its orthogonal, injectivity is equality of the two spaces.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_eq_vertical
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      sqdiagReducedRelationVerticalOrthogonal n a b c d =
        sqdiagReducedRelationVertical n a b c d := by
  constructor
  · intro hinj
    apply le_antisymm
    · exact
        (sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
          (n := n) (a := a) (b := b) (c := c) (d := d)).mp hinj
    · exact
        sqdiagReducedRelationVertical_le_verticalOrthogonal
          (n := n) (a := a) (b := b) (c := c) (d := d)
  · intro hEq
    exact
      (sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
        (n := n) (a := a) (b := b) (c := c) (d := d)).mpr (by
          rw [hEq])

set_option maxHeartbeats 800000 in
-- The existing dimension phase also gives injectivity of the induced root-to-polar map.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRootRangeToPolarVertical_injective_of_verticalOrthogonal_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hfin :
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d)) :
    Function.Injective
      (sqdiagReducedRelationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)) :=
  (sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d)).mpr
    (sqdiagReducedRelationVerticalOrthogonal_le_vertical_of_finrank_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) hfin)

set_option maxHeartbeats 800000 in
-- The reverse kernel inclusion gives the required reverse rank inequality.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationRootRankLePolarRank_of_polarToVertical_ker_le_rootMap_ker
    {n a b c d : ℕ} [NeZero n]
    (hker :
      LinearMap.ker
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagReducedRelationRootRankLePolarRank n a b c d :=
  sqdiagReducedRelationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRelationRootRangeToPolarVertical_injective_of_polarToVertical_ker_le_rootMap_ker
      (n := n) (a := a) (b := b) (c := c) (d := d) hker)

set_option maxHeartbeats 800000 in
-- The same kernel inclusion is enough to make the reduced Q-form vanish on the orthogonal.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRelationQ_eq_zero_of_polarToVertical_ker_le_rootMap_ker
    {n a b c d : ℕ} [NeZero n]
    (hker :
      LinearMap.ker
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (z : SqdiagReducedRelation n a b c d)
    (hz : z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ z = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_rootRange_finrank_le_polarRange
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRelationRootRankLePolarRank_of_polarToVertical_ker_le_rootMap_ker
      (n := n) (a := a) (b := b) (c := c) (d := d) hker)
    z hz

noncomputable def sqdiagBWAAdjointGraphToReducedRelation
    {n a b c d : ℕ} [NeZero n] :
    SqdiagBWAAdjointGraph n a b c d →ₗ[F]
      SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointImageEquivReducedRelation
    (n := n) (a := a) (b := b) (c := c) (d := d)).toLinearMap.comp
    (sqdiagBWAAdjointGraphToAdjointImage
      (n := n) (a := a) (b := b) (c := c) (d := d))

theorem sqdiagBWAAdjointGraphToReducedRelation_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagBWAAdjointGraphToReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro y
  rcases sqdiagBWAAdjointGraphToAdjointImage_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ((sqdiagAdjointImageEquivReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d)).symm y) with
    ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa [sqdiagBWAAdjointGraphToReducedRelation] using
    congrArg
      (fun z : SqdiagBWZAdjointImage n a b c d =>
        (sqdiagAdjointImageEquivReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d)) z)
      hx

@[simp]
theorem sqdiagReducedRelationRootMap_graphToReduced_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) x)).1 =
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 := rfl

theorem sqdiagBWAAdjointGraphToReducedRelation_mem_vertical_of_mem_rootZero
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphRootZero n a b c d) :
    sqdiagBWAAdjointGraphToReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
      sqdiagReducedRelationVertical n a b c d := by
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 = 0
  exact LinearMap.mem_ker.mp hx

set_option synthInstance.maxHeartbeats 200000 in
-- The codomain is the vertical kernel subtype of the reduced relation.
noncomputable def sqdiagBWAAdjointGraphRootZeroToReducedVertical
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphRootZero n a b c d →ₗ[F]
      sqdiagReducedRelationVertical n a b c d where
  toFun x :=
    ⟨sqdiagBWAAdjointGraphToReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1,
      sqdiagBWAAdjointGraphToReducedRelation_mem_vertical_of_mem_rootZero
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagBWAAdjointGraphToReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagBWAAdjointGraphToReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1

theorem sqdiagBWAAdjointGraphRootZeroToReducedVertical_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagBWAAdjointGraphRootZeroToReducedVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro v
  rcases sqdiagBWAAdjointGraphToReducedRelation_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) v.1 with
    ⟨x, hx⟩
  have hrootVal :
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 = 0 := by
    have hmapRoot :=
      congrArg
        (sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d))
        hx
    have hmapRootVal := congrArg Subtype.val hmapRoot
    have hvRootVal :=
      congrArg Subtype.val (LinearMap.mem_ker.mp v.2)
    exact hmapRootVal.trans hvRootVal
  let x0 : sqdiagBWAAdjointGraphRootZero n a b c d :=
    ⟨x, LinearMap.mem_ker.mpr (by
      change K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 = 0
      exact hrootVal)⟩
  refine ⟨x0, ?_⟩
  apply Subtype.ext
  exact hx

set_option synthInstance.maxHeartbeats 200000 in
-- The reduced vertical coefficient projection keeps only the KC-adjoint range coordinate.
noncomputable def sqdiagReducedRelationVerticalCoeffMap
    {n a b c d : ℕ} [NeZero n] :
    sqdiagReducedRelationVertical n a b c d →ₗ[F]
      ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) :=
  (sqdiagReducedRelationCoeffMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRelationVertical n a b c d).subtype

noncomputable def sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →ₗ[F]
      ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) where
  toFun A :=
    ⟨sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d) A.1,
      ⟨A.1, rfl⟩⟩
  map_add' A B := by
    apply Subtype.ext
    exact
      (sqdiagKCAdjointMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add A.1 B.1
  map_smul' r A := by
    apply Subtype.ext
    exact
      (sqdiagKCAdjointMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r A.1

@[simp]
theorem sqdiagReducedRelationVerticalCoeffMap_rootZeroToReducedVertical_apply
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWAAdjointGraphRootZero n a b c d) :
    sqdiagReducedRelationVerticalCoeffMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagBWAAdjointGraphRootZeroToReducedVertical
          (n := n) (a := a) (b := b) (c := c) (d := d) x) =
      sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ⟨sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1,
          ⟨x, rfl⟩⟩ := by
  apply Subtype.ext
  have hxGraph :
      sqdiagBWAAdjointGraphPred
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 :=
    (sqdiagBWAAdjointGraphSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1).mp x.1.2
  change
    (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1.1).2 =
      sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagBWAAdjointGraphAMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1)
  simpa [SquareCombined, sqdiagCPhaseCoeff, sqdiagKCAdjointMap_apply] using hxGraph.2

set_option synthInstance.maxHeartbeats 200000 in
-- The root-zero graph A-coefficients, after KC-adjoint, give exactly the reduced vertical coefficient image.
theorem sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap_range_eq_reducedRelationVerticalCoeffMap_range
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      LinearMap.range
        (sqdiagReducedRelationVerticalCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  apply le_antisymm
  · intro C hC
    rcases hC with ⟨A, hA⟩
    rcases A.2 with ⟨x, hxA⟩
    have hArepr :
        A =
          ⟨sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1,
            ⟨x, rfl⟩⟩ := by
      apply Subtype.ext
      exact hxA.symm
    refine
      ⟨sqdiagBWAAdjointGraphRootZeroToReducedVertical
        (n := n) (a := a) (b := b) (c := c) (d := d) x, ?_⟩
    rw [← hA, hArepr]
    exact
      (sqdiagReducedRelationVerticalCoeffMap_rootZeroToReducedVertical_apply
        (n := n) (a := a) (b := b) (c := c) (d := d) x)
  · intro C hC
    rcases hC with ⟨v, hv⟩
    rcases sqdiagBWAAdjointGraphRootZeroToReducedVertical_surjective
        (n := n) (a := a) (b := b) (c := c) (d := d) v with
      ⟨x, hx⟩
    refine
      ⟨⟨sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1,
          ⟨x, rfl⟩⟩, ?_⟩
    rw [← hv, ← hx]
    exact
      (sqdiagReducedRelationVerticalCoeffMap_rootZeroToReducedVertical_apply
        (n := n) (a := a) (b := b) (c := c) (d := d) x).symm

set_option synthInstance.maxHeartbeats 500000 in
-- Reduced vertical-orthogonality means annihilating the root-zero graph A-coefficient space.
theorem sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace
    {n a b c d : ℕ} [NeZero n]
    (z : SqdiagReducedRelation n a b c d) :
    z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d ↔
      ∀ A : RootTarget n b c d,
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply A z.1.1.1 = 0 := by
  constructor
  · intro hz A hA
    rcases hA with ⟨x, hxA⟩
    let v :=
      sqdiagBWAAdjointGraphRootZeroToReducedVertical
        (n := n) (a := a) (b := b) (c := c) (d := d) x
    have hAeq :
        sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 =
          A := by
      simpa [sqdiagBWAAdjointGraphRootZeroAMap] using hxA
    have hzero :
        sqdiagReducedRelationPolar
            (n := n) (a := a) (b := b) (c := c) (d := d) z v.1 = 0 := by
      have hzDual := LinearMap.mem_ker.mp hz
      have happ :=
        congrArg
          (fun T : Module.Dual F (sqdiagReducedRelationVertical n a b c d) => T v)
          hzDual
      simpa [sqdiagReducedRelationPolarToVertical] using happ
    have hcoeff :
        v.1.1.2 =
          ⟨sqdiagKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagBWAAdjointGraphAMap
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1),
            ⟨sqdiagBWAAdjointGraphAMap
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1, rfl⟩⟩ := by
      exact
        sqdiagReducedRelationVerticalCoeffMap_rootZeroToReducedVertical_apply
          (n := n) (a := a) (b := b) (c := c) (d := d) x
    have hpolar :=
      sqdiagReducedRelationPolar_eq_rootCoeffApply_of_right_vertical_coeff_eq
        (n := n) (a := a) (b := b) (c := c) (d := d) z v.1 v.2
        (sqdiagBWAAdjointGraphAMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1)
        hcoeff
    have hrootCoeff :
        sqdiagRootCoeffApply
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1)
            z.1.1.1 = 0 := by
      simpa [hpolar] using hzero
    simpa [hAeq] using hrootCoeff
  · intro hann
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro v
    have hcoeffRange :
        sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d) v ∈
          LinearMap.range
            (sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      rw [sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap_range_eq_reducedRelationVerticalCoeffMap_range
        (n := n) (a := a) (b := b) (c := c) (d := d)]
      exact ⟨v, rfl⟩
    rcases hcoeffRange with ⟨A, hAcoeff⟩
    have hcoeff :
        v.1.1.2 =
          ⟨sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d) A.1,
            ⟨A.1, rfl⟩⟩ := by
      exact hAcoeff.symm
    have hpolar :=
      sqdiagReducedRelationPolar_eq_rootCoeffApply_of_right_vertical_coeff_eq
        (n := n) (a := a) (b := b) (c := c) (d := d) z v.1 v.2 A.1 hcoeff
    have hzero := hann A.1 A.2
    change
      sqdiagReducedRelationPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) z v.1 = 0
    simpa [hpolar] using hzero

set_option synthInstance.maxHeartbeats 500000 in
/--
Conditional diagnostic route only.
Reduced root-to-polar injectivity is false in the positive family. In the
smallest finite model `n = 2`, `a = b = c = d = 1`, the reduced root range has
dimension `3`, the induced polar map has rank `2`, and
`dim verticalOrthogonal / vertical = 1`, although `Q` still vanishes on
`verticalOrthogonal`. Production proofs must retain this quotient instead of
trying to prove separation, `verticalOrthogonal ≤ vertical`, or
`verticalOrthogonal = vertical`.
-/
theorem sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0 := by
  constructor
  · intro hinj z hann
    have hzOrth :
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d :=
      (sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d) z).mpr hann
    have hzVert :
        z ∈ sqdiagReducedRelationVertical n a b c d :=
      (sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
        (n := n) (a := a) (b := b) (c := c) (d := d)).mp hinj hzOrth
    exact congrArg Subtype.val (LinearMap.mem_ker.mp hzVert)
  · intro hsep
    exact
      (sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
        (n := n) (a := a) (b := b) (c := c) (d := d)).mpr (by
          intro z hzOrth
          rw [LinearMap.mem_ker]
          apply Subtype.ext
          exact
            hsep z
              ((sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace
                (n := n) (a := a) (b := b) (c := c) (d := d) z).mp hzOrth))

set_option synthInstance.maxHeartbeats 500000 in
-- Separation by root-zero graph A-coefficients is a direct phase-injectivity certificate.
theorem sqdiagReducedRelationRootRangeToPolarVertical_injective_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0) :
    Function.Injective
      (sqdiagReducedRelationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)) :=
  (sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_rootZeroACoeffSpace_separates_reducedRoot
    (n := n) (a := a) (b := b) (c := c) (d := d)).mpr hsep

set_option synthInstance.maxHeartbeats 500000 in
-- The same separation certificate supplies the reduced reverse root/polar rank inequality.
theorem sqdiagReducedRelationRootRankLePolarRank_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0) :
    sqdiagReducedRelationRootRankLePolarRank n a b c d :=
  sqdiagReducedRelationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRelationRootRangeToPolarVertical_injective_of_rootZeroACoeffSpace_separates_reducedRoot
      (n := n) (a := a) (b := b) (c := c) (d := d) hsep)

set_option synthInstance.maxHeartbeats 500000 in
-- The separated reduced model has vanishing Q on the reduced vertical orthogonal.
theorem sqdiagReducedRelationQ_eq_zero_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (z : SqdiagReducedRelation n a b c d)
    (hz : z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ z = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_rootRangeToPolarVertical_injective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRelationRootRangeToPolarVertical_injective_of_rootZeroACoeffSpace_separates_reducedRoot
      (n := n) (a := a) (b := b) (c := c) (d := d) hsep)
    z hz

theorem sqdiagBWAAdjointGraphQ_eq_reducedRelationQ
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d) :
    sqdiagBWAAdjointGraphQ x =
      sqdiagReducedRelationQ
        ((sqdiagAdjointImageEquivReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d))
          (sqdiagBWAAdjointGraphToAdjointImage
            (n := n) (a := a) (b := b) (c := c) (d := d) x)) := by
  have hxGraph :
      sqdiagBWAAdjointGraphPred
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 :=
    (sqdiagBWAAdjointGraphSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2
  have hcoeff :
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2 := by
    simpa [sqdiagCPhaseCoeff] using hxGraph.2
  let y : SqdiagReducedRelation n a b c d :=
    ((sqdiagAdjointImageEquivReducedRelation
      (n := n) (a := a) (b := b) (c := c) (d := d))
      (sqdiagBWAAdjointGraphToAdjointImage
        (n := n) (a := a) (b := b) (c := c) (d := d) x))
  have hyCoeff :
      y.1.2 =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2,
          ⟨x.1.2, rfl⟩⟩ := by
    apply Subtype.ext
    change
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
          x.1.1).2 =
        sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2
    simpa [SquareCombined, sqdiagKCAdjointMap_apply] using hcoeff
  have hyRoot :
      y.1.1 =
        ⟨K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1,
          hxGraph.1⟩ := by
    apply Subtype.ext
    change
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
          x.1.1).1 =
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1
    simp [SquareCombined]
  change
    sqdiagBWAAdjointGraphQ x = sqdiagReducedRelationQ y
  rw [sqdiagReducedRelationQ, hyCoeff, hyRoot,
    sqdiagAdjointRangePair_mk_apply
      (n := n) (a := a) (b := b) (c := c) (d := d)]
  simp [sqdiagBWAAdjointGraphQ, sqdiagBWAAdjointGraphRootMap,
    sqdiagBWAAdjointGraphAMap]

theorem sqdiagBWAAdjointGraphQ_eq_reducedRelationQ_toReduced
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d) :
    sqdiagBWAAdjointGraphQ x =
      sqdiagReducedRelationQ
        (sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) x) := by
  simpa [sqdiagBWAAdjointGraphToReducedRelation] using
    sqdiagBWAAdjointGraphQ_eq_reducedRelationQ
      (n := n) (a := a) (b := b) (c := c) (d := d) x

theorem sqdiagBWAAdjointGraphPolar_eq_reducedRelationPolar
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagBWAAdjointGraph n a b c d) :
    sqdiagBWAAdjointGraphPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y =
      sqdiagReducedRelationPolar
        (sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) x)
        (sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) y) := by
  have hxGraph :
      sqdiagBWAAdjointGraphPred
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 :=
    (sqdiagBWAAdjointGraphSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2
  have hyGraph :
      sqdiagBWAAdjointGraphPred
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1 :=
    (sqdiagBWAAdjointGraphSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) y.1).mp y.2
  have hxCoeff :
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2 := by
    simpa [sqdiagCPhaseCoeff] using hxGraph.2
  have hyCoeff :
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1.2 := by
    simpa [sqdiagCPhaseCoeff] using hyGraph.2
  let rx : SqdiagReducedRelation n a b c d :=
    sqdiagBWAAdjointGraphToReducedRelation
      (n := n) (a := a) (b := b) (c := c) (d := d) x
  let ry : SqdiagReducedRelation n a b c d :=
    sqdiagBWAAdjointGraphToReducedRelation
      (n := n) (a := a) (b := b) (c := c) (d := d) y
  have hrxCoeff :
      rx.1.2 =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2,
          ⟨x.1.2, rfl⟩⟩ := by
    apply Subtype.ext
    change
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
          x.1.1).2 =
        sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2
    simpa [SquareCombined, sqdiagKCAdjointMap_apply] using hxCoeff
  have hryCoeff :
      ry.1.2 =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1.2,
          ⟨y.1.2, rfl⟩⟩ := by
    apply Subtype.ext
    change
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
          y.1.1).2 =
        sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1.2
    simpa [SquareCombined, sqdiagKCAdjointMap_apply] using hyCoeff
  have hrxRoot :
      rx.1.1 =
        ⟨K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1,
          hxGraph.1⟩ := by
    apply Subtype.ext
    change
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
          x.1.1).1 =
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1
    simp [SquareCombined]
  have hryRoot :
      ry.1.1 =
        ⟨K_yw (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1,
          hyGraph.1⟩ := by
    apply Subtype.ext
    change
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
          y.1.1).1 =
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1
    simp [SquareCombined]
  change
    sqdiagBWAAdjointGraphPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y =
      sqdiagReducedRelationPolar rx ry
  rw [sqdiagReducedRelationPolar, hrxCoeff, hryCoeff, hrxRoot, hryRoot,
    sqdiagAdjointRangePair_mk_apply
      (n := n) (a := a) (b := b) (c := c) (d := d),
    sqdiagAdjointRangePair_mk_apply
      (n := n) (a := a) (b := b) (c := c) (d := d)]
  rw [sqdiagBWAAdjointGraphPolar_apply]

set_option synthInstance.maxHeartbeats 200000 in
-- The proof quantifies over the vertical kernel subtype and its dual.
theorem sqdiagBWAAdjointGraphToReducedRelation_mem_verticalOrthogonal_of_mem_lagrangian
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphToReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d := by
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro v
  rcases sqdiagBWAAdjointGraphRootZeroToReducedVertical_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) v with
    ⟨y, hy⟩
  have hyVal :
      sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1 =
        v.1 :=
    congrArg Subtype.val hy
  have hgraphZero :
      sqdiagBWAAdjointGraphPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 = 0 := by
    have hxDual := LinearMap.mem_ker.mp hx
    have happ :=
      congrArg
        (fun T : Module.Dual F (sqdiagBWAAdjointGraphRootZero n a b c d) => T y)
        hxDual
    simpa [sqdiagBWAAdjointGraphPolarToRootZero] using happ
  have htransport :=
    sqdiagBWAAdjointGraphPolar_eq_reducedRelationPolar
      (n := n) (a := a) (b := b) (c := c) (d := d) x y.1
  change
    sqdiagReducedRelationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) x) v.1 = 0
  rw [← hyVal, ← htransport]
  exact hgraphZero

set_option synthInstance.maxHeartbeats 200000 in
-- Reduced vertical-orthogonality pulls back to the graph lagrangian.
theorem sqdiagBWAAdjointGraph_mem_lagrangian_of_toReduced_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx :
      sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d := by
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  have hyReduced :
      sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1 ∈
        sqdiagReducedRelationVertical n a b c d :=
    sqdiagBWAAdjointGraphToReducedRelation_mem_vertical_of_mem_rootZero
      (n := n) (a := a) (b := b) (c := c) (d := d) y.1 y.2
  have hxDual := LinearMap.mem_ker.mp hx
  have hred0 :
      sqdiagReducedRelationPolar
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagBWAAdjointGraphToReducedRelation
            (n := n) (a := a) (b := b) (c := c) (d := d) x)
          (sqdiagBWAAdjointGraphToReducedRelation
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1) = 0 := by
    have happ :=
      congrArg
        (fun T : Module.Dual F (sqdiagReducedRelationVertical n a b c d) =>
          T
            ⟨sqdiagBWAAdjointGraphToReducedRelation
                (n := n) (a := a) (b := b) (c := c) (d := d) y.1,
              hyReduced⟩)
        hxDual
    simpa [sqdiagReducedRelationPolarToVertical] using happ
  have htransport :=
    sqdiagBWAAdjointGraphPolar_eq_reducedRelationPolar
      (n := n) (a := a) (b := b) (c := c) (d := d) x y.1
  change
    sqdiagBWAAdjointGraphPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 = 0
  rw [htransport]
  exact hred0

set_option synthInstance.maxHeartbeats 200000 in
-- Restrict the graph-to-reduced map to the graph lagrangian.
noncomputable def sqdiagBWAAdjointGraphLagrangianToReducedVerticalOrthogonal
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphLagrangian n a b c d →ₗ[F]
      sqdiagReducedRelationVerticalOrthogonal n a b c d where
  toFun x :=
    ⟨sqdiagBWAAdjointGraphToReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1,
      sqdiagBWAAdjointGraphToReducedRelation_mem_verticalOrthogonal_of_mem_lagrangian
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagBWAAdjointGraphToReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagBWAAdjointGraphToReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1

theorem sqdiagBWAAdjointGraphLagrangianToReducedVerticalOrthogonal_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagBWAAdjointGraphLagrangianToReducedVerticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro z
  rcases sqdiagBWAAdjointGraphToReducedRelation_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) z.1 with
    ⟨x, hx⟩
  have hxlag :
      x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d :=
    sqdiagBWAAdjointGraph_mem_lagrangian_of_toReduced_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) x (by
        simpa [hx] using z.2)
  let x0 : sqdiagBWAAdjointGraphLagrangian n a b c d := ⟨x, hxlag⟩
  refine ⟨x0, ?_⟩
  apply Subtype.ext
  exact hx

set_option maxHeartbeats 800000 in
-- The restricted lagrangian map has the same kernel as the unrestricted graph-to-reduced map.
set_option synthInstance.maxHeartbeats 200000 in
noncomputable def sqdiagBWAAdjointGraphLagrangianToReducedVerticalOrthogonalKerEquivGraphToReducedKer
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWAAdjointGraphLagrangianToReducedVerticalOrthogonal
          (n := n) (a := a) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    LinearMap.ker
        (sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d)) where
  toFun x := by
    refine ⟨x.1.1, ?_⟩
    have hmap := congrArg Subtype.val (LinearMap.mem_ker.mp x.2)
    exact hmap
  invFun x := by
    have hsum :
        sqdiagBWAAdjointGraphToReducedRelation
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 =
          0 :=
      LinearMap.mem_ker.mp x.2
    have hxlag :
        x.1 ∈ sqdiagBWAAdjointGraphLagrangian n a b c d :=
      sqdiagBWAAdjointGraph_mem_lagrangian_of_toReduced_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 (by
          rw [hsum]
          exact
            (sqdiagReducedRelationVerticalOrthogonal n a b c d).zero_mem)
    let x0 : sqdiagBWAAdjointGraphLagrangian n a b c d := ⟨x.1, hxlag⟩
    refine ⟨x0, ?_⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact hsum
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

noncomputable def sqdiagBWAAdjointGraphToReducedRelationKerEquivAdjointImageKer
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    LinearMap.ker
        (sqdiagBWAAdjointGraphToAdjointImage
          (n := n) (a := a) (b := b) (c := c) (d := d)) where
  toFun x := by
    refine ⟨x.1, ?_⟩
    have hred := LinearMap.mem_ker.mp x.2
    change
      (sqdiagAdjointImageEquivReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d))
        (sqdiagBWAAdjointGraphToAdjointImage
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1) = 0
      at hred
    exact
      (sqdiagAdjointImageEquivReducedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d)).injective hred
  invFun x := by
    refine ⟨x.1, ?_⟩
    have hadj := LinearMap.mem_ker.mp x.2
    rw [LinearMap.mem_ker]
    change
      (sqdiagAdjointImageEquivReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d))
        (sqdiagBWAAdjointGraphToAdjointImage
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1) = 0
    rw [hadj]
    rfl
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

set_option maxHeartbeats 800000 in
-- Rank-nullity for the graph lagrangian over the reduced vertical-orthogonal model.
set_option synthInstance.maxHeartbeats 200000 in
theorem finrank_sqdiagBWAAdjointGraphLagrangian_eq_reducedRelationVerticalOrthogonal_add_kernels
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) =
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        Module.finrank F (SquareCombinedKernel n a b c d) +
        Module.finrank F
          (LinearMap.ker
            (sqdiagKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  let f :=
    sqdiagBWAAdjointGraphLagrangianToReducedVerticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hrange :
      Module.finrank F (LinearMap.range f) =
        Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) := by
    have htop : LinearMap.range f = ⊤ :=
      LinearMap.range_eq_top.mpr
        (sqdiagBWAAdjointGraphLagrangianToReducedVerticalOrthogonal_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d))
    rw [htop, finrank_top]
  have hker :
      Module.finrank F (LinearMap.ker f) =
        Module.finrank F (SquareCombinedKernel n a b c d) +
          Module.finrank F
            (LinearMap.ker
              (sqdiagKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d))) := by
    calc
      Module.finrank F (LinearMap.ker f) =
          Module.finrank F
            (LinearMap.ker
              (sqdiagBWAAdjointGraphToReducedRelation
                (n := n) (a := a) (b := b) (c := c) (d := d))) := by
            exact LinearEquiv.finrank_eq
              (sqdiagBWAAdjointGraphLagrangianToReducedVerticalOrthogonalKerEquivGraphToReducedKer
                (n := n) (a := a) (b := b) (c := c) (d := d))
      _ =
          Module.finrank F
            (LinearMap.ker
              (sqdiagBWAAdjointGraphToAdjointImage
                (n := n) (a := a) (b := b) (c := c) (d := d))) := by
            exact LinearEquiv.finrank_eq
              (sqdiagBWAAdjointGraphToReducedRelationKerEquivAdjointImageKer
                (n := n) (a := a) (b := b) (c := c) (d := d))
      _ =
          Module.finrank F
              (SquareCombinedKernel n a b c d ×
                LinearMap.ker
                  (sqdiagKCAdjointMap
                    (n := n) (a := a) (b := b) (c := c) (d := d))) := by
            exact LinearEquiv.finrank_eq
              (sqdiagBWAAdjointGraphToAdjointImageKerEquiv
                (n := n) (a := a) (b := b) (c := c) (d := d))
      _ =
          Module.finrank F (SquareCombinedKernel n a b c d) +
            Module.finrank F
              (LinearMap.ker
                (sqdiagKCAdjointMap
                  (n := n) (a := a) (b := b) (c := c) (d := d))):= by
            rw [Module.finrank_prod]
  rw [hrange, hker] at h
  omega

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  rw [sqdiagBWAAdjointGraphQ_eq_reducedRelationQ_toReduced
    (n := n) (a := a) (b := b) (c := c) (d := d) x]
  exact hred _
    (sqdiagBWAAdjointGraphToReducedRelation_mem_verticalOrthogonal_of_mem_lagrangian
      (n := n) (a := a) (b := b) (c := c) (d := d) x hx)

set_option synthInstance.maxHeartbeats 500000 in
-- The production graph phase follows from separation of reduced roots by root-zero graph A-coefficients.
theorem sqdiagBWAAdjointGraphQ_eq_zero_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro z hz
  exact
    sqdiagReducedRelationQ_eq_zero_of_rootZeroACoeffSpace_separates_reducedRoot
      (n := n) (a := a) (b := b) (c := c) (d := d) hsep z hz

noncomputable def sqdiagAdjointPairAdd
    {n a b c d : ℕ} [NeZero n] :
    (↑(LinearMap.range
        (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d))) ×
      ↑(LinearMap.range
        (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d)))) →ₗ[F]
      RootTarget n b c d × CFun4 n a b d where
  toFun x := x.1.1 + x.2.1
  map_add' x y := by
    change
      (x.1.1 + y.1.1) + (x.2.1 + y.2.1) =
        (x.1.1 + x.2.1) + (y.1.1 + y.2.1)
    abel
  map_smul' r x := by
    change r • x.1.1 + r • x.2.1 = r • (x.1.1 + x.2.1)
    rw [smul_add]

noncomputable def sqdiagAdjointPairPresentationSubmodule
    {n a b c d : ℕ} [NeZero n] :
    Submodule F
      (↑(LinearMap.range
          (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d))) ×
        ↑(LinearMap.range
          (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d)))) :=
  (sqdiagZAdjointTargetSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d)).comap
    (sqdiagAdjointPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d))

abbrev SqdiagAdjointPairPresentation
    (n a b c d : ℕ) [NeZero n] :=
  ↑(sqdiagAdjointPairPresentationSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d))

set_option synthInstance.maxHeartbeats 200000 in
-- The map targets the nested reduced relation subtype and starts from two range subtypes.
noncomputable def sqdiagAdjointPairPresentationSum
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointPairPresentation n a b c d →ₗ[F]
      SqdiagReducedRelation n a b c d where
  toFun x :=
    let t : RootTarget n b c d × CFun4 n a b d :=
      sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1
    let htarget :
        t.1 ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
          ∃ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              t.2 :=
      (sqdiagZAdjointTargetSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) t).mp x.2
    let hrange :
        t ∈ LinearMap.range
          (SquareCombined
            (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      rw [range_SquareCombined_eq_sup_range_B_W]
      exact Submodule.mem_sup.mpr
        ⟨x.1.1.1, x.1.1.2, x.1.2.1, x.1.2.2, by
          simp [t, sqdiagAdjointPairAdd]⟩
    ⟨(⟨t.1, htarget.1⟩, ⟨t.2, htarget.2⟩), hrange⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact
        congrArg Prod.fst
          ((sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1)
    · apply Subtype.ext
      exact
        congrArg Prod.snd
          ((sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1)
  map_smul' r x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact
        congrArg Prod.fst
          ((sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1)
    · apply Subtype.ext
      exact
        congrArg Prod.snd
          ((sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1)

set_option synthInstance.maxHeartbeats 200000 in
-- The proof opens a `range SquareCombined = range B ⊔ range W` witness and rebuilds subtypes.
theorem sqdiagAdjointPairPresentationSum_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro x
  have hcombined :
      (x.1.1.1, x.1.2.1) ∈
        LinearMap.range
          (SquareCombined
            (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    exact x.2
  have hsup :
      (x.1.1.1, x.1.2.1) ∈
        LinearMap.range
            (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d)) ⊔
          LinearMap.range
            (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    simpa [range_SquareCombined_eq_sup_range_B_W] using hcombined
  rcases Submodule.mem_sup.mp hsup with ⟨uB, huB, uW, huW, hsum⟩
  let p :
      ↑(LinearMap.range
          (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d))) ×
        ↑(LinearMap.range
          (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d))) :=
    (⟨uB, huB⟩, ⟨uW, huW⟩)
  have hp :
      p ∈ sqdiagAdjointPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
    have htarget :
        (x.1.1.1, x.1.2.1) ∈
          sqdiagZAdjointTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d) := by
      apply (sqdiagZAdjointTargetSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (x.1.1.1, x.1.2.1)).mpr
      exact ⟨x.1.1.2, x.1.2.2⟩
    change
      sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) p ∈
        sqdiagZAdjointTargetSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d)
    simpa [p, sqdiagAdjointPairAdd, hsum] using htarget
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    simpa [sqdiagAdjointPairPresentationSum, p, sqdiagAdjointPairAdd] using
      congrArg Prod.fst hsum
  · apply Subtype.ext
    simpa [sqdiagAdjointPairPresentationSum, p, sqdiagAdjointPairAdd] using
      congrArg Prod.snd hsum

@[simp]
theorem sqdiagAdjointPairPresentationSum_root_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d) :
    (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x).1.1.1 =
      (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := rfl

@[simp]
theorem sqdiagAdjointPairPresentationSum_coeff_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d) :
    (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x).1.2.1 =
      (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 := rfl

theorem sqdiagAdjointPairPresentationSum_ker_pairAdd_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (x : LinearMap.ker
      (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 = 0 := by
  have hx := LinearMap.mem_ker.mp x.2
  have hval := congrArg Subtype.val hx
  apply Prod.ext
  · have hroot := congrArg Subtype.val (congrArg Prod.fst hval)
    rw [sqdiagAdjointPairPresentationSum_root_apply] at hroot
    simpa [sqdiagAdjointPairAdd] using hroot
  · have hcoeff := congrArg Subtype.val (congrArg Prod.snd hval)
    rw [sqdiagAdjointPairPresentationSum_coeff_apply] at hcoeff
    simpa [sqdiagAdjointPairAdd] using hcoeff

set_option synthInstance.maxHeartbeats 200000 in
-- The equivalence compares a kernel over pair-presentation subtypes with the existing B/W intersection.
noncomputable def sqdiagAdjointPairPresentationKerEquivSquareBWIntersection
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    SquareBWIntersection n a b c d where
  toFun x :=
    let hpair :
        x.1.1.1.1 + x.1.1.2.1 = 0 :=
      sqdiagAdjointPairPresentationSum_ker_pairAdd_eq_zero
        (n := n) (a := a) (b := b) (c := c) (d := d) x
    let heq : x.1.1.1.1 = x.1.1.2.1 :=
      (add_eq_zero_iff_eq_of_F_module _ _).mp hpair
    ⟨x.1.1.1.1,
      ⟨x.1.1.1.2, by
        rw [heq]
        exact x.1.1.2.2⟩⟩
  invFun x :=
    let p :
        ↑(LinearMap.range
            (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d))) ×
          ↑(LinearMap.range
            (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d))) :=
      (⟨x.1, x.2.1⟩, ⟨x.1, x.2.2⟩)
    let hsum :
        sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) p = 0 := by
      change x.1 + x.1 = 0
      exact (add_eq_zero_iff_eq_of_F_module x.1 x.1).mpr rfl
    let hp :
        p ∈ sqdiagAdjointPairPresentationSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
      change
        sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) p ∈
          sqdiagZAdjointTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d)
      rw [hsum]
      exact
        (sqdiagZAdjointTargetSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d)).zero_mem
    let xp : SqdiagAdjointPairPresentation n a b c d := ⟨p, hp⟩
    ⟨xp, LinearMap.mem_ker.mpr (by
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        change
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) p).1 = 0
        rw [hsum]
        rfl
      · apply Subtype.ext
        change
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) p).2 = 0
        rw [hsum]
        rfl)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      have hpair :
          x.1.1.1.1 + x.1.1.2.1 = 0 :=
        sqdiagAdjointPairPresentationSum_ker_pairAdd_eq_zero
          (n := n) (a := a) (b := b) (c := c) (d := d) x
      exact (add_eq_zero_iff_eq_of_F_module _ _).mp hpair
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Rank-nullity over the presentation sum uses nested range/kernel subtypes.
theorem finrank_sqdiagAdjointPairPresentation_eq_relation_add_intersection
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagAdjointPairPresentation n a b c d) =
      Module.finrank F (SqdiagReducedRelation n a b c d) +
        Module.finrank F (SquareBWIntersection n a b c d) := by
  let f :=
    sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hrange :
      Module.finrank F (LinearMap.range f) =
        Module.finrank F (SqdiagReducedRelation n a b c d) := by
    have htop : LinearMap.range f = ⊤ :=
      LinearMap.range_eq_top.mpr
        (sqdiagAdjointPairPresentationSum_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d))
    rw [htop, finrank_top]
  have hker :
      Module.finrank F (LinearMap.ker f) =
        Module.finrank F (SquareBWIntersection n a b c d) := by
    exact LinearEquiv.finrank_eq
      (sqdiagAdjointPairPresentationKerEquivSquareBWIntersection
        (n := n) (a := a) (b := b) (c := c) (d := d))
  rw [hrange, hker] at h
  omega

theorem finrank_sqdiagAdjointPairPresentation_add_core_eq_relation_add_square_terms
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F (SqdiagAdjointPairPresentation n a b c d) +
        2 * (n - 1) ^ 3 =
      Module.finrank F (SqdiagReducedRelation n a b c d) +
        ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1)) := by
  have hpair :=
    finrank_sqdiagAdjointPairPresentation_eq_relation_add_intersection
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hI :=
    finrank_SquareBWIntersection_add_core
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd
  omega

set_option synthInstance.maxHeartbeats 200000 in
-- This is the reduced root map pulled back through the pair-presentation sum map.
noncomputable def sqdiagAdjointPairPresentationRootMap
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointPairPresentation n a b c d →ₗ[F]
      ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)) :=
  (sqdiagReducedRelationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d))

set_option synthInstance.maxHeartbeats 200000 in
-- The vertical kernel is formed over the nested pair-presentation subtype.
abbrev sqdiagAdjointPairPresentationVertical
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (SqdiagAdjointPairPresentation n a b c d) :=
  LinearMap.ker
    (sqdiagAdjointPairPresentationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def sqdiagAdjointPairPresentationQ
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d) : F :=
  sqdiagReducedRelationQ
    (sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d) x)

noncomputable def sqdiagAdjointPairPresentationPolar
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagAdjointPairPresentation n a b c d) : F :=
  sqdiagReducedRelationPolar
    (sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d) x)
    (sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d) y)

set_option synthInstance.maxHeartbeats 200000 in
-- Pulling the reduced polar form back along the pair-presentation sum map preserves linearity.
noncomputable def sqdiagAdjointPairPresentationPolarLinear
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointPairPresentation n a b c d →ₗ[F]
      SqdiagAdjointPairPresentation n a b c d →ₗ[F] F where
  toFun x :=
    (sqdiagReducedRelationPolarLinear
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) x)).comp
      (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d))
  map_add' x y := by
    apply LinearMap.ext
    intro z
    have h :=
      congrArg
        (fun L : SqdiagReducedRelation n a b c d →ₗ[F] F =>
          L
            (sqdiagAdjointPairPresentationSum
              (n := n) (a := a) (b := b) (c := c) (d := d) z))
        ((sqdiagReducedRelationPolarLinear
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_add
            (sqdiagAdjointPairPresentationSum
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
            (sqdiagAdjointPairPresentationSum
              (n := n) (a := a) (b := b) (c := c) (d := d) y))
    rw [(sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add]
    exact h
  map_smul' r x := by
    apply LinearMap.ext
    intro z
    have h :=
      congrArg
        (fun L : SqdiagReducedRelation n a b c d →ₗ[F] F =>
          L
            (sqdiagAdjointPairPresentationSum
              (n := n) (a := a) (b := b) (c := c) (d := d) z))
        ((sqdiagReducedRelationPolarLinear
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r
            (sqdiagAdjointPairPresentationSum
              (n := n) (a := a) (b := b) (c := c) (d := d) x))
    rw [(sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul]
    exact h

@[simp]
theorem sqdiagAdjointPairPresentationPolarLinear_apply
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagAdjointPairPresentation n a b c d) :
    sqdiagAdjointPairPresentationPolarLinear
        (n := n) (a := a) (b := b) (c := c) (d := d) x y =
      sqdiagAdjointPairPresentationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The target dual is over the pair-presentation vertical kernel subtype.
noncomputable def sqdiagAdjointPairPresentationPolarToVertical
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointPairPresentation n a b c d →ₗ[F]
      Module.Dual F (sqdiagAdjointPairPresentationVertical n a b c d) where
  toFun x :=
    (sqdiagAdjointPairPresentationPolarLinear
      (n := n) (a := a) (b := b) (c := c) (d := d) x).comp
      (sqdiagAdjointPairPresentationVertical n a b c d).subtype
  map_add' x y := by
    apply LinearMap.ext
    intro z
    have h :=
      congrArg
        (fun L : SqdiagAdjointPairPresentation n a b c d →ₗ[F] F => L z.1)
        ((sqdiagAdjointPairPresentationPolarLinear
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x y)
    exact h
  map_smul' r x := by
    apply LinearMap.ext
    intro z
    have h :=
      congrArg
        (fun L : SqdiagAdjointPairPresentation n a b c d →ₗ[F] F => L z.1)
        ((sqdiagAdjointPairPresentationPolarLinear
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x)
    exact h

set_option synthInstance.maxHeartbeats 200000 in
-- Orthogonality is taken against the pair-presentation vertical kernel.
abbrev sqdiagAdjointPairPresentationVerticalOrthogonal
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (SqdiagAdjointPairPresentation n a b c d) :=
  LinearMap.ker
    (sqdiagAdjointPairPresentationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d))

set_option synthInstance.maxHeartbeats 200000 in
-- Rank-nullity for the pair-presentation polar map over nested subtypes.
theorem finrank_sqdiagAdjointPairPresentation_eq_verticalOrthogonal_add_polarRange
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagAdjointPairPresentation n a b c d) =
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) +
        Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationPolarToVertical
              (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  let f :=
    sqdiagAdjointPairPresentationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h :=
    LinearMap.finrank_range_add_finrank_ker f
  change
    Module.finrank F (SqdiagAdjointPairPresentation n a b c d) =
      Module.finrank F (LinearMap.ker f) +
      Module.finrank F (LinearMap.range f)
  exact h.symm.trans (Nat.add_comm _ _)

set_option synthInstance.maxHeartbeats 500000 in
-- Rank-nullity for the pair-presentation root map identifies the vertical kernel term.
theorem finrank_sqdiagAdjointPairPresentation_eq_vertical_add_rootRange
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagAdjointPairPresentation n a b c d) =
      Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d) +
        Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  let f :=
    sqdiagAdjointPairPresentationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h :=
    LinearMap.finrank_range_add_finrank_ker f
  change
    Module.finrank F (SqdiagAdjointPairPresentation n a b c d) =
      Module.finrank F (LinearMap.ker f) +
        Module.finrank F (LinearMap.range f)
  exact h.symm.trans (Nat.add_comm _ _)

theorem sqdiagAdjointPairPresentationRootMap_range_eq_reducedRelationRootMap_range
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagAdjointPairPresentationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      LinearMap.range
        (sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  apply le_antisymm
  · intro R hR
    rcases hR with ⟨x, hxR⟩
    refine
      ⟨sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x, ?_⟩
    simpa [sqdiagAdjointPairPresentationRootMap] using hxR
  · intro R hR
    rcases hR with ⟨z, hzR⟩
    rcases sqdiagAdjointPairPresentationSum_surjective
        (n := n) (a := a) (b := b) (c := c) (d := d) z with
      ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hzR]
    simpa [sqdiagAdjointPairPresentationRootMap, hx]

theorem finrank_sqdiagAdjointPairPresentation_rootRange_eq_reducedRelation_rootRange
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.range
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  rw [sqdiagAdjointPairPresentationRootMap_range_eq_reducedRelationRootMap_range
    (n := n) (a := a) (b := b) (c := c) (d := d)]

abbrev sqdiagAdjointPairPresentationPolarRootRankMatch
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F
      (LinearMap.range
        (sqdiagAdjointPairPresentationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d))) =
    Module.finrank F
      (LinearMap.range
        (sqdiagAdjointPairPresentationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)))

set_option synthInstance.maxHeartbeats 500000 in
-- Equal root and polar image ranks give the pair-presentation dimension phase certificate.
theorem sqdiagAdjointPairPresentationVerticalOrthogonal_finrank_eq_vertical_of_polarRange_finrank_eq_rootRange
    {n a b c d : ℕ} [NeZero n]
    (hrange :
      Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationPolarToVertical
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))) :
    Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
      Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d) := by
  have hpolar :=
    finrank_sqdiagAdjointPairPresentation_eq_verticalOrthogonal_add_polarRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hroot :=
    finrank_sqdiagAdjointPairPresentation_eq_vertical_add_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  omega

theorem sqdiagAdjointPairPresentationSum_mem_reducedVertical_of_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVertical n a b c d) :
    sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
      sqdiagReducedRelationVertical n a b c d := by
  exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)

theorem sqdiagAdjointPairPresentationPolar_eq_zero_of_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVertical n a b c d)
    (hy : y ∈ sqdiagAdjointPairPresentationVertical n a b c d) :
    sqdiagAdjointPairPresentationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y = 0 := by
  unfold sqdiagAdjointPairPresentationPolar
  exact
    sqdiagReducedRelationPolar_eq_zero_of_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x)
      (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) y)
      (sqdiagAdjointPairPresentationSum_mem_reducedVertical_of_mem_vertical
        (n := n) (a := a) (b := b) (c := c) (d := d) x hx)
      (sqdiagAdjointPairPresentationSum_mem_reducedVertical_of_mem_vertical
        (n := n) (a := a) (b := b) (c := c) (d := d) y hy)

set_option synthInstance.maxHeartbeats 200000 in
-- The pair version has the same nested vertical-dual codomain.
theorem sqdiagAdjointPairPresentationVertical_le_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n] :
    sqdiagAdjointPairPresentationVertical n a b c d ≤
      sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change
    sqdiagAdjointPairPresentationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 = 0
  exact
    sqdiagAdjointPairPresentationPolar_eq_zero_of_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 hx y.2

set_option synthInstance.maxHeartbeats 500000 in
-- Pair verticality is exactly the root-map kernel, so the polar map factors through roots.
theorem sqdiagAdjointPairPresentationRootMap_ker_le_polarToVertical_ker
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagAdjointPairPresentationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
      LinearMap.ker
        (sqdiagAdjointPairPresentationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  exact
    sqdiagAdjointPairPresentationVertical_le_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)

set_option maxHeartbeats 800000 in
-- The pair-presentation induced map from root image to vertical dual.
set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagAdjointPairPresentationRootRangeToPolarVertical
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagAdjointPairPresentationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) →ₗ[F]
      Module.Dual F (sqdiagAdjointPairPresentationVertical n a b c d) :=
  let root :=
    sqdiagAdjointPairPresentationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let polar :=
    sqdiagAdjointPairPresentationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let hker : LinearMap.ker root ≤ LinearMap.ker polar :=
    sqdiagAdjointPairPresentationRootMap_ker_le_polarToVertical_ker
      (n := n) (a := a) (b := b) (c := c) (d := d)
  ((LinearMap.ker root).liftQ polar hker).comp
    root.quotKerEquivRange.symm.toLinearMap

set_option maxHeartbeats 800000 in
-- On representatives, the pair induced map is the restricted pair polar map.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationRootRangeToPolarVertical_apply_root
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d) :
    sqdiagAdjointPairPresentationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ⟨sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x,
          ⟨x, rfl⟩⟩ =
      sqdiagAdjointPairPresentationPolarToVertical
        (n := n) (a := a) (b := b) (c := c) (d := d) x := by
  let root :=
    sqdiagAdjointPairPresentationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let polar :=
    sqdiagAdjointPairPresentationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let hker : LinearMap.ker root ≤ LinearMap.ker polar :=
    sqdiagAdjointPairPresentationRootMap_ker_le_polarToVertical_ker
      (n := n) (a := a) (b := b) (c := c) (d := d)
  change
    ((LinearMap.ker root).liftQ polar hker)
        (root.quotKerEquivRange.symm ⟨root x, ⟨x, rfl⟩⟩) =
      polar x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  simpa using
    (Submodule.liftQ_apply
      (p := LinearMap.ker root) (f := polar) (h := hker) x)

set_option maxHeartbeats 800000 in
-- Factoring through the pair root image preserves the pair polar image.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationRootRangeToPolarVertical_range_eq_polarToVertical_range
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      LinearMap.range
        (sqdiagAdjointPairPresentationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  let root :=
    sqdiagAdjointPairPresentationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let polar :=
    sqdiagAdjointPairPresentationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let hker : LinearMap.ker root ≤ LinearMap.ker polar :=
    sqdiagAdjointPairPresentationRootMap_ker_le_polarToVertical_ker
      (n := n) (a := a) (b := b) (c := c) (d := d)
  change
    LinearMap.range
        (((LinearMap.ker root).liftQ polar hker).comp
          root.quotKerEquivRange.symm.toLinearMap) =
      LinearMap.range polar
  apply le_antisymm
  · intro φ hφ
    rcases hφ with ⟨R, hRφ⟩
    rcases R.2 with ⟨x, hxR⟩
    refine ⟨x, ?_⟩
    rw [← hRφ]
    have hR : R = ⟨root x, ⟨x, rfl⟩⟩ := by
      apply Subtype.ext
      exact hxR.symm
    rw [hR]
    simpa [root, polar] using
      (sqdiagAdjointPairPresentationRootRangeToPolarVertical_apply_root
        (n := n) (a := a) (b := b) (c := c) (d := d) x).symm
  · intro φ hφ
    rcases hφ with ⟨x, hxφ⟩
    refine ⟨⟨root x, ⟨x, rfl⟩⟩, ?_⟩
    rw [← hxφ]
    simpa [root, polar] using
      sqdiagAdjointPairPresentationRootRangeToPolarVertical_apply_root
        (n := n) (a := a) (b := b) (c := c) (d := d) x

@[simp]
theorem sqdiagAdjointPairPresentationRootRangeToPolarVertical_apply_root_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (y : sqdiagAdjointPairPresentationVertical n a b c d) :
    sqdiagAdjointPairPresentationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ⟨sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x,
          ⟨x, rfl⟩⟩ y =
      sqdiagAdjointPairPresentationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 := by
  rw [sqdiagAdjointPairPresentationRootRangeToPolarVertical_apply_root
    (n := n) (a := a) (b := b) (c := c) (d := d) x]
  rfl

set_option maxHeartbeats 800000 in
-- One half of the pair-presentation rank match.
set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagAdjointPairPresentation_polarRange_le_rootRange
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
      Module.finrank F
        (LinearMap.range
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  rw [← sqdiagAdjointPairPresentationRootRangeToPolarVertical_range_eq_polarToVertical_range
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact
    LinearMap.finrank_range_le
      (sqdiagAdjointPairPresentationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d))

abbrev sqdiagAdjointPairPresentationRootRankLePolarRank
    (n a b c d : ℕ) [NeZero n] : Prop :=
  Module.finrank F
      (LinearMap.range
        (sqdiagAdjointPairPresentationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
    Module.finrank F
      (LinearMap.range
        (sqdiagAdjointPairPresentationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))

set_option maxHeartbeats 800000 in
-- The remaining pair phase-rank task is the reverse inequality.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationPolarRootRankMatch_of_rootRange_finrank_le_polarRange
    {n a b c d : ℕ} [NeZero n]
    (hle :
      Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
        Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationPolarToVertical
              (n := n) (a := a) (b := b) (c := c) (d := d)))) :
    sqdiagAdjointPairPresentationPolarRootRankMatch n a b c d := by
  exact
    le_antisymm
      (finrank_sqdiagAdjointPairPresentation_polarRange_le_rootRange
        (n := n) (a := a) (b := b) (c := c) (d := d))
      hle

set_option maxHeartbeats 800000 in
-- Injectivity of the pair induced root-to-polar map gives the reverse rank inequality.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
    {n a b c d : ℕ} [NeZero n]
    (hinj :
      Function.Injective
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d))) :
    sqdiagAdjointPairPresentationRootRankLePolarRank n a b c d := by
  change
    Module.finrank F
        (LinearMap.range
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
      Module.finrank F
        (LinearMap.range
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)))
  rw [← sqdiagAdjointPairPresentationRootRangeToPolarVertical_range_eq_polarToVertical_range
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact
    le_of_eq
      (LinearMap.finrank_range_of_inj hinj).symm

set_option maxHeartbeats 800000 in
-- Pair induced-map injectivity follows from the reverse kernel inclusion.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_of_polarToVertical_ker_le_rootMap_ker
    {n a b c d : ℕ} [NeZero n]
    (hker :
      LinearMap.ker
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    Function.Injective
      (sqdiagAdjointPairPresentationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  let root :=
    sqdiagAdjointPairPresentationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let polar :=
    sqdiagAdjointPairPresentationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let f :=
    sqdiagAdjointPairPresentationRootRangeToPolarVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hfker : LinearMap.ker f = ⊥ := by
    apply le_antisymm
    · intro R hR
      rcases R.2 with ⟨x, hxR⟩
      have hRrepr : R = ⟨root x, ⟨x, rfl⟩⟩ := by
        apply Subtype.ext
        exact hxR.symm
      have hpolar : polar x = 0 := by
        have hmap0 : f ⟨root x, ⟨x, rfl⟩⟩ = 0 := by
          simpa [hRrepr] using (LinearMap.mem_ker.mp hR)
        simpa [root, polar, f] using
          (sqdiagAdjointPairPresentationRootRangeToPolarVertical_apply_root
            (n := n) (a := a) (b := b) (c := c) (d := d) x).symm.trans hmap0
      have hxroot : root x = 0 := by
        exact LinearMap.mem_ker.mp (hker (LinearMap.mem_ker.mpr hpolar))
      have hRzero : R = 0 := by
        apply Subtype.ext
        rw [← hxR]
        exact hxroot
      simpa [hRzero]
    · exact bot_le
  exact LinearMap.ker_eq_bot.mp hfker

set_option maxHeartbeats 800000 in
-- Pair induced-map injectivity is exactly the missing reverse kernel inclusion.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_iff_polarToVertical_ker_le_rootMap_ker
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      LinearMap.ker
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  constructor
  · intro hinj x hx
    rw [LinearMap.mem_ker] at hx ⊢
    let root :=
      sqdiagAdjointPairPresentationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
    let f :=
      sqdiagAdjointPairPresentationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)
    have hmap0 : f ⟨root x, ⟨x, rfl⟩⟩ = 0 := by
      simpa [f, root] using
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical_apply_root
          (n := n) (a := a) (b := b) (c := c) (d := d) x).trans hx
    have hrootRange0 : (⟨root x, ⟨x, rfl⟩⟩ : LinearMap.range root) = 0 := by
      apply hinj
      simpa using hmap0
    exact congrArg Subtype.val hrootRange0
  · intro hker
    exact
      sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_of_polarToVertical_ker_le_rootMap_ker
        (n := n) (a := a) (b := b) (c := c) (d := d) hker

set_option maxHeartbeats 800000 in
-- The same condition expressed directly as pair vertical-orthogonal containment.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d ≤
        sqdiagAdjointPairPresentationVertical n a b c d := by
  simpa [sqdiagAdjointPairPresentationVerticalOrthogonal,
    sqdiagAdjointPairPresentationVertical] using
    sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_iff_polarToVertical_ker_le_rootMap_ker
      (n := n) (a := a) (b := b) (c := c) (d := d)

set_option maxHeartbeats 800000 in
-- Since pair vertical is already contained in its orthogonal, injectivity is equality.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_eq_vertical
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d =
        sqdiagAdjointPairPresentationVertical n a b c d := by
  constructor
  · intro hinj
    apply le_antisymm
    · exact
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
          (n := n) (a := a) (b := b) (c := c) (d := d)).mp hinj
    · exact
        sqdiagAdjointPairPresentationVertical_le_verticalOrthogonal
          (n := n) (a := a) (b := b) (c := c) (d := d)
  · intro hEq
    exact
      (sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
        (n := n) (a := a) (b := b) (c := c) (d := d)).mpr (by
          rw [hEq])

set_option synthInstance.maxHeartbeats 200000 in
-- Equal dimension turns the pair-presentation vertical inclusion into equality.
theorem sqdiagAdjointPairPresentationVerticalOrthogonal_le_vertical_of_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d)) :
    sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d ≤
      sqdiagAdjointPairPresentationVertical n a b c d := by
  have hEq :
      sqdiagAdjointPairPresentationVertical n a b c d =
        sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d := by
    refine
      Submodule.eq_of_le_of_finrank_eq
        (S₁ := sqdiagAdjointPairPresentationVertical n a b c d)
        (S₂ := sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) ?_ ?_
    · exact sqdiagAdjointPairPresentationVertical_le_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d)
    · exact hfin.symm
  intro x hx
  rw [hEq]
  exact hx

set_option maxHeartbeats 800000 in
-- The pair dimension phase also gives injectivity of the induced root-to-polar map.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_of_verticalOrthogonal_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d)) :
    Function.Injective
      (sqdiagAdjointPairPresentationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)) :=
  (sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d)).mpr
    (sqdiagAdjointPairPresentationVerticalOrthogonal_le_vertical_of_finrank_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) hfin)

set_option synthInstance.maxHeartbeats 200000 in
-- The sum map is still surjective after restricting to vertical kernels.
noncomputable def sqdiagAdjointPairPresentationVerticalToReducedVertical
    {n a b c d : ℕ} [NeZero n] :
    sqdiagAdjointPairPresentationVertical n a b c d →ₗ[F]
      sqdiagReducedRelationVertical n a b c d where
  toFun x :=
    ⟨sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1,
      sqdiagAdjointPairPresentationSum_mem_reducedVertical_of_mem_vertical
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1

theorem sqdiagAdjointPairPresentationVerticalToReducedVertical_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagAdjointPairPresentationVerticalToReducedVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro v
  rcases sqdiagAdjointPairPresentationSum_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) v.1 with
    ⟨x, hx⟩
  have hxvert :
      x ∈ sqdiagAdjointPairPresentationVertical n a b c d := by
    rw [LinearMap.mem_ker]
    have hroot :=
      congrArg
        (sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d))
        hx
    exact hroot.trans (LinearMap.mem_ker.mp v.2)
  let x0 : sqdiagAdjointPairPresentationVertical n a b c d := ⟨x, hxvert⟩
  refine ⟨x0, ?_⟩
  apply Subtype.ext
  exact hx

set_option synthInstance.maxHeartbeats 500000 in
-- Pull reduced vertical-dual functionals back along the surjective pair-to-reduced vertical map.
noncomputable def sqdiagReducedVerticalDualToPairVerticalDual
    {n a b c d : ℕ} [NeZero n] :
    Module.Dual F (sqdiagReducedRelationVertical n a b c d) →ₗ[F]
      Module.Dual F (sqdiagAdjointPairPresentationVertical n a b c d) where
  toFun φ :=
    φ.comp
      (sqdiagAdjointPairPresentationVerticalToReducedVertical
        (n := n) (a := a) (b := b) (c := c) (d := d))
  map_add' φ ψ := by
    ext y
    rfl
  map_smul' r φ := by
    ext y
    rfl

set_option synthInstance.maxHeartbeats 500000 in
-- Surjectivity of the vertical map makes the dual pullback injective.
theorem sqdiagReducedVerticalDualToPairVerticalDual_injective
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
      (sqdiagReducedVerticalDualToPairVerticalDual
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro φ ψ hφψ
  ext v
  rcases sqdiagAdjointPairPresentationVerticalToReducedVertical_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) v with
    ⟨u, hu⟩
  have happ := congrArg
    (fun L : Module.Dual F (sqdiagAdjointPairPresentationVertical n a b c d) => L u)
    hφψ
  simpa [sqdiagReducedVerticalDualToPairVerticalDual, hu] using happ

@[simp]
theorem sqdiagReducedVerticalDualToPairVerticalDual_apply_reducedPolar_pairSum
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d) :
    sqdiagReducedVerticalDualToPairVerticalDual
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRelationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagAdjointPairPresentationSum
            (n := n) (a := a) (b := b) (c := c) (d := d) x)) =
      sqdiagAdjointPairPresentationPolarToVertical
        (n := n) (a := a) (b := b) (c := c) (d := d) x := by
  ext y
  rfl

set_option maxHeartbeats 800000 in
-- The pair polar image is the injective pullback of the reduced polar image.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationPolarToVertical_range_eq_map_reducedRelationPolarRange
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagAdjointPairPresentationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      (LinearMap.range
        (sqdiagReducedRelationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d))).map
        (sqdiagReducedVerticalDualToPairVerticalDual
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  let S :=
    sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let redPolar :=
    sqdiagReducedRelationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let pairPolar :=
    sqdiagAdjointPairPresentationPolarToVertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let D :=
    sqdiagReducedVerticalDualToPairVerticalDual
      (n := n) (a := a) (b := b) (c := c) (d := d)
  apply le_antisymm
  · intro φ hφ
    rcases hφ with ⟨x, hxφ⟩
    refine ⟨redPolar (S x), ⟨S x, rfl⟩, ?_⟩
    rw [← hxφ]
    simpa [S, redPolar, pairPolar, D] using
      (sqdiagReducedVerticalDualToPairVerticalDual_apply_reducedPolar_pairSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x).symm
  · intro φ hφ
    rcases hφ with ⟨ψ, hψ, hDψ⟩
    rcases hψ with ⟨z, hzψ⟩
    rcases sqdiagAdjointPairPresentationSum_surjective
        (n := n) (a := a) (b := b) (c := c) (d := d) z with
      ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hDψ, ← hzψ, ← hx]
    simpa [S, redPolar, pairPolar, D] using
      sqdiagReducedVerticalDualToPairVerticalDual_apply_reducedPolar_pairSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x

set_option maxHeartbeats 2000000 in
-- The pair polar image and reduced polar image have the same dimension.
set_option synthInstance.maxHeartbeats 1000000 in
theorem finrank_sqdiagAdjointPairPresentation_polarRange_eq_reducedRelation_polarRange
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.range
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  let D :=
    sqdiagReducedVerticalDualToPairVerticalDual
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let p :=
    LinearMap.range
      (sqdiagReducedRelationPolarToVertical
        (n := n) (a := a) (b := b) (c := c) (d := d))
  have hDinj : Function.Injective D :=
    sqdiagReducedVerticalDualToPairVerticalDual_injective
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hdominj : Function.Injective (D.domRestrict p) := by
    intro φ ψ hφψ
    apply Subtype.ext
    exact hDinj hφψ
  have hfin := LinearMap.finrank_range_of_inj hdominj
  rw [LinearMap.range_domRestrict] at hfin
  rw [sqdiagAdjointPairPresentationPolarToVertical_range_eq_map_reducedRelationPolarRange
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact hfin

set_option maxHeartbeats 800000 in
-- Pair polar/root rank match is the same numerical condition as the reduced one.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationPolarRootRankMatch_iff_reducedRelationPolarRootRankMatch
    {n a b c d : ℕ} [NeZero n] :
    sqdiagAdjointPairPresentationPolarRootRankMatch n a b c d ↔
      sqdiagReducedRelationPolarRootRankMatch n a b c d := by
  have hpolar :=
    finrank_sqdiagAdjointPairPresentation_polarRange_eq_reducedRelation_polarRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hroot :=
    finrank_sqdiagAdjointPairPresentation_rootRange_eq_reducedRelation_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor
  · intro h
    exact hpolar.symm.trans (h.trans hroot)
  · intro h
    exact hpolar.trans (h.trans hroot.symm)

theorem sqdiagAdjointPairPresentationPolarRootRankMatch_of_reducedRelation
    {n a b c d : ℕ} [NeZero n]
    (h : sqdiagReducedRelationPolarRootRankMatch n a b c d) :
    sqdiagAdjointPairPresentationPolarRootRankMatch n a b c d :=
  (sqdiagAdjointPairPresentationPolarRootRankMatch_iff_reducedRelationPolarRootRankMatch
    (n := n) (a := a) (b := b) (c := c) (d := d)).mpr h

theorem sqdiagReducedRelationPolarRootRankMatch_of_pairPresentation
    {n a b c d : ℕ} [NeZero n]
    (h : sqdiagAdjointPairPresentationPolarRootRankMatch n a b c d) :
    sqdiagReducedRelationPolarRootRankMatch n a b c d :=
  (sqdiagAdjointPairPresentationPolarRootRankMatch_iff_reducedRelationPolarRootRankMatch
    (n := n) (a := a) (b := b) (c := c) (d := d)).mp h

set_option maxHeartbeats 800000 in
-- Pair reverse rank inequality is the same numerical condition as the reduced one.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationRootRankLePolarRank_iff_reducedRelationRootRankLePolarRank
    {n a b c d : ℕ} [NeZero n] :
    sqdiagAdjointPairPresentationRootRankLePolarRank n a b c d ↔
      sqdiagReducedRelationRootRankLePolarRank n a b c d := by
  have hpolar :=
    finrank_sqdiagAdjointPairPresentation_polarRange_eq_reducedRelation_polarRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hroot :=
    finrank_sqdiagAdjointPairPresentation_rootRange_eq_reducedRelation_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor
  · intro h
    calc
      Module.finrank F
          (LinearMap.range
            (sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
          Module.finrank F
            (LinearMap.range
              (sqdiagAdjointPairPresentationRootMap
                (n := n) (a := a) (b := b) (c := c) (d := d))) := hroot.symm
      _ ≤ Module.finrank F
            (LinearMap.range
              (sqdiagAdjointPairPresentationPolarToVertical
                (n := n) (a := a) (b := b) (c := c) (d := d))) := h
      _ = Module.finrank F
            (LinearMap.range
              (sqdiagReducedRelationPolarToVertical
                (n := n) (a := a) (b := b) (c := c) (d := d))) := hpolar
  · intro h
    calc
      Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
          Module.finrank F
            (LinearMap.range
              (sqdiagReducedRelationRootMap
                (n := n) (a := a) (b := b) (c := c) (d := d))) := hroot
      _ ≤ Module.finrank F
            (LinearMap.range
              (sqdiagReducedRelationPolarToVertical
                (n := n) (a := a) (b := b) (c := c) (d := d))) := h
      _ = Module.finrank F
            (LinearMap.range
              (sqdiagAdjointPairPresentationPolarToVertical
                (n := n) (a := a) (b := b) (c := c) (d := d))) := hpolar.symm

theorem sqdiagAdjointPairPresentationRootRankLePolarRank_of_reducedRelation
    {n a b c d : ℕ} [NeZero n]
    (h : sqdiagReducedRelationRootRankLePolarRank n a b c d) :
    sqdiagAdjointPairPresentationRootRankLePolarRank n a b c d :=
  (sqdiagAdjointPairPresentationRootRankLePolarRank_iff_reducedRelationRootRankLePolarRank
    (n := n) (a := a) (b := b) (c := c) (d := d)).mpr h

theorem sqdiagReducedRelationRootRankLePolarRank_of_pairPresentation
    {n a b c d : ℕ} [NeZero n]
    (h : sqdiagAdjointPairPresentationRootRankLePolarRank n a b c d) :
    sqdiagReducedRelationRootRankLePolarRank n a b c d :=
  (sqdiagAdjointPairPresentationRootRankLePolarRank_iff_reducedRelationRootRankLePolarRank
    (n := n) (a := a) (b := b) (c := c) (d := d)).mp h

-- WARNING: reduced root-to-polar injectivity is false in the positive family.
-- Smallest counterexample: n = 2, a = b = c = d = 1.
-- In that model, dim rootRange = 3, rank polar = 2, and
-- dim verticalOrthogonal / vertical = 1, while Q still vanishes on
-- verticalOrthogonal. Production proofs must retain this quotient.
set_option maxHeartbeats 800000 in
-- The restricted vertical-sum map has the same kernel as the unrestricted sum map.
set_option synthInstance.maxHeartbeats 200000 in
noncomputable def
    sqdiagAdjointPairPresentationVerticalToReducedVerticalKerEquivPairPresentationKer
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagAdjointPairPresentationVerticalToReducedVertical
          (n := n) (a := a) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    LinearMap.ker
        (sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d)) where
  toFun x := by
    refine ⟨x.1.1, ?_⟩
    exact congrArg Subtype.val (LinearMap.mem_ker.mp x.2)
  invFun x := by
    have hsum :
        sqdiagAdjointPairPresentationSum
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 =
          0 :=
      LinearMap.mem_ker.mp x.2
    have hxvert :
        x.1 ∈ sqdiagAdjointPairPresentationVertical n a b c d := by
      rw [LinearMap.mem_ker]
      change
        sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagAdjointPairPresentationSum
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1) =
          0
      rw [hsum]
      exact
        (sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero
    let x0 : sqdiagAdjointPairPresentationVertical n a b c d := ⟨x.1, hxvert⟩
    refine ⟨x0, ?_⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact hsum
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

set_option maxHeartbeats 800000 in
-- Rank-nullity for the restricted vertical-sum map.
set_option synthInstance.maxHeartbeats 500000 in
theorem finrank_sqdiagAdjointPairPresentationVertical_eq_reducedRelationVertical_add_intersection
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d) =
      Module.finrank F (sqdiagReducedRelationVertical n a b c d) +
        Module.finrank F (SquareBWIntersection n a b c d) := by
  have hpair :=
    finrank_sqdiagAdjointPairPresentation_eq_relation_add_intersection
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hpairRoot :=
    finrank_sqdiagAdjointPairPresentation_eq_vertical_add_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hredRoot :=
    finrank_sqdiagReducedRelation_eq_vertical_add_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hrange :=
    finrank_sqdiagAdjointPairPresentation_rootRange_eq_reducedRelation_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  omega

set_option synthInstance.maxHeartbeats 200000 in
-- Reduced vertical-orthogonality pulls back to pair-presentation vertical-orthogonality.
theorem sqdiagAdjointPairPresentation_mem_verticalOrthogonal_of_sum_mem_reducedVerticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx :
      sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d := by
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  have hyReduced :
      sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1 ∈
        sqdiagReducedRelationVertical n a b c d :=
    sqdiagAdjointPairPresentationSum_mem_reducedVertical_of_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) y.1 y.2
  have hxDual := LinearMap.mem_ker.mp hx
  have happ :=
    congrArg
      (fun T : Module.Dual F (sqdiagReducedRelationVertical n a b c d) =>
        T
          ⟨sqdiagAdjointPairPresentationSum
              (n := n) (a := a) (b := b) (c := c) (d := d) y.1,
            hyReduced⟩)
      hxDual
  simpa [sqdiagAdjointPairPresentationPolarToVertical,
    sqdiagAdjointPairPresentationPolar,
    sqdiagReducedRelationPolarToVertical] using happ

set_option synthInstance.maxHeartbeats 200000 in
-- The sum map preserves vertical orthogonality by surjectivity on the vertical kernels.
theorem sqdiagAdjointPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d := by
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro v
  rcases sqdiagAdjointPairPresentationVerticalToReducedVertical_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) v with
    ⟨y, hy⟩
  have hyVal :
      sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1 =
        v.1 :=
    congrArg Subtype.val hy
  have hxDual := LinearMap.mem_ker.mp hx
  have happ :=
    congrArg
      (fun T : Module.Dual F (sqdiagAdjointPairPresentationVertical n a b c d) =>
        T y)
      hxDual
  change
    sqdiagReducedRelationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) x) v.1 = 0
  rw [← hyVal]
  simpa [sqdiagAdjointPairPresentationPolarToVertical,
    sqdiagAdjointPairPresentationPolar] using happ

theorem sqdiagAdjointPairPresentationQ_eq_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ x = 0 := by
  simpa [sqdiagAdjointPairPresentationQ] using
    hred
      (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x)
      (sqdiagAdjointPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d) x hx)

set_option synthInstance.maxHeartbeats 200000 in
-- Restrict the pair-presentation sum map to the two vertical-orthogonal subspaces.
noncomputable def sqdiagAdjointPairPresentationVerticalOrthogonalToReducedVerticalOrthogonal
    {n a b c d : ℕ} [NeZero n] :
    sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →ₗ[F]
      sqdiagReducedRelationVerticalOrthogonal n a b c d where
  toFun x :=
    ⟨sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1,
      sqdiagAdjointPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1

theorem sqdiagAdjointPairPresentationVerticalOrthogonalToReducedVerticalOrthogonal_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagAdjointPairPresentationVerticalOrthogonalToReducedVerticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro z
  rcases sqdiagAdjointPairPresentationSum_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) z.1 with
    ⟨x, hx⟩
  have hxorth :
      x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d :=
    sqdiagAdjointPairPresentation_mem_verticalOrthogonal_of_sum_mem_reducedVerticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) x (by
        simpa [hx] using z.2)
  let x0 : sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d := ⟨x, hxorth⟩
  refine ⟨x0, ?_⟩
  apply Subtype.ext
  exact hx

set_option maxHeartbeats 800000 in
-- The restricted map has the same kernel as the unrestricted pair-presentation sum map.
set_option synthInstance.maxHeartbeats 200000 in
noncomputable def
    sqdiagAdjointPairPresentationVerticalOrthogonalToReducedVerticalOrthogonalKerEquivPairPresentationKer
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagAdjointPairPresentationVerticalOrthogonalToReducedVerticalOrthogonal
          (n := n) (a := a) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    LinearMap.ker
        (sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d)) where
  toFun x := by
    refine ⟨x.1.1, ?_⟩
    have hmap := congrArg Subtype.val (LinearMap.mem_ker.mp x.2)
    exact hmap
  invFun x := by
    have hsum :
        sqdiagAdjointPairPresentationSum
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 =
          0 :=
      LinearMap.mem_ker.mp x.2
    have hxorth :
        x.1 ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d :=
      sqdiagAdjointPairPresentation_mem_verticalOrthogonal_of_sum_mem_reducedVerticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 (by
          rw [hsum]
          exact
            (sqdiagReducedRelationVerticalOrthogonal n a b c d).zero_mem)
    let x0 : sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d := ⟨x.1, hxorth⟩
    refine ⟨x0, ?_⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact hsum
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

set_option maxHeartbeats 800000 in
-- Rank-nullity for the restricted orthogonal-sum map.
set_option synthInstance.maxHeartbeats 200000 in
theorem finrank_sqdiagAdjointPairPresentationVerticalOrthogonal_eq_reducedRelationVerticalOrthogonal_add_intersection
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) +
        Module.finrank F (SquareBWIntersection n a b c d) := by
  let f :=
    sqdiagAdjointPairPresentationVerticalOrthogonalToReducedVerticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hrange :
      Module.finrank F (LinearMap.range f) =
        Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) := by
    have htop : LinearMap.range f = ⊤ :=
      LinearMap.range_eq_top.mpr
        (sqdiagAdjointPairPresentationVerticalOrthogonalToReducedVerticalOrthogonal_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d))
    rw [htop, finrank_top]
  have hker :
      Module.finrank F (LinearMap.ker f) =
        Module.finrank F (SquareBWIntersection n a b c d) := by
    calc
      Module.finrank F (LinearMap.ker f) =
          Module.finrank F
            (LinearMap.ker
              (sqdiagAdjointPairPresentationSum
                (n := n) (a := a) (b := b) (c := c) (d := d))) := by
            exact LinearEquiv.finrank_eq
              (sqdiagAdjointPairPresentationVerticalOrthogonalToReducedVerticalOrthogonalKerEquivPairPresentationKer
                (n := n) (a := a) (b := b) (c := c) (d := d))
      _ = Module.finrank F (SquareBWIntersection n a b c d) := by
            exact LinearEquiv.finrank_eq
              (sqdiagAdjointPairPresentationKerEquivSquareBWIntersection
                (n := n) (a := a) (b := b) (c := c) (d := d))
  rw [hrange, hker] at h
  omega

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationVerticalOrthogonal_le_vertical_iff_reducedRelationVerticalOrthogonal_le_vertical
    {n a b c d : ℕ} [NeZero n] :
    (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d ≤
        sqdiagAdjointPairPresentationVertical n a b c d) ↔
      sqdiagReducedRelationVerticalOrthogonal n a b c d ≤
        sqdiagReducedRelationVertical n a b c d := by
  constructor
  · intro hpair z hz
    rcases
      sqdiagAdjointPairPresentationVerticalOrthogonalToReducedVerticalOrthogonal_surjective
        (n := n) (a := a) (b := b) (c := c) (d := d) ⟨z, hz⟩ with
      ⟨x, hx⟩
    have hxvert :
        x.1 ∈ sqdiagAdjointPairPresentationVertical n a b c d :=
      hpair x.2
    have hsum :
        sqdiagAdjointPairPresentationSum
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 =
          z :=
      congrArg Subtype.val hx
    rw [LinearMap.mem_ker]
    have hroot := LinearMap.mem_ker.mp hxvert
    rw [← hsum]
    simpa [sqdiagAdjointPairPresentationRootMap] using hroot
  · intro hred x hx
    have hsumOrth :
        sqdiagAdjointPairPresentationSum
            (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d :=
      sqdiagAdjointPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d) x hx
    have hsumVert :
        sqdiagAdjointPairPresentationSum
            (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
          sqdiagReducedRelationVertical n a b c d :=
      hred hsumOrth
    rw [LinearMap.mem_ker]
    simpa [sqdiagAdjointPairPresentationRootMap] using
      LinearMap.mem_ker.mp hsumVert

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationVerticalOrthogonal_eq_vertical_iff_reducedRelationVerticalOrthogonal_eq_vertical
    {n a b c d : ℕ} [NeZero n] :
    sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d =
        sqdiagAdjointPairPresentationVertical n a b c d ↔
      sqdiagReducedRelationVerticalOrthogonal n a b c d =
        sqdiagReducedRelationVertical n a b c d := by
  constructor
  · intro hpairEq
    apply le_antisymm
    · exact
        (sqdiagAdjointPairPresentationVerticalOrthogonal_le_vertical_iff_reducedRelationVerticalOrthogonal_le_vertical
          (n := n) (a := a) (b := b) (c := c) (d := d)).mp (by
            intro x hx
            simpa [hpairEq] using hx)
    · exact
        sqdiagReducedRelationVertical_le_verticalOrthogonal
          (n := n) (a := a) (b := b) (c := c) (d := d)
  · intro hredEq
    apply le_antisymm
    · exact
        (sqdiagAdjointPairPresentationVerticalOrthogonal_le_vertical_iff_reducedRelationVerticalOrthogonal_le_vertical
          (n := n) (a := a) (b := b) (c := c) (d := d)).mpr (by
            intro z hz
            simpa [hredEq] using hz)
    · exact
        sqdiagAdjointPairPresentationVertical_le_verticalOrthogonal
          (n := n) (a := a) (b := b) (c := c) (d := d)

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationVerticalOrthogonal_finrank_eq_vertical_iff_reducedRelationVerticalOrthogonal_finrank_eq_vertical
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d) ↔
      Module.finrank F (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d) := by
  have horth :=
    finrank_sqdiagAdjointPairPresentationVerticalOrthogonal_eq_reducedRelationVerticalOrthogonal_add_intersection
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hvert :=
    finrank_sqdiagAdjointPairPresentationVertical_eq_reducedRelationVertical_add_intersection
      (n := n) (a := a) (b := b) (c := c) (d := d)
  constructor <;> intro h <;> omega

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_iff_reducedRelationRootRangeToPolarVertical_injective
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      Function.Injective
        (sqdiagReducedRelationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [
    sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d),
    sqdiagReducedRelationRootRangeToPolarVertical_injective_iff_verticalOrthogonal_le_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact
    sqdiagAdjointPairPresentationVerticalOrthogonal_le_vertical_iff_reducedRelationVerticalOrthogonal_le_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d)

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero separation also gives pair-presentation root-to-polar injectivity.
theorem sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0) :
    Function.Injective
      (sqdiagAdjointPairPresentationRootRangeToPolarVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)) :=
  (sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_iff_reducedRelationRootRangeToPolarVertical_injective
    (n := n) (a := a) (b := b) (c := c) (d := d)).mpr
    (sqdiagReducedRelationRootRangeToPolarVertical_injective_of_rootZeroACoeffSpace_separates_reducedRoot
      (n := n) (a := a) (b := b) (c := c) (d := d) hsep)

set_option synthInstance.maxHeartbeats 500000 in
-- Root-zero separation supplies the pair-presentation reverse rank inequality.
theorem sqdiagAdjointPairPresentationRootRankLePolarRank_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0) :
    sqdiagAdjointPairPresentationRootRankLePolarRank n a b c d :=
  sqdiagAdjointPairPresentationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_of_rootZeroACoeffSpace_separates_reducedRoot
      (n := n) (a := a) (b := b) (c := c) (d := d) hsep)

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentation_polarToVertical_ker_le_rootMap_ker_iff_reducedRelation_polarToVertical_ker_le_rootMap_ker
    {n a b c d : ℕ} [NeZero n] :
    (LinearMap.ker
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) ↔
      LinearMap.ker
          (sqdiagReducedRelationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagReducedRelationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  simpa [sqdiagAdjointPairPresentationVerticalOrthogonal,
    sqdiagAdjointPairPresentationVertical,
    sqdiagReducedRelationVerticalOrthogonal,
    sqdiagReducedRelationVertical] using
    sqdiagAdjointPairPresentationVerticalOrthogonal_le_vertical_iff_reducedRelationVerticalOrthogonal_le_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiagReducedRelationQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0)
    (z : SqdiagReducedRelation n a b c d)
    (hz : z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ z = 0 := by
  rcases sqdiagAdjointPairPresentationSum_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) z with
    ⟨x, hx⟩
  have hxorth :
      x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d :=
    sqdiagAdjointPairPresentation_mem_verticalOrthogonal_of_sum_mem_reducedVerticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) x (by
        simpa [hx] using hz)
  have hq := hpair x hxorth
  simpa [sqdiagAdjointPairPresentationQ, hx] using hq

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hpair :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointPairPresentationQ x = 0)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro z hz
  exact
    sqdiagReducedRelationQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) hpair z hz

theorem sqdiagAdjointPairPresentationQ_eq_rootCoeffApply_of_coeff_eq
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x =
      sqdiagRootCoeffApply A
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  unfold sqdiagAdjointPairPresentationQ sqdiagReducedRelationQ
  let R : ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)) :=
    (sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d) x).1.1
  have hroot :
      R.1 =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := rfl
  have hcoeff :
      (sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) x).1.2 =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) A,
          ⟨A, rfl⟩⟩ := by
    apply Subtype.ext
    simpa [sqdiagKCAdjointMap_apply] using hA.symm
  rw [hcoeff]
  exact sqdiagAdjointRangePair_mk_apply
    (n := n) (a := a) (b := b) (c := c) (d := d) R A

theorem sqdiagAdjointPairPresentation_exists_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d) :
    ∃ A : RootTarget n b c d,
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 := by
  have htarget :
      (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 ∈
          ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
        ∃ A : RootTarget n b c d,
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) A =
            (sqdiagAdjointPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 :=
    (sqdiagZAdjointTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1)).mp x.2
  exact htarget.2

theorem sqdiagAdjointPairPresentation_exists_Q_rootCoeffApply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d) :
    ∃ A : RootTarget n b c d,
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 ∧
      sqdiagAdjointPairPresentationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x =
        sqdiagRootCoeffApply A
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  rcases sqdiagAdjointPairPresentation_exists_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) x with
    ⟨A, hA⟩
  refine ⟨A, hA, ?_⟩
  exact
    sqdiagAdjointPairPresentationQ_eq_rootCoeffApply_of_coeff_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) x A hA

theorem sqdiagAdjointPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hzero :
      ∀ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
        sqdiagRootCoeffApply A
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  rcases sqdiagAdjointPairPresentation_exists_Q_rootCoeffApply
      (n := n) (a := a) (b := b) (c := c) (d := d) x with
    ⟨A, hA, hq⟩
  rw [hq]
  exact hzero A hA

theorem sqdiagAdjointPairPresentationQ_eq_zero_of_verticalOrthogonal_coeff_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hzero :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply A
              (sqdiagAdjointPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0)
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) x (hzero x hx)

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_coeff_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hzero :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply A
              (sqdiagAdjointPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointPairPresentationQ_eq_zero_of_verticalOrthogonal_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) hzero y hy

theorem sqdiagAdjointPairPresentationPolar_eq_rootCoeffApply_of_coeff_eq
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagAdjointPairPresentation n a b c d)
    (A B : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    (hB :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2) :
    sqdiagAdjointPairPresentationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y =
      sqdiagRootCoeffApply A
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 +
        sqdiagRootCoeffApply B
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  unfold sqdiagAdjointPairPresentationPolar sqdiagReducedRelationPolar
  let Rx : ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)) :=
    (sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d) x).1.1
  let Ry : ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)) :=
    (sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d) y).1.1
  have hxcoeff :
      (sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) x).1.2 =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) A,
          ⟨A, rfl⟩⟩ := by
    apply Subtype.ext
    simpa [sqdiagKCAdjointMap_apply] using hA.symm
  have hycoeff :
      (sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) y).1.2 =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) B,
          ⟨B, rfl⟩⟩ := by
    apply Subtype.ext
    simpa [sqdiagKCAdjointMap_apply] using hB.symm
  rw [hxcoeff, hycoeff]
  rw [sqdiagAdjointRangePair_mk_apply,
    sqdiagAdjointRangePair_mk_apply]
  simp

theorem sqdiagAdjointPairPresentationPolar_eq_zero_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d)
    (y : SqdiagAdjointPairPresentation n a b c d)
    (hy : y ∈ sqdiagAdjointPairPresentationVertical n a b c d) :
    sqdiagAdjointPairPresentationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y = 0 := by
  have hxDual := LinearMap.mem_ker.mp hx
  have happ :=
    congrArg
      (fun T : Module.Dual F (sqdiagAdjointPairPresentationVertical n a b c d) =>
        T ⟨y, hy⟩)
      hxDual
  simpa [sqdiagAdjointPairPresentationPolarToVertical] using happ

theorem sqdiagAdjointPairPresentation_pairAdd_root_eq_zero_of_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVertical n a b c d) :
    (sqdiagAdjointPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 := by
  have hroot := LinearMap.mem_ker.mp hx
  have hrootVal := congrArg Subtype.val hroot
  change
    (sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d) x).1.1.1 = 0
    at hrootVal
  simpa [sqdiagAdjointPairPresentationSum_root_apply] using hrootVal

theorem sqdiagAdjointPairPresentation_mem_vertical_of_pairAdd_root_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hxroot :
      (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0) :
    x ∈ sqdiagAdjointPairPresentationVertical n a b c d := by
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change
    (sqdiagAdjointPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0
  exact hxroot

theorem sqdiagAdjointPairPresentationQ_eq_zero_of_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVertical n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  rcases sqdiagAdjointPairPresentation_exists_Q_rootCoeffApply
      (n := n) (a := a) (b := b) (c := c) (d := d) x with
    ⟨A, _hA, hq⟩
  rw [hq]
  have hroot :=
    sqdiagAdjointPairPresentation_pairAdd_root_eq_zero_of_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) x hx
  simp [hroot, sqdiagRootCoeffApply]

set_option synthInstance.maxHeartbeats 200000 in
-- Pair-presentation phase vanishes once vertical orthogonal and vertical are equal by dimension.
theorem sqdiagAdjointPairPresentationQ_eq_zero_of_verticalOrthogonal_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d))
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointPairPresentationQ_eq_zero_of_mem_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d) x
    (sqdiagAdjointPairPresentationVerticalOrthogonal_le_vertical_of_finrank_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) hfin hx)

set_option synthInstance.maxHeartbeats 500000 in
-- Pair-presentation phase vanishes when polar and root image ranks agree.
theorem sqdiagAdjointPairPresentationQ_eq_zero_of_polarRange_finrank_eq_rootRange
    {n a b c d : ℕ} [NeZero n]
    (hrange :
      Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationPolarToVertical
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d))))
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointPairPresentationQ_eq_zero_of_verticalOrthogonal_finrank_eq
    (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointPairPresentationVerticalOrthogonal_finrank_eq_vertical_of_polarRange_finrank_eq_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hrange)
    x hx

set_option maxHeartbeats 800000 in
-- The reverse pair rank inequality is enough for pair-presentation phase vanishing.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationQ_eq_zero_of_rootRange_finrank_le_polarRange
    {n a b c d : ℕ} [NeZero n]
    (hle : sqdiagAdjointPairPresentationRootRankLePolarRank n a b c d)
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointPairPresentationQ_eq_zero_of_polarRange_finrank_eq_rootRange
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointPairPresentationPolarRootRankMatch_of_rootRange_finrank_le_polarRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hle)
    x hx

set_option maxHeartbeats 800000 in
-- The reduced reverse rank inequality also gives pair-presentation phase vanishing.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationQ_eq_zero_of_reducedRelation_rootRange_finrank_le_polarRange
    {n a b c d : ℕ} [NeZero n]
    (hle : sqdiagReducedRelationRootRankLePolarRank n a b c d)
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointPairPresentationQ_eq_zero_of_rootRange_finrank_le_polarRange
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointPairPresentationRootRankLePolarRank_of_reducedRelation
      (n := n) (a := a) (b := b) (c := c) (d := d) hle)
    x hx

set_option synthInstance.maxHeartbeats 500000 in
-- Pair-presentation phase vanishes from the root-zero reduced separation certificate.
theorem sqdiagAdjointPairPresentationQ_eq_zero_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0)
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointPairPresentationQ_eq_zero_of_rootRange_finrank_le_polarRange
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointPairPresentationRootRankLePolarRank_of_rootZeroACoeffSpace_separates_reducedRoot
      (n := n) (a := a) (b := b) (c := c) (d := d) hsep)
    x hx

set_option maxHeartbeats 800000 in
-- Pair induced-map injectivity is enough for pair-presentation phase vanishing.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationQ_eq_zero_of_rootRangeToPolarVertical_injective
    {n a b c d : ℕ} [NeZero n]
    (hinj :
      Function.Injective
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointPairPresentationQ_eq_zero_of_rootRange_finrank_le_polarRange
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointPairPresentationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
      (n := n) (a := a) (b := b) (c := c) (d := d) hinj)
    x hx

set_option maxHeartbeats 800000 in
-- The reverse pair kernel inclusion is enough for pair-presentation phase vanishing.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagAdjointPairPresentationQ_eq_zero_of_polarToVertical_ker_le_rootMap_ker
    {n a b c d : ℕ} [NeZero n]
    (hker :
      LinearMap.ker
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointPairPresentationQ_eq_zero_of_rootRangeToPolarVertical_injective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_of_polarToVertical_ker_le_rootMap_ker
      (n := n) (a := a) (b := b) (c := c) (d := d) hker)
    x hx

set_option synthInstance.maxHeartbeats 200000 in
-- Graph phase vanishes after transporting the pair-presentation dimension equality.
theorem sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_verticalOrthogonal_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hfin :
      Module.finrank F (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) =
        Module.finrank F (sqdiagAdjointPairPresentationVertical n a b c d))
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointPairPresentationQ_eq_zero_of_verticalOrthogonal_finrank_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) hfin y hy

set_option synthInstance.maxHeartbeats 500000 in
-- Graph phase vanishes when the pair polar and root image ranks agree.
theorem sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_polarRange_finrank_eq_rootRange
    {n a b c d : ℕ} [NeZero n]
    (hrange :
      Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationPolarToVertical
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Module.finrank F
          (LinearMap.range
            (sqdiagAdjointPairPresentationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d))))
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointPairPresentationQ_eq_zero_of_polarRange_finrank_eq_rootRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hrange y hy

set_option maxHeartbeats 800000 in
-- Graph phase vanishes from the pair reverse rank inequality.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_rootRange_finrank_le_polarRange
    {n a b c d : ℕ} [NeZero n]
    (hle : sqdiagAdjointPairPresentationRootRankLePolarRank n a b c d)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointPairPresentationQ_eq_zero_of_rootRange_finrank_le_polarRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hle y hy

set_option maxHeartbeats 800000 in
-- Graph phase vanishes from injectivity of the pair induced root-to-polar map.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_rootRangeToPolarVertical_injective
    {n a b c d : ℕ} [NeZero n]
    (hinj :
      Function.Injective
        (sqdiagAdjointPairPresentationRootRangeToPolarVertical
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 :=
  sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_rootRange_finrank_le_polarRange
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointPairPresentationRootRankLePolarRank_of_rootRangeToPolarVertical_injective
      (n := n) (a := a) (b := b) (c := c) (d := d) hinj)
    x hx

set_option maxHeartbeats 800000 in
-- Graph phase vanishes from the pair reverse kernel inclusion.
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_polarToVertical_ker_le_rootMap_ker
    {n a b c d : ℕ} [NeZero n]
    (hker :
      LinearMap.ker
          (sqdiagAdjointPairPresentationPolarToVertical
            (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
        LinearMap.ker
          (sqdiagAdjointPairPresentationRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 :=
  sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_rootRangeToPolarVertical_injective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointPairPresentationRootRangeToPolarVertical_injective_of_polarToVertical_ker_le_rootMap_ker
      (n := n) (a := a) (b := b) (c := c) (d := d) hker)
    x hx

theorem sqdiagAdjointPairPresentation_rootCoeff_equation_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d)
    (y : SqdiagAdjointPairPresentation n a b c d)
    (hyroot :
      (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0)
    (A B : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    (hB :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2) :
    sqdiagRootCoeffApply A
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 +
        sqdiagRootCoeffApply B
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
      0 := by
  have hpolar :=
    sqdiagAdjointPairPresentationPolar_eq_zero_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) x hx y
      (sqdiagAdjointPairPresentation_mem_vertical_of_pairAdd_root_eq_zero
        (n := n) (a := a) (b := b) (c := c) (d := d) y hyroot)
  rw [sqdiagAdjointPairPresentationPolar_eq_rootCoeffApply_of_coeff_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) x y A B hA hB] at hpolar
  exact hpolar

theorem sqdiagAdjointPairPresentation_exists_rootCoeff_equation_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d)
    (y : SqdiagAdjointPairPresentation n a b c d)
    (hyroot :
      (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0) :
    ∃ A B : RootTarget n b c d,
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 ∧
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
      sqdiagRootCoeffApply A
            (sqdiagAdjointPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 +
          sqdiagRootCoeffApply B
            (sqdiagAdjointPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
        0 := by
  rcases sqdiagAdjointPairPresentation_exists_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) x with
    ⟨A, hA⟩
  rcases sqdiagAdjointPairPresentation_exists_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) y with
    ⟨B, hB⟩
  refine ⟨A, B, hA, hB, ?_⟩
  exact
    sqdiagAdjointPairPresentation_rootCoeff_equation_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x hx y hyroot A B hA hB

theorem sqdiagAdjointPairPresentation_rootCoeff_zero_of_pairing_match_vertical
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    (y : SqdiagAdjointPairPresentation n a b c d)
    (hy : y ∈ sqdiagAdjointPairPresentationVertical n a b c d)
    (B : RootTarget n b c d)
    (hB :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2)
    (hmatch :
      sqdiagRootCoeffApply B
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
        sqdiagRootCoeffApply A
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1) :
    sqdiagRootCoeffApply A
      (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 := by
  have hyroot :
      (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0 :=
    sqdiagAdjointPairPresentation_pairAdd_root_eq_zero_of_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) y hy
  have heq :=
    sqdiagAdjointPairPresentation_rootCoeff_equation_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x hx y hyroot A B hA hB
  have hBzero :
      sqdiagRootCoeffApply B
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 := by
    simpa [hyroot, sqdiagRootCoeffApply] using heq
  exact hmatch ▸ hBzero

theorem sqdiagAdjointPairPresentationQ_eq_zero_of_pairing_match_vertical
    {n a b c d : ℕ} [NeZero n]
    (hmatch :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            ∃ y : SqdiagAdjointPairPresentation n a b c d,
              y ∈ sqdiagAdjointPairPresentationVertical n a b c d ∧
                ∃ B : RootTarget n b c d,
                  sqdiagKCAdjointCoeff
                      (n := n) (a := a) (b := b) (c := c) (d := d) B =
                    (sqdiagAdjointPairAdd
                      (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
                  sqdiagRootCoeffApply B
                      (sqdiagAdjointPairAdd
                        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
                    sqdiagRootCoeffApply A
                      (sqdiagAdjointPairAdd
                        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1)
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  refine
    sqdiagAdjointPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) x ?_
  intro A hA
  rcases hmatch x hx A hA with ⟨y, hy, B, hB, hpair⟩
  exact
    sqdiagAdjointPairPresentation_rootCoeff_zero_of_pairing_match_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x hx A hA y hy B hB hpair

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_pairing_match_vertical
    {n a b c d : ℕ} [NeZero n]
    (hmatch :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            ∃ y : SqdiagAdjointPairPresentation n a b c d,
              y ∈ sqdiagAdjointPairPresentationVertical n a b c d ∧
                ∃ B : RootTarget n b c d,
                  sqdiagKCAdjointCoeff
                      (n := n) (a := a) (b := b) (c := c) (d := d) B =
                    (sqdiagAdjointPairAdd
                      (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
                  sqdiagRootCoeffApply B
                      (sqdiagAdjointPairAdd
                        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
                    sqdiagRootCoeffApply A
                      (sqdiagAdjointPairAdd
                        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointPairPresentationQ_eq_zero_of_pairing_match_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hmatch y hy

theorem sqdiagAdjointPairPresentation_rootCoeff_zero_of_same_coeff_vertical
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    (hlift :
      ∃ y : SqdiagAdjointPairPresentation n a b c d,
        y ∈ sqdiagAdjointPairPresentationVertical n a b c d ∧
          (sqdiagAdjointPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 =
            (sqdiagAdjointPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2) :
    sqdiagRootCoeffApply A
      (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 := by
  rcases hlift with ⟨y, hyvert, hycoeff⟩
  have hpolar0 :
      sqdiagAdjointPairPresentationPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) x y = 0 := by
    have hxDual := LinearMap.mem_ker.mp hx
    have happ :=
      congrArg
        (fun T : Module.Dual F (sqdiagAdjointPairPresentationVertical n a b c d) =>
          T ⟨y, hyvert⟩)
        hxDual
    simpa [sqdiagAdjointPairPresentationPolarToVertical] using happ
  have hyroot :
      (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0 :=
    sqdiagAdjointPairPresentation_pairAdd_root_eq_zero_of_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) y hyvert
  have hyA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 :=
    hA.trans hycoeff.symm
  have hpolar :=
    sqdiagAdjointPairPresentationPolar_eq_rootCoeffApply_of_coeff_eq
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x y A A hA hyA
  rw [hyroot] at hpolar
  simp [sqdiagRootCoeffApply] at hpolar
  exact hpolar.symm.trans hpolar0

/--
Conditional diagnostic route only.
Finite reduced-model checks show the same-coeff vertical-lift premise is false
in the general positive family; it already fails for `n = 3` and
`a = b = c = d = 1`, where the pair-orthogonal coeff image has dimension `16`
but the vertical coeff image has dimension `14`. Production proofs must prove
the root-coefficient vanishing or reduced `Q = 0` statement directly from the
pair/core exactness API.
-/
theorem sqdiagAdjointPairPresentationQ_eq_zero_of_same_coeff_vertical
    {n a b c d : ℕ} [NeZero n]
    (hlift :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            ∃ y : SqdiagAdjointPairPresentation n a b c d,
              y ∈ sqdiagAdjointPairPresentationVertical n a b c d ∧
                (sqdiagAdjointPairAdd
                  (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 =
                  (sqdiagAdjointPairAdd
                    (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  refine
    sqdiagAdjointPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) x ?_
  intro A hA
  exact
    sqdiagAdjointPairPresentation_rootCoeff_zero_of_same_coeff_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x hx A hA (hlift x hx A hA)

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentation_same_coeff_vertical
    {n a b c d : ℕ} [NeZero n]
    (hlift :
      ∀ x : SqdiagAdjointPairPresentation n a b c d,
        x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            ∃ y : SqdiagAdjointPairPresentation n a b c d,
              y ∈ sqdiagAdjointPairPresentationVertical n a b c d ∧
                (sqdiagAdjointPairAdd
                  (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 =
                  (sqdiagAdjointPairAdd
                    (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointPairPresentationQ_eq_zero_of_same_coeff_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hlift y hy

end

end SquareDiagonal
end Core4loop
