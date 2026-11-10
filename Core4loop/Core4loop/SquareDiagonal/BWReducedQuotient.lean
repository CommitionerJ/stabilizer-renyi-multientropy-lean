import Core4loop.SquareDiagonal.BWReducedRelation

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

set_option synthInstance.maxHeartbeats 300000 in
-- This is the nonzero reduced-root defect left by the root-to-polar map.
abbrev sqdiagReducedRelationRootDefect
    (n a b c d : ℕ) [NeZero n] :
    Submodule F
      (LinearMap.range
        (sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) :=
  LinearMap.ker
    (sqdiagReducedRelationRootRangeToPolarVertical
      (n := n) (a := a) (b := b) (c := c) (d := d))

set_option synthInstance.maxHeartbeats 300000 in
-- The map records the reduced root of a vertical-orthogonal relation in the
-- root-defect kernel.
noncomputable def sqdiagReducedRelationVerticalOrthogonalToRootDefect
    {n a b c d : ℕ} [NeZero n] :
    sqdiagReducedRelationVerticalOrthogonal n a b c d →ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d where
  toFun x :=
    ⟨⟨sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1,
        ⟨x.1, rfl⟩⟩,
      by
        rw [LinearMap.mem_ker]
        rw [sqdiagReducedRelationRootRangeToPolarVertical_apply_root
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1]
        exact LinearMap.mem_ker.mp x.2⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1

@[simp]
theorem sqdiagReducedRelationVerticalOrthogonalToRootDefect_apply
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    (sqdiagReducedRelationVerticalOrthogonalToRootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d) x).1.1 =
      sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 := rfl

set_option maxHeartbeats 800000 in
-- The surjectivity proof unfolds nested root-range and defect subtypes.
set_option synthInstance.maxHeartbeats 300000 in
-- Every root-defect vector has a vertical-orthogonal reduced-relation
-- representative by the defining kernel condition.
theorem sqdiagReducedRelationVerticalOrthogonalToRootDefect_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagReducedRelationVerticalOrthogonalToRootDefect
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro R0
  rcases R0.1.2 with ⟨x, hx⟩
  have hxOrth :
      x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d := by
    rw [LinearMap.mem_ker]
    have hzero :=
      LinearMap.mem_ker.mp R0.2
    have hR :
        R0.1 =
          ⟨sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x,
            ⟨x, rfl⟩⟩ := by
      apply Subtype.ext
      exact hx.symm
    change
      sqdiagReducedRelationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d) x = 0
    calc
      sqdiagReducedRelationPolarToVertical
          (n := n) (a := a) (b := b) (c := c) (d := d) x =
          sqdiagReducedRelationRootRangeToPolarVertical
              (n := n) (a := a) (b := b) (c := c) (d := d)
              ⟨sqdiagReducedRelationRootMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) x,
                ⟨x, rfl⟩⟩ := by
            exact
              (sqdiagReducedRelationRootRangeToPolarVertical_apply_root
                (n := n) (a := a) (b := b) (c := c) (d := d) x).symm
      _ =
          sqdiagReducedRelationRootRangeToPolarVertical
              (n := n) (a := a) (b := b) (c := c) (d := d) R0.1 := by
            rw [hR]
      _ = 0 := hzero
  refine ⟨⟨x, hxOrth⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hx

set_option maxHeartbeats 800000 in
-- The kernel equivalence compares nested subtype zeros through projections.
set_option synthInstance.maxHeartbeats 300000 in
-- The kernel of the vertical-orthogonal-to-defect map is exactly the reduced
-- vertical submodule.
noncomputable def
    sqdiagReducedRelationVerticalOrthogonalToRootDefectKerEquivVertical
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
      (sqdiagReducedRelationVerticalOrthogonalToRootDefect
        (n := n) (a := a) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    sqdiagReducedRelationVertical n a b c d where
  toFun x :=
    ⟨x.1.1, by
      rw [LinearMap.mem_ker]
      have hxker :=
        LinearMap.mem_ker.mp x.2
      have hroot :
          sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 = 0 := by
        change
          (sqdiagReducedRelationVerticalOrthogonalToRootDefect
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1.1 =
            (0 : sqdiagReducedRelationRootDefect n a b c d).1.1
        exact congrArg
          (fun R0 : sqdiagReducedRelationRootDefect n a b c d => R0.1.1)
          hxker
      exact hroot⟩
  invFun x :=
    ⟨⟨x.1,
        (sqdiagReducedRelationVertical_le_verticalOrthogonal
          (n := n) (a := a) (b := b) (c := c) (d := d)) x.2⟩,
      by
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        apply Subtype.ext
        exact LinearMap.mem_ker.mp x.2⟩
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
-- Rank-nullity here elaborates over the nested root-defect target.
set_option synthInstance.maxHeartbeats 300000 in
-- Rank-nullity for the quotient exact sequence
-- `0 -> vertical -> verticalOrthogonal -> rootDefect -> 0`.
theorem finrank_sqdiagReducedRelationVerticalOrthogonal_eq_vertical_add_rootDefect
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (sqdiagReducedRelationVerticalOrthogonal n a b c d) =
      Module.finrank F
          (sqdiagReducedRelationVertical n a b c d) +
        Module.finrank F
          (sqdiagReducedRelationRootDefect n a b c d) := by
  let f :=
    sqdiagReducedRelationVerticalOrthogonalToRootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hrange :
      Module.finrank F (LinearMap.range f) =
        Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) := by
    have htop : LinearMap.range f = ⊤ :=
      LinearMap.range_eq_top.mpr
        (sqdiagReducedRelationVerticalOrthogonalToRootDefect_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d))
    exact LinearEquiv.finrank_eq (LinearEquiv.ofTop (LinearMap.range f) htop)
  have hker :
      Module.finrank F (LinearMap.ker f) =
        Module.finrank F (sqdiagReducedRelationVertical n a b c d) := by
    exact LinearEquiv.finrank_eq
      (sqdiagReducedRelationVerticalOrthogonalToRootDefectKerEquivVertical
        (n := n) (a := a) (b := b) (c := c) (d := d))
  have hadd :
      Module.finrank F (LinearMap.range f) +
          Module.finrank F (LinearMap.ker f) =
        Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
          Module.finrank F (sqdiagReducedRelationVertical n a b c d) :=
    congrArg₂ (fun x y : ℕ => x + y) hrange hker
  have h' :
      Module.finrank F (sqdiagReducedRelationRootDefect n a b c d) +
          Module.finrank F (sqdiagReducedRelationVertical n a b c d) =
        Module.finrank F
          (sqdiagReducedRelationVerticalOrthogonal n a b c d) :=
    hadd.symm.trans h
  exact h'.symm.trans
    (Nat.add_comm
      (Module.finrank F (sqdiagReducedRelationRootDefect n a b c d))
      (Module.finrank F (sqdiagReducedRelationVertical n a b c d)))

theorem sqdiagReducedRelationQ_add
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagReducedRelation n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) (x + y) =
      sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x +
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) y +
          sqdiagReducedRelationPolar
            (n := n) (a := a) (b := b) (c := c) (d := d) x y := by
  unfold sqdiagReducedRelationQ sqdiagReducedRelationPolar
  change
    sqdiagAdjointRangePair
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (x.1.1 + y.1.1) (x.1.2 + y.1.2) =
      sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d)
          x.1.1 x.1.2 +
        sqdiagAdjointRangePair
          (n := n) (a := a) (b := b) (c := c) (d := d)
          y.1.1 y.1.2 +
          (sqdiagAdjointRangePair
              (n := n) (a := a) (b := b) (c := c) (d := d)
              y.1.1 x.1.2 +
            sqdiagAdjointRangePair
              (n := n) (a := a) (b := b) (c := c) (d := d)
              x.1.1 y.1.2)
  rw [sqdiagAdjointRangePair_add_root,
    (sqdiagAdjointRangePair
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1).map_add,
    (sqdiagAdjointRangePair
      (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1).map_add]
  abel

@[simp]
theorem sqdiagReducedRelationPolar_self
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagReducedRelation n a b c d) :
    sqdiagReducedRelationPolar
      (n := n) (a := a) (b := b) (c := c) (d := d) x x = 0 := by
  unfold sqdiagReducedRelationPolar
  exact F_add_self _

set_option synthInstance.maxHeartbeats 300000 in
-- Inside the vertical orthogonal, the quadratic value depends only on the
-- reduced root, not on the representative.
theorem sqdiagReducedRelationQ_eq_of_mem_verticalOrthogonal_of_root_eq
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (_hy : y ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hroot :
      sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x =
        sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) y) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x =
      sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) y := by
  let z : SqdiagReducedRelation n a b c d := x + y
  have hzVert : z ∈ sqdiagReducedRelationVertical n a b c d := by
    rw [LinearMap.mem_ker]
    change
      sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) z = 0
    calc
      sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) z =
          sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x +
            sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) y := by
            rfl
      _ =
          sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x +
            sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x := by
            rw [hroot]
      _ = 0 := (add_eq_zero_iff_eq_of_F_module _ _).mpr rfl
  have hzQ :
      sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) z = 0 :=
    sqdiagReducedRelationQ_eq_zero_of_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) z hzVert
  have hpolarxz :
      sqdiagReducedRelationPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) x z = 0 := by
    have hxker := LinearMap.mem_ker.mp hx
    have happ :=
      congrArg
        (fun T : Module.Dual F (sqdiagReducedRelationVertical n a b c d) =>
          T ⟨z, hzVert⟩)
        hxker
    simpa [sqdiagReducedRelationPolarToVertical] using happ
  have hpolarSplit :
      sqdiagReducedRelationPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) x z =
        sqdiagReducedRelationPolar
            (n := n) (a := a) (b := b) (c := c) (d := d) x x +
          sqdiagReducedRelationPolar
            (n := n) (a := a) (b := b) (c := c) (d := d) x y := by
    change
      sqdiagReducedRelationPolarLinear
          (n := n) (a := a) (b := b) (c := c) (d := d) x z =
        sqdiagReducedRelationPolarLinear
            (n := n) (a := a) (b := b) (c := c) (d := d) x x +
          sqdiagReducedRelationPolarLinear
            (n := n) (a := a) (b := b) (c := c) (d := d) x y
    rw [show z = x + y by rfl]
    exact
      (sqdiagReducedRelationPolarLinear
        (n := n) (a := a) (b := b) (c := c) (d := d) x).map_add x y
  have hpolarxy :
      sqdiagReducedRelationPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) x y = 0 := by
    rw [hpolarSplit, sqdiagReducedRelationPolar_self] at hpolarxz
    simpa using hpolarxz
  have hsum :
      sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x +
          sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) y = 0 := by
    have hqadd :=
      sqdiagReducedRelationQ_add
        (n := n) (a := a) (b := b) (c := c) (d := d) x y
    rw [show z = x + y by rfl] at hzQ
    rw [hqadd, hpolarxy] at hzQ
    simpa [add_assoc] using hzQ
  exact (add_eq_zero_iff_eq_of_F_module _ _).mp hsum

theorem sqdiagReducedRelationQ_eq_of_verticalOrthogonal_defect_eq
    {n a b c d : ℕ} [NeZero n]
    (x y : sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hdef :
      sqdiagReducedRelationVerticalOrthogonalToRootDefect
          (n := n) (a := a) (b := b) (c := c) (d := d) x =
        sqdiagReducedRelationVerticalOrthogonalToRootDefect
          (n := n) (a := a) (b := b) (c := c) (d := d) y) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 =
      sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1 := by
  apply
    sqdiagReducedRelationQ_eq_of_mem_verticalOrthogonal_of_root_eq
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x.1 y.1 x.2 y.2
  have hroot :=
    congrArg
      (fun R0 : sqdiagReducedRelationRootDefect n a b c d => R0.1.1)
      hdef
  simpa [sqdiagReducedRelationVerticalOrthogonalToRootDefect_apply] using hroot

theorem sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_defect_section
    {n a b c d : ℕ} [NeZero n]
    (S :
      sqdiagReducedRelationRootDefect n a b c d →ₗ[F]
        sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hS :
      ∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
        sqdiagReducedRelationVerticalOrthogonalToRootDefect
            (n := n) (a := a) (b := b) (c := c) (d := d) (S R0) =
          R0)
    (hQ :
      ∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
        sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (S R0).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let xv : sqdiagReducedRelationVerticalOrthogonal n a b c d := ⟨x, hx⟩
  let R0 : sqdiagReducedRelationRootDefect n a b c d :=
    sqdiagReducedRelationVerticalOrthogonalToRootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d) xv
  have hsame :
      sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (S R0).1 =
        sqdiagReducedRelationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x := by
    exact
      sqdiagReducedRelationQ_eq_of_verticalOrthogonal_defect_eq
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (S R0) xv (by rw [hS R0])
  exact hsame.symm.trans (hQ R0)

theorem sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_param_defect_section
    {X : Type*} [AddCommGroup X] [Module F X]
    {n a b c d : ℕ} [NeZero n]
    (encode :
      sqdiagReducedRelationRootDefect n a b c d →ₗ[F] X)
    (repr :
      X →ₗ[F] sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hsection :
      ∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
        sqdiagReducedRelationVerticalOrthogonalToRootDefect
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (repr (encode R0)) =
          R0)
    (hQ :
      ∀ x : X,
        sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (repr x).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_defect_section
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (repr.comp encode)
    hsection
    (fun R0 => hQ (encode R0))
    x hx

end

end SquareDiagonal
end Core4loop
