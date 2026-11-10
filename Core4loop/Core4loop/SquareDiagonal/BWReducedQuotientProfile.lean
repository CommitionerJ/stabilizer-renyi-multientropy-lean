import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.Module.Projective
import Core4loop.Vec
import Core4loop.SquareDiagonal.BWReducedQuotient
import Core4loop.SquareDiagonal.BWReducedProfile
import Core4loop.SquareDiagonal.KCAdjointRank
import Core4loop.RootSpaces.PullYZW
import Core4loop.Square.Rank.IntersectionRoot
import Core4loop.Square.Rank.CoreParam

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

noncomputable def linearMapLiftOfRangeLe
    {V W U : Type*}
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [AddCommGroup U] [Module F U]
    (f : V →ₗ[F] W) (g : U →ₗ[F] W)
    (h : LinearMap.range g ≤ LinearMap.range f) :
    U →ₗ[F] V :=
  let gRange : U →ₗ[F] LinearMap.range f :=
    g.codRestrict (LinearMap.range f) (fun u => h ⟨u, rfl⟩)
  (Classical.choose
    (f.rangeRestrict.exists_rightInverse_of_surjective
      (LinearMap.range_rangeRestrict f))).comp gRange

theorem linearMap_comp_liftOfRangeLe
    {V W U : Type*}
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [AddCommGroup U] [Module F U]
    (f : V →ₗ[F] W) (g : U →ₗ[F] W)
    (h : LinearMap.range g ≤ LinearMap.range f) :
    f.comp (linearMapLiftOfRangeLe f g h) = g := by
  ext u
  let gRange : U →ₗ[F] LinearMap.range f :=
    g.codRestrict (LinearMap.range f) (fun u => h ⟨u, rfl⟩)
  let e :=
    f.rangeRestrict.exists_rightInverse_of_surjective
      (LinearMap.range_rangeRestrict f)
  have hright := Classical.choose_spec e
  have hu :=
    congrArg (fun T : LinearMap.range f →ₗ[F] LinearMap.range f => T (gRange u)) hright
  have hval := congrArg Subtype.val hu
  simpa [linearMapLiftOfRangeLe, gRange, e] using hval

theorem linearMap_range_le_iff_exists_comp
    {V W U : Type*}
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [AddCommGroup U] [Module F U]
    (f : V →ₗ[F] W) (g : U →ₗ[F] W) :
    LinearMap.range g ≤ LinearMap.range f ↔
      ∃ h : U →ₗ[F] V, f.comp h = g := by
  constructor
  · intro hrange
    exact ⟨linearMapLiftOfRangeLe f g hrange,
      linearMap_comp_liftOfRangeLe f g hrange⟩
  · rintro ⟨h, hcomp⟩
    intro w hw
    rcases hw with ⟨u, rfl⟩
    refine ⟨h u, ?_⟩
    exact congrArg (fun T : U →ₗ[F] W => T u) hcomp

theorem linearMap_bijective_iff_exists_linear_inverse
    {V W : Type*}
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) :
    Function.Bijective f ↔
      ∃ g : W →ₗ[F] V,
        g.comp f = LinearMap.id ∧
          f.comp g = LinearMap.id := by
  constructor
  · intro hbij
    let e : V ≃ₗ[F] W := LinearEquiv.ofBijective f hbij
    refine ⟨e.symm.toLinearMap, ?_, ?_⟩
    · ext v
      simpa [e] using e.left_inv v
    · ext w
      simpa [e] using e.right_inv w
  · rintro ⟨g, hleft, hright⟩
    have hleftFun : Function.LeftInverse g f := by
      intro v
      have hv :=
        congrArg (fun T : V →ₗ[F] V => T v) hleft
      simpa using hv
    have hrightFun : Function.RightInverse g f := by
      intro w
      have hw :=
        congrArg (fun T : W →ₗ[F] W => T w) hright
      simpa using hw
    exact ⟨hleftFun.injective, hrightFun.surjective⟩

-- The surviving reduced-root defect is modeled by the two external trace
-- kernels and their genuine shared matrix overlap. This is not a zero quotient.
abbrev SqdiagReducedRootProfile
    (n b d : ℕ) [NeZero n] :=
  (LinearMap.ker (SquareRootTrace (n := n) (c := d)) ×
    LinearMap.ker (SquareRootTrace (n := n) (c := b))) ×
      MatrixZeroSum n

theorem sqdiagSquareRootTrace_ker_coord_zero
    {n c : ℕ} [NeZero n]
    (M : LinearMap.ker (SquareRootTrace (n := n) (c := c)))
    (s sy sw : I n) :
    (∑ z : ZVec n c, if vecSum z = s then (M.1 z).1 sy sw else 0) = 0 := by
  have htrace :
      SquareRootTrace (n := n) (c := c) M.1 = 0 :=
    LinearMap.mem_ker.mp M.2
  have hcoord :=
    congrArg (fun T : SquareRootCore n => (T s).1 sy sw) htrace
  change
    ((∑ z : ZVec n c, if vecSum z = s then M.1 z else 0).1 sy sw) = 0
    at hcoord
  calc
    (∑ z : ZVec n c, if vecSum z = s then (M.1 z).1 sy sw else 0)
        =
      ∑ z : ZVec n c,
        ((if vecSum z = s then M.1 z else 0 : MatrixZeroSum n).1 sy sw) := by
          refine Finset.sum_congr rfl ?_
          intro z _
          by_cases hz : vecSum z = s <;> simp [hz]
    _ = 0 := by
          simpa using hcoord

theorem sqdiagSquareRootTrace_ker_matrix_coord_zero
    {n c : ℕ} [NeZero n]
    (M : LinearMap.ker (SquareRootTrace (n := n) (c := c)))
    (s : I n) :
    (∑ z : ZVec n c, if vecSum z = s then M.1 z else 0) = 0 := by
  have htrace :
      SquareRootTrace (n := n) (c := c) M.1 = 0 :=
    LinearMap.mem_ker.mp M.2
  exact congrFun htrace s

noncomputable def sqdiagSharedMatrixCube
    {n : ℕ} [NeZero n] :
    MatrixZeroSum n →ₗ[F] CubeZeroSum n where
  toFun S :=
    ⟨fun sy sz sw => S.1 sz (sw + sy), by
      constructor
      · constructor
        · apply LinearMap.mem_ker.mpr
          funext sz sw
          change (∑ sy : I n, S.1 sz (sw + sy)) = 0
          have hshift :
              (∑ sy : I n, S.1 sz (sw + sy)) =
                ∑ r : I n, S.1 sz r := by
            simpa using
              (Equiv.sum_comp (Equiv.addLeft sw)
                (fun r : I n => S.1 sz r))
          rw [hshift]
          exact matrix_row_zero S sz
        · apply LinearMap.mem_ker.mpr
          funext sy sw
          change (∑ sz : I n, S.1 sz (sw + sy)) = 0
          exact matrix_col_zero S (sw + sy)
      · apply LinearMap.mem_ker.mpr
        funext sy sz
        change (∑ sw : I n, S.1 sz (sw + sy)) = 0
        have hshift :
            (∑ sw : I n, S.1 sz (sw + sy)) =
              ∑ r : I n, S.1 sz r := by
          simpa [add_comm] using
            (Equiv.sum_comp (Equiv.addRight sy)
              (fun r : I n => S.1 sz r))
        rw [hshift]
        exact matrix_row_zero S sz⟩
  map_add' S T := by
    apply Subtype.ext
    funext sy sz sw
    rfl
  map_smul' r S := by
    apply Subtype.ext
    funext sy sz sw
    rfl

@[simp]
theorem sqdiagSharedMatrixCube_apply
    {n : ℕ} [NeZero n]
    (S : MatrixZeroSum n) (sy sz sw : I n) :
    (sqdiagSharedMatrixCube (n := n) S).1 sy sz sw =
      S.1 sz (sw + sy) :=
  rfl

noncomputable def sqdiagCubeFromZMatrixSlices
    {n : ℕ} [NeZero n] :
    ZeroSumProfileM n (MatrixZeroSum n) →ₗ[F] CubeZeroSum n where
  toFun S :=
    ⟨fun sy sz sw => (S.1 sz).1 sy sw, by
      constructor
      · constructor
        · apply LinearMap.mem_ker.mpr
          funext sz sw
          exact matrix_col_zero (S.1 sz) sw
        · apply LinearMap.mem_ker.mpr
          funext sy sw
          have hS : (∑ sz : I n, S.1 sz) = 0 := LinearMap.mem_ker.mp S.2
          have h := congrArg (fun M : MatrixZeroSum n => M.1 sy sw) hS
          simpa using h
      · apply LinearMap.mem_ker.mpr
        funext sy sz
        exact matrix_row_zero (S.1 sz) sy⟩
  map_add' S T := by
    apply Subtype.ext
    funext sy sz sw
    rfl
  map_smul' r S := by
    apply Subtype.ext
    funext sy sz sw
    rfl

noncomputable def sqdiagCubeZMatrixSlices
    {n : ℕ} [NeZero n] :
    CubeZeroSum n →ₗ[F] ZeroSumProfileM n (MatrixZeroSum n) where
  toFun T :=
    ⟨fun sz =>
      ⟨fun sy sw => T.1 sy sz sw, by
        constructor
        · apply LinearMap.mem_ker.mpr
          funext sy
          exact cube_sumZ_zero T sy sz
        · apply LinearMap.mem_ker.mpr
          funext sw
          exact cube_sumX_zero T sz sw⟩, by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      funext sy sw
      simp [sigmaMapM, cube_sumY_zero T sy sw]⟩
  map_add' T U := by
    apply Subtype.ext
    funext sz
    apply Subtype.ext
    funext sy sw
    rfl
  map_smul' r T := by
    apply Subtype.ext
    funext sz
    apply Subtype.ext
    funext sy sw
    rfl

@[simp]
theorem sqdiagCubeFromZMatrixSlices_apply
    {n : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) (sy sz sw : I n) :
    (sqdiagCubeFromZMatrixSlices (n := n) S).1 sy sz sw =
      (S.1 sz).1 sy sw :=
  rfl

@[simp]
theorem sqdiagCubeZMatrixSlices_apply
    {n : ℕ} [NeZero n]
    (T : CubeZeroSum n) (sz sy sw : I n) :
    ((sqdiagCubeZMatrixSlices (n := n) T).1 sz).1 sy sw =
      T.1 sy sz sw :=
  rfl

@[simp]
theorem sqdiagCubeFromZMatrixSlices_cubeZMatrixSlices
    {n : ℕ} [NeZero n] (T : CubeZeroSum n) :
    sqdiagCubeFromZMatrixSlices (n := n)
        (sqdiagCubeZMatrixSlices (n := n) T) = T := by
  apply Subtype.ext
  funext sy sz sw
  rfl

@[simp]
theorem sqdiagCubeZMatrixSlices_cubeFromZMatrixSlices
    {n : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) :
    sqdiagCubeZMatrixSlices (n := n)
        (sqdiagCubeFromZMatrixSlices (n := n) S) = S := by
  apply Subtype.ext
  funext sz
  apply Subtype.ext
  funext sy sw
  rfl

noncomputable def sqdiagYWCoeffOfZMatrixSlices
    {n c : ℕ} [NeZero n] :
    ZeroSumProfileM n (MatrixZeroSum n) →ₗ[F] YWCoeff n c where
  toFun S := fun z => S.1 (vecSum z)
  map_add' S T := by
    funext z
    rfl
  map_smul' r S := by
    funext z
    rfl

@[simp]
theorem sqdiagYWCoeffOfZMatrixSlices_apply
    {n c : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) (z : ZVec n c) :
    sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c) S z =
      S.1 (vecSum z) :=
  rfl

@[simp]
theorem sqdiagYWCoeffOfZMatrixSlices_pullYW
    {n b c d : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) :
    pullYW (n := n) (b := b) (c := c) (d := d)
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c) S) =
      pullYZW (n := n) (b := b) (c := c) (d := d)
        (sqdiagCubeFromZMatrixSlices (n := n) S) := by
  funext y z w
  rfl

theorem sqdiagYWCoeffOfZMatrixSlices_pullYW_mem_range_pullYZW
    {n b c d : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) :
    pullYW (n := n) (b := b) (c := c) (d := d)
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c) S) ∈
      LinearMap.range
        (pullYZW (n := n) (b := b) (c := c) (d := d)) := by
  exact ⟨sqdiagCubeFromZMatrixSlices (n := n) S, by
    rw [sqdiagYWCoeffOfZMatrixSlices_pullYW]⟩

@[simp]
theorem sqdiagYWCoeffOfZMatrixSlices_cubeZMatrixSlices_pullYW
    {n b c d : ℕ} [NeZero n]
    (T : CubeZeroSum n) :
    pullYW (n := n) (b := b) (c := c) (d := d)
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)
          (sqdiagCubeZMatrixSlices (n := n) T)) =
      pullYZW (n := n) (b := b) (c := c) (d := d) T := by
  funext y z w
  rfl

theorem pullYW_mem_range_pullYZW_iff_ywCoeff_range_zMatrixSlices
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) (M : YWCoeff n c) :
    pullYW (n := n) (b := b) (c := c) (d := d) M ∈
        LinearMap.range
          (pullYZW (n := n) (b := b) (c := c) (d := d)) ↔
      M ∈ LinearMap.range
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨sqdiagCubeZMatrixSlices (n := n) T, ?_⟩
    apply pullYW_injective (n := n) (b := b) (c := c) (d := d) hb hd
    rw [sqdiagYWCoeffOfZMatrixSlices_cubeZMatrixSlices_pullYW]
    exact hT
  · rintro ⟨S, rfl⟩
    exact
      sqdiagYWCoeffOfZMatrixSlices_pullYW_mem_range_pullYZW
        (n := n) (b := b) (c := c) (d := d) S

noncomputable def sqdiagSquareRootTraceZMatrixSlices
    {n c : ℕ} [NeZero n] :
    ZeroSumProfileM n (MatrixZeroSum n) →ₗ[F] SquareRootCore n :=
  (SquareRootTrace (n := n) (c := c)).comp
    (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))

@[simp]
theorem sqdiagSquareRootTraceZMatrixSlices_apply
    {n c : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) :
    sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c) S =
      SquareRootTrace (n := n) (c := c)
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c) S) :=
  rfl

noncomputable def sqdiagVecSumFiberParity
    {n c : ℕ} [NeZero n] (sz : I n) : F :=
  ∑ z : ZVec n c, if vecSum z = sz then (1 : F) else 0

theorem sqdiagSquareRootTraceZMatrixSlices_coord
    {n c : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n))
    (sz sy sw : I n) :
    (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c) S sz).1 sy sw =
      sqdiagVecSumFiberParity (n := n) (c := c) sz * (S.1 sz).1 sy sw := by
  change
    ((Submodule.subtype (MatrixZeroSum n))
      (∑ z : ZVec n c,
        if vecSum z = sz then
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c) S) z
        else 0)) sy sw =
      (∑ z : ZVec n c, if vecSum z = sz then (1 : F) else 0) *
        (S.1 sz).1 sy sw
  rw [map_sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases hz : vecSum z = sz
  · simp [sqdiagYWCoeffOfZMatrixSlices_apply, hz]
  · simp [hz]

theorem sqdiagVecSumFiberParity_eq
    {n c : ℕ} [NeZero n] (hc : 0 < c) (s t : I n) :
    sqdiagVecSumFiberParity (n := n) (c := c) s =
      sqdiagVecSumFiberParity (n := n) (c := c) t := by
  classical
  let i : Fin c := ⟨0, hc⟩
  unfold sqdiagVecSumFiberParity
  calc
    (∑ z : ZVec n c, if vecSum z = s then (1 : F) else 0)
        =
      ∑ z : ZVec n c,
        if vecSum (shiftVec z i (t - s)) = t then (1 : F) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [vecSum_shiftVec]
          by_cases hz : vecSum z = s
          · simp [hz]
          · have htarget : vecSum z + (t - s) ≠ t := by
              intro h
              apply hz
              calc
                vecSum z = (vecSum z + (t - s)) - (t - s) := by abel
                _ = t - (t - s) := by rw [h]
                _ = s := by abel
            simp [hz, htarget]
    _ =
      ∑ z : ZVec n c, if vecSum z = t then (1 : F) else 0 := by
        exact
          sum_vec_shift_invariant (n := n) (k := c) i (t - s)
            (fun z : Vec n c => if vecSum z = t then (1 : F) else 0)

noncomputable def sqdiagVecSumFiberParityBase
    {n c : ℕ} [NeZero n] : F :=
  sqdiagVecSumFiberParity (n := n) (c := c) 0

theorem sqdiagVecSumFiberParity_eq_base
    {n c : ℕ} [NeZero n] (hc : 0 < c) (sz : I n) :
    sqdiagVecSumFiberParity (n := n) (c := c) sz =
      sqdiagVecSumFiberParityBase (n := n) (c := c) := by
  exact sqdiagVecSumFiberParity_eq (n := n) (c := c) hc sz 0

theorem sqdiagSquareRootTraceZMatrixSlices_coord_base
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (S : ZeroSumProfileM n (MatrixZeroSum n))
    (sz sy sw : I n) :
    (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c) S sz).1 sy sw =
      sqdiagVecSumFiberParityBase (n := n) (c := c) * (S.1 sz).1 sy sw := by
  rw [sqdiagSquareRootTraceZMatrixSlices_coord,
    sqdiagVecSumFiberParity_eq_base (n := n) (c := c) hc sz]

theorem sqdiagVecSumFiberParityBase_eq_card_tail
    {n c : ℕ} [NeZero n] (hc : 0 < c) :
    sqdiagVecSumFiberParityBase (n := n) (c := c) =
      (Fintype.card (Vec n (c - 1)) : F) := by
  unfold sqdiagVecSumFiberParityBase sqdiagVecSumFiberParity
  rw [sum_vecSum_eq_card_tail_mul (n := n) (d := c) hc
    (fun s : I n => if s = 0 then (1 : F) else 0)]
  have hsum : (∑ s : I n, if s = 0 then (1 : F) else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : I n)]
    · simp
    · intro s _ hs
      simp [hs]
    · intro hnot
      simp at hnot
  rw [hsum, mul_one]

theorem sqdiagVecSumFiberParityBase_eq_one_of_odd
    {n c : ℕ} [NeZero n] (hc : 0 < c) (hn : Odd n) :
    sqdiagVecSumFiberParityBase (n := n) (c := c) = 1 := by
  rw [sqdiagVecSumFiberParityBase_eq_card_tail (n := n) (c := c) hc]
  exact natCast_card_vec_eq_one_of_odd (n := n) (k := c - 1) hn

theorem sqdiagVecSumFiberParityBase_eq_zero_of_even_two_le
    {n c : ℕ} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c) :
    sqdiagVecSumFiberParityBase (n := n) (c := c) = 0 := by
  have hc : 0 < c := by omega
  have htail : 0 < c - 1 := by omega
  rw [sqdiagVecSumFiberParityBase_eq_card_tail (n := n) (c := c) hc]
  exact natCast_card_vec_eq_zero_of_even_pos
    (n := n) (k := c - 1) hn htail

@[simp]
theorem sqdiagVecSumFiberParity_one
    {n : ℕ} [NeZero n] (sz : I n) :
    sqdiagVecSumFiberParity (n := n) (c := 1) sz = 1 := by
  classical
  let z0 : ZVec n 1 := fun _ => sz
  unfold sqdiagVecSumFiberParity
  rw [Finset.sum_eq_single z0]
  · simp [z0, vecSum]
  · intro z _ hz0
    by_cases hz : vecSum z = sz
    · have hz_eq : z = z0 := by
        funext i
        fin_cases i
        simpa [z0, vecSum] using hz
      exact False.elim (hz0 hz_eq)
    · simp [hz]
  · intro hz0
    simp at hz0

@[simp]
theorem sqdiagSquareRootTraceZMatrixSlices_one_apply
    {n : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) (sz : I n) :
    sqdiagSquareRootTraceZMatrixSlices (n := n) (c := 1) S sz =
      S.1 sz := by
  apply Subtype.ext
  funext sy sw
  rw [sqdiagSquareRootTraceZMatrixSlices_coord,
    sqdiagVecSumFiberParity_one]
  simp

noncomputable def sqdiagZMatrixSlicesRootCoreInclusion
    {n : ℕ} [NeZero n] :
    ZeroSumProfileM n (MatrixZeroSum n) →ₗ[F] SquareRootCore n :=
  Submodule.subtype (ZeroSumProfileM n (MatrixZeroSum n))

@[simp]
theorem sqdiagZMatrixSlicesRootCoreInclusion_apply
    {n : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) :
    sqdiagZMatrixSlicesRootCoreInclusion (n := n) S = S.1 :=
  rfl

@[simp]
theorem sqdiagZMatrixSlicesRootCoreInclusion_range
    {n : ℕ} [NeZero n] :
    LinearMap.range (sqdiagZMatrixSlicesRootCoreInclusion (n := n)) =
      ZeroSumProfileM n (MatrixZeroSum n) := by
  ext R
  constructor
  · rintro ⟨S, rfl⟩
    exact S.2
  · intro hR
    exact ⟨⟨R, hR⟩, rfl⟩

theorem sqdiagSquareRootTraceZMatrixSlices_one_eq
    {n : ℕ} [NeZero n] :
    sqdiagSquareRootTraceZMatrixSlices (n := n) (c := 1) =
      sqdiagZMatrixSlicesRootCoreInclusion (n := n) := by
  apply LinearMap.ext
  intro S
  funext sz
  simp

@[simp]
theorem sqdiagSquareRootTraceZMatrixSlices_one_range
    {n : ℕ} [NeZero n] :
    LinearMap.range (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := 1)) =
      ZeroSumProfileM n (MatrixZeroSum n) := by
  rw [sqdiagSquareRootTraceZMatrixSlices_one_eq]
  ext R
  constructor
  · rintro ⟨S, rfl⟩
    exact S.2
  · intro hR
    exact ⟨⟨R, hR⟩, rfl⟩

@[simp]
theorem sqdiagSquareRootTraceZMatrixSlices_one_mem_range_iff
    {n : ℕ} [NeZero n] (R : SquareRootCore n) :
    R ∈ LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := 1)) ↔
      R ∈ ZeroSumProfileM n (MatrixZeroSum n) := by
  rw [sqdiagSquareRootTraceZMatrixSlices_one_range]

theorem sqdiagSquareRootTraceZMatrixSlices_eq_inclusion_of_parityBase_eq_one
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (hparity : sqdiagVecSumFiberParityBase (n := n) (c := c) = 1) :
    sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c) =
      sqdiagZMatrixSlicesRootCoreInclusion (n := n) := by
  apply LinearMap.ext
  intro S
  funext sz
  apply Subtype.ext
  funext sy sw
  rw [sqdiagSquareRootTraceZMatrixSlices_coord_base (n := n) (c := c) hc,
    hparity]
  simp

theorem sqdiagSquareRootTraceZMatrixSlices_range_eq_zeroSumProfileM_of_parityBase_eq_one
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (hparity : sqdiagVecSumFiberParityBase (n := n) (c := c) = 1) :
    LinearMap.range (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) =
      ZeroSumProfileM n (MatrixZeroSum n) := by
  rw [sqdiagSquareRootTraceZMatrixSlices_eq_inclusion_of_parityBase_eq_one
    (n := n) (c := c) hc hparity]
  exact sqdiagZMatrixSlicesRootCoreInclusion_range (n := n)

theorem sqdiagSquareRootTraceZMatrixSlices_eq_zero_of_parityBase_eq_zero
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (hparity : sqdiagVecSumFiberParityBase (n := n) (c := c) = 0) :
    sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c) = 0 := by
  apply LinearMap.ext
  intro S
  funext sz
  apply Subtype.ext
  funext sy sw
  rw [sqdiagSquareRootTraceZMatrixSlices_coord_base (n := n) (c := c) hc,
    hparity]
  simp

theorem sqdiagSquareRootTraceZMatrixSlices_range_eq_bot_of_parityBase_eq_zero
    {n c : ℕ} [NeZero n] (hc : 0 < c)
    (hparity : sqdiagVecSumFiberParityBase (n := n) (c := c) = 0) :
    LinearMap.range (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) =
      ⊥ := by
  rw [sqdiagSquareRootTraceZMatrixSlices_eq_zero_of_parityBase_eq_zero
    (n := n) (c := c) hc hparity]
  simp

theorem sqdiagSquareRootTraceZMatrixSlices_eq_inclusion_of_odd
    {n c : ℕ} [NeZero n] (hc : 0 < c) (hn : Odd n) :
    sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c) =
      sqdiagZMatrixSlicesRootCoreInclusion (n := n) :=
  sqdiagSquareRootTraceZMatrixSlices_eq_inclusion_of_parityBase_eq_one
    (n := n) (c := c) hc
    (sqdiagVecSumFiberParityBase_eq_one_of_odd
      (n := n) (c := c) hc hn)

theorem sqdiagSquareRootTraceZMatrixSlices_range_eq_zeroSumProfileM_of_odd
    {n c : ℕ} [NeZero n] (hc : 0 < c) (hn : Odd n) :
    LinearMap.range (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) =
      ZeroSumProfileM n (MatrixZeroSum n) :=
  sqdiagSquareRootTraceZMatrixSlices_range_eq_zeroSumProfileM_of_parityBase_eq_one
    (n := n) (c := c) hc
    (sqdiagVecSumFiberParityBase_eq_one_of_odd
      (n := n) (c := c) hc hn)

theorem sqdiagSquareRootTraceZMatrixSlices_eq_zero_of_even_two_le
    {n c : ℕ} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c) :
    sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c) = 0 := by
  have hc : 0 < c := by omega
  exact
    sqdiagSquareRootTraceZMatrixSlices_eq_zero_of_parityBase_eq_zero
      (n := n) (c := c) hc
      (sqdiagVecSumFiberParityBase_eq_zero_of_even_two_le
        (n := n) (c := c) hn hc2)

theorem sqdiagSquareRootTraceZMatrixSlices_range_eq_bot_of_even_two_le
    {n c : ℕ} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c) :
    LinearMap.range (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) =
      ⊥ := by
  have hc : 0 < c := by omega
  exact
    sqdiagSquareRootTraceZMatrixSlices_range_eq_bot_of_parityBase_eq_zero
      (n := n) (c := c) hc
      (sqdiagVecSumFiberParityBase_eq_zero_of_even_two_le
        (n := n) (c := c) hn hc2)

noncomputable def sqdiagSharedMatrixYWCoeff
    {n c : ℕ} [NeZero n] :
    MatrixZeroSum n →ₗ[F] YWCoeff n c where
  toFun S := fun z =>
    ⟨fun sy sw => S.1 (vecSum z) (sw + sy), by
      constructor
      · apply LinearMap.mem_ker.mpr
        funext sy
        change (∑ sw : I n, S.1 (vecSum z) (sw + sy)) = 0
        have hshift :
            (∑ sw : I n, S.1 (vecSum z) (sw + sy)) =
              ∑ r : I n, S.1 (vecSum z) r := by
          simpa [add_comm] using
            (Equiv.sum_comp (Equiv.addRight sy)
              (fun r : I n => S.1 (vecSum z) r))
        rw [hshift]
        exact matrix_row_zero S (vecSum z)
      · apply LinearMap.mem_ker.mpr
        funext sw
        change (∑ sy : I n, S.1 (vecSum z) (sw + sy)) = 0
        have hshift :
            (∑ sy : I n, S.1 (vecSum z) (sw + sy)) =
              ∑ r : I n, S.1 (vecSum z) r := by
          simpa using
            (Equiv.sum_comp (Equiv.addLeft sw)
              (fun r : I n => S.1 (vecSum z) r))
        rw [hshift]
        exact matrix_row_zero S (vecSum z)⟩
  map_add' S T := by
    funext z
    apply Subtype.ext
    funext sy sw
    rfl
  map_smul' r S := by
    funext z
    apply Subtype.ext
    funext sy sw
    rfl

@[simp]
theorem sqdiagSharedMatrixYWCoeff_apply
    {n c : ℕ} [NeZero n]
    (S : MatrixZeroSum n) (z : ZVec n c) (sy sw : I n) :
    (sqdiagSharedMatrixYWCoeff (n := n) (c := c) S z).1 sy sw =
      S.1 (vecSum z) (sw + sy) :=
  rfl

@[simp]
theorem sqdiagSharedMatrixYWCoeff_pullYW
    {n b c d : ℕ} [NeZero n]
    (S : MatrixZeroSum n) :
    pullYW (n := n) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixYWCoeff (n := n) (c := c) S) =
      pullYZW (n := n) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixCube (n := n) S) := by
  funext y z w
  rfl

noncomputable def sqdiagSharedMatrixKCRangeModel
    {n b d : ℕ} [NeZero n] :
    MatrixZeroSum n →ₗ[F] SqdiagKCAdjointRangeModel n b d where
  toFun S := fun y w =>
    ⟨fun sz => S.1 sz (vecSum w + vecSum y), by
      apply LinearMap.mem_ker.mpr
      change (∑ sz : I n, S.1 sz (vecSum w + vecSum y)) = 0
      exact matrix_col_zero S (vecSum w + vecSum y)⟩
  map_add' S T := by
    funext y w
    apply Subtype.ext
    funext sz
    rfl
  map_smul' r S := by
    funext y w
    apply Subtype.ext
    funext sz
    rfl

@[simp]
theorem sqdiagSharedMatrixKCRangeModel_apply
    {n b d : ℕ} [NeZero n]
    (S : MatrixZeroSum n) (y : YVec n b) (w : WVec n d) (sz : I n) :
    (sqdiagSharedMatrixKCRangeModel (n := n) (b := b) (d := d) S y w).1 sz =
      S.1 sz (vecSum w + vecSum y) :=
  rfl

@[simp]
theorem sqdiagSharedMatrixKCRangeEmbed_apply
    {n a b d : ℕ} [NeZero n]
    (S : MatrixZeroSum n) (p : PVec n a) (y : YVec n b) (sz : I n)
    (w : WVec n d) :
    sqdiagKCAdjointRangeEmbed (n := n) (a := a) (b := b) (d := d)
        (sqdiagSharedMatrixKCRangeModel (n := n) (b := b) (d := d) S)
        p y sz w =
      S.1 sz (vecSum w + vecSum y) :=
  rfl

noncomputable def sqdiagSharedMatrixTarget
    {n a b c d : ℕ} [NeZero n] :
    MatrixZeroSum n →ₗ[F] RootTarget n b c d × CFun4 n a b d :=
  LinearMap.prod
    ((pullYZW (n := n) (b := b) (c := c) (d := d)).comp
      (sqdiagSharedMatrixCube (n := n)))
    ((sqdiagKCAdjointRangeEmbed (n := n) (a := a) (b := b) (d := d)).comp
      (sqdiagSharedMatrixKCRangeModel (n := n) (b := b) (d := d)))

@[simp]
theorem sqdiagSharedMatrixTarget_root
    {n a b c d : ℕ} [NeZero n]
    (S : MatrixZeroSum n) :
    (sqdiagSharedMatrixTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) S).1 =
      pullYZW (n := n) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixCube (n := n) S) :=
  rfl

@[simp]
theorem sqdiagSharedMatrixTarget_coeff
    {n a b c d : ℕ} [NeZero n]
    (S : MatrixZeroSum n) :
    (sqdiagSharedMatrixTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) S).2 =
      sqdiagKCAdjointRangeEmbed (n := n) (a := a) (b := b) (d := d)
        (sqdiagSharedMatrixKCRangeModel (n := n) (b := b) (d := d) S) :=
  rfl

theorem sqdiagSharedMatrixTarget_mem_ZAdjoint
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (S : MatrixZeroSum n) :
    sqdiagSharedMatrixTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) S ∈
      sqdiagZAdjointTargetSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  apply (sqdiagZAdjointTargetSubmodule_mem_iff
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagSharedMatrixTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) S)).mpr
  constructor
  · rw [sqdiagSharedMatrixTarget_root]
    exact
      (range_pullYZW_le_inf_YZW
        (n := n) (b := b) (c := c) (d := d)
        ⟨sqdiagSharedMatrixCube (n := n) S, rfl⟩).1.2
  · have hRange :
        (sqdiagSharedMatrixTarget
          (n := n) (a := a) (b := b) (c := c) (d := d) S).2 ∈
          LinearMap.range
            (sqdiagKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      rw [sqdiagSharedMatrixTarget_coeff,
        range_sqdiagKCAdjointMap_eq_rangeEmbed
          (n := n) (a := a) (b := b) (c := c) (d := d) hc]
      exact ⟨sqdiagSharedMatrixKCRangeModel (n := n) (b := b) (d := d) S, rfl⟩
    rcases hRange with ⟨A, hA⟩
    refine ⟨A, ?_⟩
    simpa [sqdiagKCAdjointMap_apply] using hA

-- This is only the external reduced-root skeleton. It lands in the Z-difference
-- root space, but it is not the final profile-to-defect map: finite regression
-- at (n,a,b,c,d) = (2,2,2,2,2) shows this skeleton alone has too small a root
-- span. The production map must add the SquareBWIntersection/CoreParam
-- normalization through pair presentations.
noncomputable def sqdiagReducedRootProfileRootTarget
    {n b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F] RootTarget n b c d where
  toFun p :=
    pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
      pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1 +
        pullYZW (n := n) (b := b) (c := c) (d := d)
          (sqdiagSharedMatrixCube (n := n) p.2)
  map_add' x y := by
    funext yy zz ww
    change
      (pullYZ (n := n) (b := b) (c := c) (d := d)
            (x.1.1.1 + y.1.1.1) +
          pullZW (n := n) (b := b) (c := c) (d := d)
            (x.1.2.1 + y.1.2.1) +
            pullYZW (n := n) (b := b) (c := c) (d := d)
              (sqdiagSharedMatrixCube (n := n) (x.2 + y.2))) yy zz ww =
        ((pullYZ (n := n) (b := b) (c := c) (d := d) x.1.1.1 +
            pullZW (n := n) (b := b) (c := c) (d := d) x.1.2.1 +
              pullYZW (n := n) (b := b) (c := c) (d := d)
                (sqdiagSharedMatrixCube (n := n) x.2)) +
          (pullYZ (n := n) (b := b) (c := c) (d := d) y.1.1.1 +
            pullZW (n := n) (b := b) (c := c) (d := d) y.1.2.1 +
              pullYZW (n := n) (b := b) (c := c) (d := d)
                (sqdiagSharedMatrixCube (n := n) y.2))) yy zz ww
    rw [(pullYZ (n := n) (b := b) (c := c) (d := d)).map_add,
      (pullZW (n := n) (b := b) (c := c) (d := d)).map_add,
      (sqdiagSharedMatrixCube (n := n)).map_add,
      (pullYZW (n := n) (b := b) (c := c) (d := d)).map_add]
    simp only [Pi.add_apply]
    ring_nf
  map_smul' r x := by
    funext yy zz ww
    change
      (pullYZ (n := n) (b := b) (c := c) (d := d)
            (r • x.1.1.1) +
          pullZW (n := n) (b := b) (c := c) (d := d)
            (r • x.1.2.1) +
            pullYZW (n := n) (b := b) (c := c) (d := d)
              (sqdiagSharedMatrixCube (n := n) (r • x.2))) yy zz ww =
        (r •
          (pullYZ (n := n) (b := b) (c := c) (d := d) x.1.1.1 +
            pullZW (n := n) (b := b) (c := c) (d := d) x.1.2.1 +
              pullYZW (n := n) (b := b) (c := c) (d := d)
                (sqdiagSharedMatrixCube (n := n) x.2))) yy zz ww
    rw [(pullYZ (n := n) (b := b) (c := c) (d := d)).map_smul,
      (pullZW (n := n) (b := b) (c := c) (d := d)).map_smul,
      (sqdiagSharedMatrixCube (n := n)).map_smul,
      (pullYZW (n := n) (b := b) (c := c) (d := d)).map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf

theorem sqdiagReducedRootProfileRootTarget_mem_ZDiff
    {n b c d : ℕ} [NeZero n]
    (_hb : 0 < b) (_hc : 0 < c) (_hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  let RYZ : RootTarget n b c d :=
    pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1
  let RZW : RootTarget n b c d :=
    pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1
  let RYZW : RootTarget n b c d :=
    pullYZW (n := n) (b := b) (c := c) (d := d)
      (sqdiagSharedMatrixCube (n := n) p.2)
  have hYZ :
      RYZ ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
    (range_pullYZ_le_inf_YZ
      (n := n) (b := b) (c := c) (d := d)
      ⟨p.1.1.1, rfl⟩).2
  have hZW :
      RZW ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
    (range_pullZW_le_inf_ZW
      (n := n) (b := b) (c := c) (d := d)
      ⟨p.1.2.1, rfl⟩).1
  have hYZW :
      RYZW ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
    (range_pullYZW_le_inf_YZW
      (n := n) (b := b) (c := c) (d := d)
      ⟨sqdiagSharedMatrixCube (n := n) p.2, rfl⟩).1.2
  change RYZ + RZW + RYZW ∈
    ZDiffSpace (n := n) (b := b) (c := c) (d := d)
  exact
    (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem
      ((ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem hYZ hZW)
      hYZW

theorem sqdiagReducedRootProfileRootTarget_mem_annihilator_of_components
    {n a b c d : ℕ} [NeZero n]
    (hYZ :
      ∀ M : LinearMap.ker (SquareRootTrace (n := n) (c := d)),
        pullYZ (n := n) (b := b) (c := c) (d := d) M.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hZW :
      ∀ M : LinearMap.ker (SquareRootTrace (n := n) (c := b)),
        pullZW (n := n) (b := b) (c := c) (d := d) M.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hShared :
      ∀ S : MatrixZeroSum n,
        pullYZW (n := n) (b := b) (c := c) (d := d)
            (sqdiagSharedMatrixCube (n := n) S) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p ∈
      sqdiagRootZeroACoeffAnnihilator n a b c d := by
  change
    pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
        pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1 +
          pullYZW (n := n) (b := b) (c := c) (d := d)
            (sqdiagSharedMatrixCube (n := n) p.2) ∈
      sqdiagRootZeroACoeffAnnihilator n a b c d
  exact
    (sqdiagRootZeroACoeffAnnihilator n a b c d).add_mem
      ((sqdiagRootZeroACoeffAnnihilator n a b c d).add_mem
        (hYZ p.1.1) (hZW p.1.2))
      (hShared p.2)

theorem sqdiagReducedRelationRoot_mem_annihilator_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x).1 ∈
      sqdiagRootZeroACoeffAnnihilator n a b c d := by
  apply
    (sqdiagRootZeroACoeffAnnihilator_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x).1).mpr
  intro A hA
  have hroot :=
    (sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d) x).mp hx A hA
  change
    sqdiagRootCoeffApply
        (n := n) (b := b) (c := c) (d := d) A
        ((sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x).1) = 0
    at hroot
  exact hroot

noncomputable def sqdiagReducedRootProfileRootMap
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun p :=
    ⟨sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p,
      sqdiagReducedRootProfileRootTarget_mem_ZDiff
        (n := n) (b := b) (c := c) (d := d) hb hc hd p⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d)).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d)).map_smul r x

@[simp]
theorem sqdiagReducedRootProfileRootMap_apply
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileRootMap
        (n := n) (b := b) (c := c) (d := d) hb hc hd p).1 =
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p :=
  rfl

noncomputable def sqdiagReducedRootProfileYZCorrectedRootTarget
    {n b c d : ℕ} [NeZero n]
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d) :
    SqdiagReducedRootProfile n b d →ₗ[F] RootTarget n b c d :=
  sqdiagReducedRootProfileRootTarget
      (n := n) (b := b) (c := c) (d := d) +
    (pullYZ (n := n) (b := b) (c := c) (d := d)).comp Z

@[simp]
theorem sqdiagReducedRootProfileYZCorrectedRootTarget_apply
    {n b c d : ℕ} [NeZero n]
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileYZCorrectedRootTarget
        (n := n) (b := b) (c := c) (d := d) Z p =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) :=
  rfl

theorem sqdiagReducedRootProfileYZCorrectedRootTarget_mem_ZDiff
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileYZCorrectedRootTarget
        (n := n) (b := b) (c := c) (d := d) Z p ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rw [sqdiagReducedRootProfileYZCorrectedRootTarget_apply]
  exact
    (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem
      (sqdiagReducedRootProfileRootTarget_mem_ZDiff
        (n := n) (b := b) (c := c) (d := d) hb hc hd p)
      ((range_pullYZ_le_inf_YZ
        (n := n) (b := b) (c := c) (d := d)
        ⟨Z p, rfl⟩).2)

noncomputable def sqdiagReducedRootProfileYZCorrectedRootMap
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun p :=
    ⟨sqdiagReducedRootProfileYZCorrectedRootTarget
        (n := n) (b := b) (c := c) (d := d) Z p,
      sqdiagReducedRootProfileYZCorrectedRootTarget_mem_ZDiff
        (n := n) (b := b) (c := c) (d := d) hb hc hd Z p⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileYZCorrectedRootTarget
        (n := n) (b := b) (c := c) (d := d) Z).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileYZCorrectedRootTarget
        (n := n) (b := b) (c := c) (d := d) Z).map_smul r x

@[simp]
theorem sqdiagReducedRootProfileYZCorrectedRootMap_apply
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileYZCorrectedRootMap
        (n := n) (b := b) (c := c) (d := d) hb hc hd Z p).1 =
      sqdiagReducedRootProfileYZCorrectedRootTarget
        (n := n) (b := b) (c := c) (d := d) Z p :=
  rfl

theorem
    sqdiagReducedRootProfileYZCorrectedRootTarget_range_le_rootZeroACoeffAnnihilator_iff
    {n a b c d : ℕ} [NeZero n]
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d) :
    LinearMap.range
        (sqdiagReducedRootProfileYZCorrectedRootTarget
          (n := n) (b := b) (c := c) (d := d) Z) ≤
      sqdiagRootZeroACoeffAnnihilator n a b c d ↔
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileYZCorrectedRootTarget
          (n := n) (b := b) (c := c) (d := d) Z p ∈
        sqdiagRootZeroACoeffAnnihilator n a b c d := by
  constructor
  · intro h p
    exact h ⟨p, rfl⟩
  · intro h R hR
    rcases hR with ⟨p, rfl⟩
    exact h p

theorem sqdiagReducedRootProfileRootZeroEvalRangeLe_of_forall_exists_YZ
    {n a b c d : ℕ} [NeZero n]
    (h :
      ∀ p : SqdiagReducedRootProfile n b d,
        ∃ M : YZCoeff n d,
          sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)
              (pullYZ (n := n) (b := b) (c := c) (d := d) M) =
            sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p)) :
    LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d))) ≤
      LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (pullYZ (n := n) (b := b) (c := c) (d := d))) := by
  intro L hL
  rcases hL with ⟨p, hp⟩
  rcases h p with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  rw [← hp]
  exact hM

theorem sqdiagReducedRootProfileRootZeroEvalRangeLe_of_forall_exists_YZ_rootCoeff
    {n a b c d : ℕ} [NeZero n]
    (h :
      ∀ p : SqdiagReducedRootProfile n b d,
        ∃ M : YZCoeff n d,
          ∀ A : RootTarget n b c d,
            A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
              sqdiagRootCoeffApply
                  (n := n) (b := b) (c := c) (d := d) A
                  (pullYZ (n := n) (b := b) (c := c) (d := d) M) =
                sqdiagRootCoeffApply
                  (n := n) (b := b) (c := c) (d := d) A
                  (sqdiagReducedRootProfileRootTarget
                    (n := n) (b := b) (c := c) (d := d) p)) :
    LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d))) ≤
      LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (pullYZ (n := n) (b := b) (c := c) (d := d))) := by
  apply sqdiagReducedRootProfileRootZeroEvalRangeLe_of_forall_exists_YZ
    (n := n) (a := a) (b := b) (c := c) (d := d)
  intro p
  rcases h p with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  ext A
  exact hM A.1 A.2

theorem sqdiagReducedRootProfileRootZeroEvalRangeLe_of_rootTarget_mem_annihilator
    {n a b c d : ℕ} [NeZero n]
    (h :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d) :
    LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d))) ≤
      LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (pullYZ (n := n) (b := b) (c := c) (d := d))) := by
  apply sqdiagReducedRootProfileRootZeroEvalRangeLe_of_forall_exists_YZ
    (n := n) (a := a) (b := b) (c := c) (d := d)
  intro p
  refine ⟨0, ?_⟩
  have hp :
      sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p) = 0 :=
    LinearMap.mem_ker.mp (h p)
  rw [(pullYZ (n := n) (b := b) (c := c) (d := d)).map_zero]
  simpa using hp.symm

theorem sqdiagReducedRootProfileRootZeroEvalRangeLe_of_components_mem_annihilator
    {n a b c d : ℕ} [NeZero n]
    (hYZ :
      ∀ M : LinearMap.ker (SquareRootTrace (n := n) (c := d)),
        pullYZ (n := n) (b := b) (c := c) (d := d) M.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hZW :
      ∀ M : LinearMap.ker (SquareRootTrace (n := n) (c := b)),
        pullZW (n := n) (b := b) (c := c) (d := d) M.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hShared :
      ∀ S : MatrixZeroSum n,
        pullYZW (n := n) (b := b) (c := c) (d := d)
            (sqdiagSharedMatrixCube (n := n) S) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d) :
    LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d))) ≤
      LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (pullYZ (n := n) (b := b) (c := c) (d := d))) := by
  exact
    sqdiagReducedRootProfileRootZeroEvalRangeLe_of_rootTarget_mem_annihilator
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun p =>
        sqdiagReducedRootProfileRootTarget_mem_annihilator_of_components
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hYZ hZW hShared p)

theorem sqdiagReducedRootProfileRootZeroEvalRangeLe_of_profile_ZW_shared_eval
    {n a b c d : ℕ} [NeZero n]
    (hZW :
      ∀ M : LinearMap.ker (SquareRootTrace (n := n) (c := b)),
        ∃ N : YZCoeff n d,
          sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)
              (pullYZ (n := n) (b := b) (c := c) (d := d) N) =
            sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)
              (pullZW (n := n) (b := b) (c := c) (d := d) M.1))
    (hShared :
      ∀ S : MatrixZeroSum n,
        ∃ N : YZCoeff n d,
          sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)
              (pullYZ (n := n) (b := b) (c := c) (d := d) N) =
            sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)
              (pullYZW (n := n) (b := b) (c := c) (d := d)
                (sqdiagSharedMatrixCube (n := n) S))) :
    LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d))) ≤
      LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (pullYZ (n := n) (b := b) (c := c) (d := d))) := by
  apply sqdiagReducedRootProfileRootZeroEvalRangeLe_of_forall_exists_YZ
    (n := n) (a := a) (b := b) (c := c) (d := d)
  intro p
  rcases hZW p.1.2 with ⟨NZW, hNZW⟩
  rcases hShared p.2 with ⟨NYZW, hNYZW⟩
  refine ⟨p.1.1.1 + NZW + NYZW, ?_⟩
  let E :=
    sqdiagRootZeroACoeffEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let P := pullYZ (n := n) (b := b) (c := c) (d := d)
  let Q := pullZW (n := n) (b := b) (c := c) (d := d)
  let R := pullYZW (n := n) (b := b) (c := c) (d := d)
  calc
    E (P (p.1.1.1 + NZW + NYZW))
        = E (P p.1.1.1 + P NZW + P NYZW) := by
          rw [P.map_add, P.map_add]
    _ = E (P p.1.1.1) + E (P NZW) + E (P NYZW) := by
          rw [E.map_add, E.map_add]
    _ = E (P p.1.1.1) + E (Q p.1.2.1) +
          E (R (sqdiagSharedMatrixCube (n := n) p.2)) := by
          rw [hNZW, hNYZW]
    _ = E (P p.1.1.1 + Q p.1.2.1 +
          R (sqdiagSharedMatrixCube (n := n) p.2)) := by
          rw [E.map_add, E.map_add]
    _ =
        E (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p) := by
          rfl

theorem sqdiagReducedRootProfileRootZeroEvalRangeLe_of_ZW_shared_mem_annihilator
    {n a b c d : ℕ} [NeZero n]
    (hZW :
      ∀ M : LinearMap.ker (SquareRootTrace (n := n) (c := b)),
        pullZW (n := n) (b := b) (c := c) (d := d) M.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hShared :
      ∀ S : MatrixZeroSum n,
        pullYZW (n := n) (b := b) (c := c) (d := d)
            (sqdiagSharedMatrixCube (n := n) S) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d) :
    LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d))) ≤
      LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (pullYZ (n := n) (b := b) (c := c) (d := d))) := by
  apply sqdiagReducedRootProfileRootZeroEvalRangeLe_of_profile_ZW_shared_eval
    (n := n) (a := a) (b := b) (c := c) (d := d)
  · intro M
    refine ⟨0, ?_⟩
    have hzero :
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (pullZW (n := n) (b := b) (c := c) (d := d) M.1) = 0 :=
      LinearMap.mem_ker.mp (hZW M)
    rw [(pullYZ (n := n) (b := b) (c := c) (d := d)).map_zero]
    simpa using hzero.symm
  · intro S
    refine ⟨0, ?_⟩
    have hzero :
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (pullYZW (n := n) (b := b) (c := c) (d := d)
              (sqdiagSharedMatrixCube (n := n) S)) = 0 :=
      LinearMap.mem_ker.mp (hShared S)
    rw [(pullYZ (n := n) (b := b) (c := c) (d := d)).map_zero]
    simpa using hzero.symm

theorem
    sqdiagReducedRootProfileRootZeroEvalRangeLe_of_ZW_shared_verticalOrthogonal_roots
    {n a b c d : ℕ} [NeZero n]
    (hZW :
      ∀ M : LinearMap.ker (SquareRootTrace (n := n) (c := b)),
        ∃ x : SqdiagReducedRelation n a b c d,
          x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d ∧
            (sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x).1 =
              pullZW (n := n) (b := b) (c := c) (d := d) M.1)
    (hShared :
      ∀ S : MatrixZeroSum n,
        ∃ x : SqdiagReducedRelation n a b c d,
          x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d ∧
            (sqdiagReducedRelationRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x).1 =
              pullYZW (n := n) (b := b) (c := c) (d := d)
                (sqdiagSharedMatrixCube (n := n) S)) :
    LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d))) ≤
      LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (pullYZ (n := n) (b := b) (c := c) (d := d))) := by
  apply sqdiagReducedRootProfileRootZeroEvalRangeLe_of_ZW_shared_mem_annihilator
    (n := n) (a := a) (b := b) (c := c) (d := d)
  · intro M
    rcases hZW M with ⟨x, hx, hroot⟩
    rw [← hroot]
    exact
      sqdiagReducedRelationRoot_mem_annihilator_of_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d) x hx
  · intro S
    rcases hShared S with ⟨x, hx, hroot⟩
    rw [← hroot]
    exact
      sqdiagReducedRelationRoot_mem_annihilator_of_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d) x hx

theorem sqdiagReducedRootProfileRootZeroEvalRangeLe_of_ZW_YZW_eval
    {n a b c d : ℕ} [NeZero n]
    (hZW :
      ∀ M : ZWCoeff n b,
        ∃ N : YZCoeff n d,
          sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)
              (pullYZ (n := n) (b := b) (c := c) (d := d) N) =
            sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)
              (pullZW (n := n) (b := b) (c := c) (d := d) M))
    (hYZW :
      ∀ T : CubeZeroSum n,
        ∃ N : YZCoeff n d,
          sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)
              (pullYZ (n := n) (b := b) (c := c) (d := d) N) =
            sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)
              (pullYZW (n := n) (b := b) (c := c) (d := d) T)) :
    LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d))) ≤
      LinearMap.range
        ((sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (pullYZ (n := n) (b := b) (c := c) (d := d))) := by
  apply sqdiagReducedRootProfileRootZeroEvalRangeLe_of_forall_exists_YZ
    (n := n) (a := a) (b := b) (c := c) (d := d)
  intro p
  rcases hZW p.1.2.1 with ⟨NZW, hNZW⟩
  rcases hYZW (sqdiagSharedMatrixCube (n := n) p.2) with ⟨NYZW, hNYZW⟩
  refine ⟨p.1.1.1 + NZW + NYZW, ?_⟩
  let E :=
    sqdiagRootZeroACoeffEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let P := pullYZ (n := n) (b := b) (c := c) (d := d)
  let Q := pullZW (n := n) (b := b) (c := c) (d := d)
  let R := pullYZW (n := n) (b := b) (c := c) (d := d)
  calc
    E (P (p.1.1.1 + NZW + NYZW))
        = E (P p.1.1.1 + P NZW + P NYZW) := by
          rw [P.map_add, P.map_add]
    _ = E (P p.1.1.1) + E (P NZW) + E (P NYZW) := by
          rw [E.map_add, E.map_add]
    _ = E (P p.1.1.1) + E (Q p.1.2.1) +
          E (R (sqdiagSharedMatrixCube (n := n) p.2)) := by
          rw [hNZW, hNYZW]
    _ = E (P p.1.1.1 + Q p.1.2.1 +
          R (sqdiagSharedMatrixCube (n := n) p.2)) := by
          rw [E.map_add, E.map_add]
    _ =
        E (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p) := by
          rfl

noncomputable def sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hEvalRange :
      LinearMap.range
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d))) ≤
        LinearMap.range
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (pullYZ (n := n) (b := b) (c := c) (d := d)))) :
    SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d :=
  linearMapLiftOfRangeLe
    ((sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (pullYZ (n := n) (b := b) (c := c) (d := d)))
    ((sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d)))
    hEvalRange

theorem sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe_eval_pullYZ
    {n a b c d : ℕ} [NeZero n]
    (hEvalRange :
      LinearMap.range
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d))) ≤
        LinearMap.range
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (pullYZ (n := n) (b := b) (c := c) (d := d))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
        (pullYZ (n := n) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange p)) =
      sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p) := by
  let f :=
    (sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (pullYZ (n := n) (b := b) (c := c) (d := d))
  let g :=
    (sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d))
  have hcomp := linearMap_comp_liftOfRangeLe f g hEvalRange
  have hp := congrArg
    (fun T : SqdiagReducedRootProfile n b d →ₗ[F]
        Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) => T p)
    hcomp
  simpa [f, g, sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe] using hp

theorem
    sqdiagReducedRootProfileYZCorrectedRootTarget_range_le_rootZeroACoeffAnnihilator_of_rootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hEvalRange :
      LinearMap.range
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d))) ≤
        LinearMap.range
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (pullYZ (n := n) (b := b) (c := c) (d := d)))) :
    LinearMap.range
        (sqdiagReducedRootProfileYZCorrectedRootTarget
          (n := n) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange)) ≤
      sqdiagRootZeroACoeffAnnihilator n a b c d := by
  rw [sqdiagReducedRootProfileYZCorrectedRootTarget_range_le_rootZeroACoeffAnnihilator_iff]
  intro p
  apply LinearMap.mem_ker.mpr
  rw [sqdiagReducedRootProfileYZCorrectedRootTarget_apply,
    (sqdiagRootZeroACoeffEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add]
  rw [sqdiagReducedRootProfileYZCorrectionOfRootZeroEvalRangeLe_eval_pullYZ
    (n := n) (a := a) (b := b) (c := c) (d := d) hEvalRange p]
  exact F_module_add_self _

noncomputable def sqdiagReducedRootProfileZTarget
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F]
      RootTarget n b c d × CFun4 n a b d where
  toFun p :=
    (sqdiagReducedRootProfileRootTarget
      (n := n) (b := b) (c := c) (d := d) p,
     (sqdiagSharedMatrixTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) p.2).2)
  map_add' x y := by
    apply Prod.ext
    · exact
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d)).map_add x y
    · change
        (sqdiagSharedMatrixTarget
          (n := n) (a := a) (b := b) (c := c) (d := d) (x.2 + y.2)).2 =
          (sqdiagSharedMatrixTarget
            (n := n) (a := a) (b := b) (c := c) (d := d) x.2).2 +
            (sqdiagSharedMatrixTarget
              (n := n) (a := a) (b := b) (c := c) (d := d) y.2).2
      exact congrArg Prod.snd
        ((sqdiagSharedMatrixTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.2 y.2)
  map_smul' r x := by
    apply Prod.ext
    · exact
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d)).map_smul r x
    · change
        (sqdiagSharedMatrixTarget
          (n := n) (a := a) (b := b) (c := c) (d := d) (r • x.2)).2 =
          r •
            (sqdiagSharedMatrixTarget
              (n := n) (a := a) (b := b) (c := c) (d := d) x.2).2
      exact congrArg Prod.snd
        ((sqdiagSharedMatrixTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.2)

@[simp]
theorem sqdiagReducedRootProfileZTarget_root
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileZTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) p).1 =
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p :=
  rfl

@[simp]
theorem sqdiagReducedRootProfileZTarget_coeff
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileZTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) p).2 =
      (sqdiagSharedMatrixTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) p.2).2 :=
  rfl

theorem sqdiagReducedRootProfileZTarget_mem_ZAdjoint
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileZTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) p ∈
      sqdiagZAdjointTargetSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  apply (sqdiagZAdjointTargetSubmodule_mem_iff
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRootProfileZTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) p)).mpr
  constructor
  · rw [sqdiagReducedRootProfileZTarget_root]
    exact
      sqdiagReducedRootProfileRootTarget_mem_ZDiff
        (n := n) (b := b) (c := c) (d := d) hb hc hd p
  · have hshared :=
      (sqdiagZAdjointTargetSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixTarget
          (n := n) (a := a) (b := b) (c := c) (d := d) p.2)).mp
        (sqdiagSharedMatrixTarget_mem_ZAdjoint
          (n := n) (a := a) (b := b) (c := c) (d := d) hc p.2)
    simpa [sqdiagReducedRootProfileZTarget_coeff] using hshared.2

abbrev sqdiagReducedRootProfileZTargetInSquareCombinedRange
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) : Prop :=
  sqdiagReducedRootProfileZTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) p ∈
    LinearMap.range
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d))

set_option synthInstance.maxHeartbeats 300000 in
noncomputable def sqdiagReducedRootProfileRelationOfZTargetRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileZTargetInSquareCombinedRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagReducedRelation n a b c d where
  toFun p :=
    let T :=
      sqdiagReducedRootProfileZTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) p
    let hZ :=
      (sqdiagZAdjointTargetSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) T).mp
        (sqdiagReducedRootProfileZTarget_mem_ZAdjoint
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p)
    ⟨(⟨T.1, hZ.1⟩, ⟨T.2, hZ.2⟩), by
      change
        sqdiagReducedRelationAmbientMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (⟨T.1, hZ.1⟩, ⟨T.2, hZ.2⟩) ∈
          LinearMap.range
            (SquareCombined
              (n := n) (a := a) (b := b) (c := c) (d := d))
      simpa [T, sqdiagReducedRelationAmbientMap] using hrange p⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact
        congrArg Prod.fst
          ((sqdiagReducedRootProfileZTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x y)
    · exact
        congrArg Prod.snd
          ((sqdiagReducedRootProfileZTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x y)
  map_smul' r x := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact
        congrArg Prod.fst
          ((sqdiagReducedRootProfileZTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x)
    · exact
        congrArg Prod.snd
          ((sqdiagReducedRootProfileZTarget
            (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x)

@[simp]
theorem sqdiagReducedRootProfileRelationOfZTargetRange_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileZTargetInSquareCombinedRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileRelationOfZTargetRange
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd hrange p)).1 =
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p :=
  rfl

noncomputable def sqdiagKBMapToYDiff
    {n a b c d : ℕ} [NeZero n] :
    BFun4 n a c d →ₗ[F]
      ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun B :=
    ⟨KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B, by
      rw [← range_KBMap_eq_YDiffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d)]
      exact ⟨B, rfl⟩⟩
  map_add' B B' := by
    apply Subtype.ext
    exact
      (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_add B B'
  map_smul' r B := by
    apply Subtype.ext
    exact
      (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r B

theorem sqdiagKBMapToYDiff_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagKBMapToYDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro y
  have hy :
      y.1 ∈ LinearMap.range
        (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    rw [range_KBMap_eq_YDiffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)]
    exact y.2
  rcases hy with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  apply Subtype.ext
  exact hB

noncomputable def sqdiagKBRootSection
    {n a b c d : ℕ} [NeZero n] :
    ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d)) →ₗ[F]
      BFun4 n a c d :=
  Classical.choose
    ((sqdiagKBMapToYDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)).exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (sqdiagKBMapToYDiff_surjective
            (n := n) (a := a) (b := b) (c := c) (d := d))))

@[simp]
theorem sqdiagKBMapToYDiff_section
    {n a b c d : ℕ} [NeZero n]
    (y : ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d))) :
    sqdiagKBMapToYDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagKBRootSection
          (n := n) (a := a) (b := b) (c := c) (d := d) y) =
      y := by
  unfold sqdiagKBRootSection
  let e :=
    (sqdiagKBMapToYDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)).exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (sqdiagKBMapToYDiff_surjective
            (n := n) (a := a) (b := b) (c := c) (d := d)))
  change
    ((sqdiagKBMapToYDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (Classical.choose e)) y = y
  have hright := Classical.choose_spec e
  rw [hright]
  rfl

@[simp]
theorem sqdiagKBRootSection_root
    {n a b c d : ℕ} [NeZero n]
    (y : ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d))) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagKBRootSection
          (n := n) (a := a) (b := b) (c := c) (d := d) y) =
      y.1 := by
  exact congrArg Subtype.val
    (sqdiagKBMapToYDiff_section
      (n := n) (a := a) (b := b) (c := c) (d := d) y)

noncomputable def sqdiagKWMapToWDiff
    {n a b c d : ℕ} [NeZero n] :
    WFun4 n a b c →ₗ[F]
      ↑(WDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun W :=
    ⟨KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W, by
      rw [← range_KWMap_eq_WDiffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d)]
      exact ⟨W, rfl⟩⟩
  map_add' W W' := by
    apply Subtype.ext
    exact
      (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_add W W'
  map_smul' r W := by
    apply Subtype.ext
    exact
      (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r W

theorem sqdiagKWMapToWDiff_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagKWMapToWDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro w
  have hw :
      w.1 ∈ LinearMap.range
        (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    rw [range_KWMap_eq_WDiffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)]
    exact w.2
  rcases hw with ⟨W, hW⟩
  refine ⟨W, ?_⟩
  apply Subtype.ext
  exact hW

noncomputable def sqdiagKWRootSection
    {n a b c d : ℕ} [NeZero n] :
    ↑(WDiffSpace (n := n) (b := b) (c := c) (d := d)) →ₗ[F]
      WFun4 n a b c :=
  Classical.choose
    ((sqdiagKWMapToWDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)).exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (sqdiagKWMapToWDiff_surjective
            (n := n) (a := a) (b := b) (c := c) (d := d))))

@[simp]
theorem sqdiagKWMapToWDiff_section
    {n a b c d : ℕ} [NeZero n]
    (w : ↑(WDiffSpace (n := n) (b := b) (c := c) (d := d))) :
    sqdiagKWMapToWDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagKWRootSection
          (n := n) (a := a) (b := b) (c := c) (d := d) w) =
      w := by
  unfold sqdiagKWRootSection
  let e :=
    (sqdiagKWMapToWDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)).exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (sqdiagKWMapToWDiff_surjective
            (n := n) (a := a) (b := b) (c := c) (d := d)))
  change
    ((sqdiagKWMapToWDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (Classical.choose e)) w = w
  have hright := Classical.choose_spec e
  rw [hright]
  rfl

@[simp]
theorem sqdiagKWRootSection_root
    {n a b c d : ℕ} [NeZero n]
    (w : ↑(WDiffSpace (n := n) (b := b) (c := c) (d := d))) :
    KWMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagKWRootSection
          (n := n) (a := a) (b := b) (c := c) (d := d) w) =
      w.1 := by
  exact congrArg Subtype.val
    (sqdiagKWMapToWDiff_section
      (n := n) (a := a) (b := b) (c := c) (d := d) w)

noncomputable def sqdiagReducedRootProfileBRootYDiff
    {n b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F]
      ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun p :=
    ⟨pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1,
      (range_pullYZ_le_inf_YZ
        (n := n) (b := b) (c := c) (d := d)
        ⟨p.1.1.1, rfl⟩).1⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (pullYZ (n := n) (b := b) (c := c) (d := d)).map_add
        x.1.1.1 y.1.1.1
  map_smul' r x := by
    apply Subtype.ext
    exact
      (pullYZ (n := n) (b := b) (c := c) (d := d)).map_smul r x.1.1.1

@[simp]
theorem sqdiagReducedRootProfileBRootYDiff_apply
    {n b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileBRootYDiff
        (n := n) (b := b) (c := c) (d := d) p).1 =
      pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 :=
  rfl

noncomputable def sqdiagReducedRootProfileWRootWDiff
    {n b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F]
      ↑(WDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun p :=
    ⟨pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1,
      (range_pullZW_le_inf_ZW
        (n := n) (b := b) (c := c) (d := d)
        ⟨p.1.2.1, rfl⟩).2⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (pullZW (n := n) (b := b) (c := c) (d := d)).map_add
        x.1.2.1 y.1.2.1
  map_smul' r x := by
    apply Subtype.ext
    exact
      (pullZW (n := n) (b := b) (c := c) (d := d)).map_smul r x.1.2.1

@[simp]
theorem sqdiagReducedRootProfileWRootWDiff_apply
    {n b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileWRootWDiff
        (n := n) (b := b) (c := c) (d := d) p).1 =
      pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1 :=
  rfl

noncomputable def sqdiagReducedRootProfileSharedRootYDiff
    {n b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F]
      ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun p :=
    ⟨pullYZW (n := n) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixCube (n := n) p.2),
      (range_pullYZW_le_inf_YZW
        (n := n) (b := b) (c := c) (d := d)
        ⟨sqdiagSharedMatrixCube (n := n) p.2, rfl⟩).1.1⟩
  map_add' x y := by
    apply Subtype.ext
    change
      pullYZW (n := n) (b := b) (c := c) (d := d)
          (sqdiagSharedMatrixCube (n := n) (x.2 + y.2)) =
        pullYZW (n := n) (b := b) (c := c) (d := d)
            (sqdiagSharedMatrixCube (n := n) x.2) +
          pullYZW (n := n) (b := b) (c := c) (d := d)
            (sqdiagSharedMatrixCube (n := n) y.2)
    rw [(sqdiagSharedMatrixCube (n := n)).map_add,
      (pullYZW (n := n) (b := b) (c := c) (d := d)).map_add]
  map_smul' r x := by
    apply Subtype.ext
    change
      pullYZW (n := n) (b := b) (c := c) (d := d)
          (sqdiagSharedMatrixCube (n := n) (r • x.2)) =
        r • pullYZW (n := n) (b := b) (c := c) (d := d)
          (sqdiagSharedMatrixCube (n := n) x.2)
    rw [(sqdiagSharedMatrixCube (n := n)).map_smul,
      (pullYZW (n := n) (b := b) (c := c) (d := d)).map_smul]

@[simp]
theorem sqdiagReducedRootProfileSharedRootYDiff_apply
    {n b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileSharedRootYDiff
        (n := n) (b := b) (c := c) (d := d) p).1 =
      pullYZW (n := n) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixCube (n := n) p.2) :=
  rfl

noncomputable def sqdiagReducedRootProfileBRootYDiffFull
    {n b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F]
      ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d)) :=
  sqdiagReducedRootProfileBRootYDiff
      (n := n) (b := b) (c := c) (d := d) +
    sqdiagReducedRootProfileSharedRootYDiff
      (n := n) (b := b) (c := c) (d := d)

@[simp]
theorem sqdiagReducedRootProfileBRootYDiffFull_apply
    {n b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileBRootYDiffFull
        (n := n) (b := b) (c := c) (d := d) p).1 =
      pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
        pullYZW (n := n) (b := b) (c := c) (d := d)
          (sqdiagSharedMatrixCube (n := n) p.2) := by
  rfl

noncomputable def sqdiagReducedRootProfileBSource
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F] BFun4 n a c d :=
  (sqdiagKBRootSection
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileBRootYDiff
      (n := n) (b := b) (c := c) (d := d))

@[simp]
theorem sqdiagReducedRootProfileBSource_root
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileBSource
          (n := n) (a := a) (b := b) (c := c) (d := d) p) =
      pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 := by
  simp [sqdiagReducedRootProfileBSource]

noncomputable def sqdiagReducedRootProfileBSourceFull
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F] BFun4 n a c d :=
  (sqdiagKBRootSection
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileBRootYDiffFull
      (n := n) (b := b) (c := c) (d := d))

@[simp]
theorem sqdiagReducedRootProfileBSourceFull_root
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileBSourceFull
          (n := n) (a := a) (b := b) (c := c) (d := d) p) =
      pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
        pullYZW (n := n) (b := b) (c := c) (d := d)
          (sqdiagSharedMatrixCube (n := n) p.2) := by
  simp [sqdiagReducedRootProfileBSourceFull]

noncomputable def sqdiagReducedRootProfileWSource
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F] WFun4 n a b c :=
  (sqdiagKWRootSection
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileWRootWDiff
      (n := n) (b := b) (c := c) (d := d))

@[simp]
theorem sqdiagReducedRootProfileWSource_root
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    KWMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileWSource
          (n := n) (a := a) (b := b) (c := c) (d := d) p) =
      pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1 := by
  simp [sqdiagReducedRootProfileWSource]

noncomputable def sqdiagReducedRootProfileBSourceFullDiag
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F] BDiagCoeff n a d :=
  (BDiagOfBLinear (n := n) (a := a) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileBSourceFull
      (n := n) (a := a) (b := b) (c := c) (d := d))

@[simp]
theorem sqdiagReducedRootProfileBSourceFullDiag_apply
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileBSourceFullDiag
        (n := n) (a := a) (b := b) (c := c) (d := d) p =
      BDiagOfB (n := n) (a := a) (c := c) (d := d)
        (sqdiagReducedRootProfileBSourceFull
          (n := n) (a := a) (b := b) (c := c) (d := d) p) :=
  rfl

theorem sqdiagReducedRootProfileBSourceFullDiag_embed
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    BDiagEmbed (n := n) (a := a) (b := b) (d := d)
        (sqdiagReducedRootProfileBSourceFullDiag
          (n := n) (a := a) (b := b) (c := c) (d := d) p) =
      ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
        (sqdiagReducedRootProfileBSourceFull
          (n := n) (a := a) (b := b) (c := c) (d := d) p) := by
  exact
    BDiagEmbed_BDiagOfB_eq_squareCompat_B
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileBSourceFull
        (n := n) (a := a) (b := b) (c := c) (d := d) p)

noncomputable def sqdiagReducedRootProfileWSourceDiag
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F] WDiagCoeff n a b :=
  (WDiagOfWLinear (n := n) (a := a) (b := b) (c := c)).comp
    (sqdiagReducedRootProfileWSource
      (n := n) (a := a) (b := b) (c := c) (d := d))

@[simp]
theorem sqdiagReducedRootProfileWSourceDiag_apply
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileWSourceDiag
        (n := n) (a := a) (b := b) (c := c) (d := d) p =
      WDiagOfW (n := n) (a := a) (b := b) (c := c)
        (sqdiagReducedRootProfileWSource
          (n := n) (a := a) (b := b) (c := c) (d := d) p) :=
  rfl

theorem sqdiagReducedRootProfileWSourceDiag_embed
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    WDiagEmbed (n := n) (a := a) (b := b) (d := d)
        (sqdiagReducedRootProfileWSourceDiag
          (n := n) (a := a) (b := b) (c := c) (d := d) p) =
      ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
        (sqdiagReducedRootProfileWSource
          (n := n) (a := a) (b := b) (c := c) (d := d) p) := by
  exact
    WDiagEmbed_WDiagOfW_eq_squareCompat_W
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileWSource
        (n := n) (a := a) (b := b) (c := c) (d := d) p)

noncomputable def sqdiagReducedRootProfileFullPairProduct
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  LinearMap.prod
    ((SquareBMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d)).rangeRestrict.comp
      (sqdiagReducedRootProfileBSourceFull
        (n := n) (a := a) (b := b) (c := c) (d := d)))
    ((SquareWMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d)).rangeRestrict.comp
      (sqdiagReducedRootProfileWSource
        (n := n) (a := a) (b := b) (c := c) (d := d)))

@[simp]
theorem sqdiagReducedRootProfileFullPairProduct_root
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 =
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p := by
  change
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileBSourceFull
          (n := n) (a := a) (b := b) (c := c) (d := d) p) +
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileWSource
          (n := n) (a := a) (b := b) (c := c) (d := d) p) =
    sqdiagReducedRootProfileRootTarget
      (n := n) (b := b) (c := c) (d := d) p
  rw [sqdiagReducedRootProfileBSourceFull_root,
    sqdiagReducedRootProfileWSource_root]
  change
    (pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
        pullYZW (n := n) (b := b) (c := c) (d := d)
          (sqdiagSharedMatrixCube (n := n) p.2)) +
      pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1 =
    pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
      pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1 +
        pullYZW (n := n) (b := b) (c := c) (d := d)
          (sqdiagSharedMatrixCube (n := n) p.2)
  abel

theorem sqdiagReducedRootProfileFullPairProduct_root_mem_ZDiff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rw [sqdiagReducedRootProfileFullPairProduct_root]
  exact
    sqdiagReducedRootProfileRootTarget_mem_ZDiff
      (n := n) (b := b) (c := c) (d := d) hb hc hd p

@[simp]
theorem sqdiagReducedRootProfileFullPairProduct_coeff
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 =
      ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
        (sqdiagReducedRootProfileBSourceFull
          (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
          (sqdiagReducedRootProfileWSource
          (n := n) (a := a) (b := b) (c := c) (d := d) p) := by
  rfl

noncomputable def sqdiagReducedRootProfileFullCoeffMap
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F] CFun4 n a b d :=
  (LinearMap.snd F (RootTarget n b c d) (CFun4 n a b d)).comp
    ((sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d)))

@[simp]
theorem sqdiagReducedRootProfileFullCoeffMap_apply
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileFullCoeffMap
        (n := n) (a := a) (b := b) (c := c) (d := d) p =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 :=
  rfl

theorem sqdiagReducedRootProfileFullCoeffMap_diagDecomp
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileFullCoeffMap
        (n := n) (a := a) (b := b) (c := c) (d := d) p =
      BDiagEmbed (n := n) (a := a) (b := b) (d := d)
          (sqdiagReducedRootProfileBSourceFullDiag
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        WDiagEmbed (n := n) (a := a) (b := b) (d := d)
          (sqdiagReducedRootProfileWSourceDiag
            (n := n) (a := a) (b := b) (c := c) (d := d) p) := by
  rw [sqdiagReducedRootProfileFullCoeffMap_apply,
    sqdiagReducedRootProfileFullPairProduct_coeff,
    ← sqdiagReducedRootProfileBSourceFullDiag_embed
        (n := n) (a := a) (b := b) (c := c) (d := d) p,
    ← sqdiagReducedRootProfileWSourceDiag_embed
        (n := n) (a := a) (b := b) (c := c) (d := d) p]

noncomputable def sqdiagReducedRootProfileZTargetCoeffMap
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F] CFun4 n a b d :=
  (LinearMap.snd F (RootTarget n b c d) (CFun4 n a b d)).comp
    (sqdiagReducedRootProfileZTarget
      (n := n) (a := a) (b := b) (c := c) (d := d))

@[simp]
theorem sqdiagReducedRootProfileZTargetCoeffMap_apply
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileZTargetCoeffMap
        (n := n) (a := a) (b := b) (c := c) (d := d) p =
      (sqdiagReducedRootProfileZTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) p).2 :=
  rfl

noncomputable def sqdiagReducedRootProfileFullCoeffError
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F] CFun4 n a b d :=
  sqdiagReducedRootProfileFullCoeffMap
      (n := n) (a := a) (b := b) (c := c) (d := d) +
    sqdiagReducedRootProfileZTargetCoeffMap
      (n := n) (a := a) (b := b) (c := c) (d := d)

@[simp]
theorem sqdiagReducedRootProfileFullCoeffError_apply
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileFullCoeffError
        (n := n) (a := a) (b := b) (c := c) (d := d) p =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 +
        (sqdiagReducedRootProfileZTarget
          (n := n) (a := a) (b := b) (c := c) (d := d) p).2 :=
  rfl

abbrev sqdiagReducedRootProfileFullCoeffMatchesZTarget
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) : Prop :=
  (sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 =
    (sqdiagReducedRootProfileZTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) p).2

theorem sqdiagReducedRootProfileFullCoeffMatchesZTarget_iff_error_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileFullCoeffMatchesZTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) p ↔
      sqdiagReducedRootProfileFullCoeffError
        (n := n) (a := a) (b := b) (c := c) (d := d) p = 0 := by
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 =
      (sqdiagReducedRootProfileZTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) p).2 ↔
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 +
      (sqdiagReducedRootProfileZTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) p).2 = 0
  constructor
  · intro h
    rw [h]
    exact F_module_add_self _
  · intro h
    exact (add_eq_zero_iff_eq_of_F_module _ _).mp h

theorem sqdiagReducedRootProfileFullPairProduct_pairAdd_eq_ZTarget_of_coeff
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d)
    (hcoeff :
      sqdiagReducedRootProfileFullCoeffMatchesZTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) p) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p) =
      sqdiagReducedRootProfileZTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) p := by
  apply Prod.ext
  · rw [sqdiagReducedRootProfileFullPairProduct_root,
      sqdiagReducedRootProfileZTarget_root]
  · exact hcoeff

noncomputable def sqdiagReducedRootProfileExternalPairProduct
    {n a b c d : ℕ} [NeZero n] :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  LinearMap.prod
    ((SquareBMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d)).rangeRestrict.comp
      (sqdiagReducedRootProfileBSource
        (n := n) (a := a) (b := b) (c := c) (d := d)))
    ((SquareWMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d)).rangeRestrict.comp
      (sqdiagReducedRootProfileWSource
        (n := n) (a := a) (b := b) (c := c) (d := d)))

@[simp]
theorem sqdiagReducedRootProfileExternalPairProduct_root
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 =
      pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
        pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1 := by
  change
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileBSource
          (n := n) (a := a) (b := b) (c := c) (d := d) p) +
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileWSource
          (n := n) (a := a) (b := b) (c := c) (d := d) p) =
    pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
      pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1
  rw [sqdiagReducedRootProfileBSource_root,
    sqdiagReducedRootProfileWSource_root]

theorem sqdiagReducedRootProfileExternalPairProduct_root_mem_ZDiff
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  have hYZ :
      pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
    (range_pullYZ_le_inf_YZ
      (n := n) (b := b) (c := c) (d := d)
      ⟨p.1.1.1, rfl⟩).2
  have hZW :
      pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
    (range_pullZW_le_inf_ZW
      (n := n) (b := b) (c := c) (d := d)
      ⟨p.1.2.1, rfl⟩).1
  rw [sqdiagReducedRootProfileExternalPairProduct_root]
  exact (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem hYZ hZW

set_option synthInstance.maxHeartbeats 300000 in
noncomputable def sqdiagAmbientPairPresentationOfLinearProduct
    {X : Type*} [AddCommGroup X] [Module F X]
    {n a b c d : ℕ} [NeZero n]
    (P : X →ₗ[F] SqdiagAdjointAmbientPairProduct n a b c d)
    (hP :
      ∀ x : X,
        sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) (P x) ∈
          sqdiagZAdjointTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d)) :
    X →ₗ[F] SqdiagAdjointAmbientPairPresentation n a b c d where
  toFun x := ⟨P x, hP x⟩
  map_add' x y := by
    apply Subtype.ext
    exact P.map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact P.map_smul r x

@[simp]
theorem sqdiagAmbientPairPresentationOfLinearProduct_apply_val
    {X : Type*} [AddCommGroup X] [Module F X]
    {n a b c d : ℕ} [NeZero n]
    (P : X →ₗ[F] SqdiagAdjointAmbientPairProduct n a b c d)
    (hP :
      ∀ x : X,
        sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) (P x) ∈
          sqdiagZAdjointTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d))
    (x : X) :
    (sqdiagAmbientPairPresentationOfLinearProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) P hP x).1 =
      P x :=
  rfl

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRootProfileExternalPairProduct_mem_presentation_of_coeffWitness
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d)
    (hcoeff :
      ∃ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileExternalPairProduct
              (n := n) (a := a) (b := b) (c := c) (d := d) p)).2) :
    sqdiagReducedRootProfileExternalPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  apply (sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRootProfileExternalPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) p)).mpr
  apply (sqdiagZAdjointTargetSubmodule_mem_iff
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileExternalPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p))).mpr
  exact
    ⟨sqdiagReducedRootProfileExternalPairProduct_root_mem_ZDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) p,
      hcoeff⟩

theorem sqdiagKCAdjointCoeff_exists_of_rangeEmbed
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (C : CFun4 n a b d)
    (hC :
      C ∈ LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d))) :
    ∃ A : RootTarget n b c d,
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A = C := by
  have hRange :
      C ∈ LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    rwa [range_sqdiagKCAdjointMap_eq_rangeEmbed
      (n := n) (a := a) (b := b) (c := c) (d := d) hc]
  rcases hRange with ⟨A, hA⟩
  exact ⟨A, by simpa [sqdiagKCAdjointMap_apply] using hA⟩

theorem sqdiagKCAdjointCoeff_exists_iff_rangeEmbed
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (C : CFun4 n a b d) :
    (∃ A : RootTarget n b c d,
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A = C) ↔
      C ∈ LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) := by
  constructor
  · rintro ⟨A, hA⟩
    have hRange :
        C ∈ LinearMap.range
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) :=
      ⟨A, by simpa [sqdiagKCAdjointMap_apply] using hA⟩
    rwa [range_sqdiagKCAdjointMap_eq_rangeEmbed
      (n := n) (a := a) (b := b) (c := c) (d := d) hc] at hRange
  · exact sqdiagKCAdjointCoeff_exists_of_rangeEmbed
      (n := n) (a := a) (b := b) (c := c) (d := d) hc C

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRootProfileFullPairProduct_mem_presentation_of_coeffWitness
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d)
    (hcoeff :
      ∃ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileFullPairProduct
              (n := n) (a := a) (b := b) (c := c) (d := d) p)).2) :
    sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  apply (sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRootProfileFullPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) p)).mpr
  apply (sqdiagZAdjointTargetSubmodule_mem_iff
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p))).mpr
  exact
    ⟨sqdiagReducedRootProfileFullPairProduct_root_mem_ZDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p,
      hcoeff⟩

theorem sqdiagReducedRootProfileFullPairProduct_mem_presentation_of_coeff_rangeEmbed
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d)
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact
    sqdiagReducedRootProfileFullPairProduct_mem_presentation_of_coeffWitness
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p
      (sqdiagKCAdjointCoeff_exists_of_rangeEmbed
        (n := n) (a := a) (b := b) (c := c) (d := d) hc
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p)).2
        hcoeff)

abbrev sqdiagReducedRootProfileFullCoeffInRange
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) : Prop :=
  (sqdiagAdjointAmbientPairAdd
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRootProfileFullPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 ∈
    LinearMap.range
      (sqdiagKCAdjointRangeEmbed
        (n := n) (a := a) (b := b) (d := d))

theorem sqdiagReducedRootProfileFullCoeffInRange_of_coeffMatchesZTarget
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d)
    (hcoeff :
      sqdiagReducedRootProfileFullCoeffMatchesZTarget
        (n := n) (a := a) (b := b) (c := c) (d := d) p) :
    sqdiagReducedRootProfileFullCoeffInRange
      (n := n) (a := a) (b := b) (c := c) (d := d) p := by
  change
    (sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 ∈
      LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d))
  rw [hcoeff, sqdiagReducedRootProfileZTarget_coeff]
  exact ⟨sqdiagSharedMatrixKCRangeModel (n := n) (b := b) (d := d) p.2, rfl⟩

theorem sqdiagReducedRootProfileFullCoeffInRange_of_coeffError_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d)
    (herror :
      sqdiagReducedRootProfileFullCoeffError
        (n := n) (a := a) (b := b) (c := c) (d := d) p = 0) :
    sqdiagReducedRootProfileFullCoeffInRange
      (n := n) (a := a) (b := b) (c := c) (d := d) p := by
  exact
    sqdiagReducedRootProfileFullCoeffInRange_of_coeffMatchesZTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) p
      ((sqdiagReducedRootProfileFullCoeffMatchesZTarget_iff_error_eq_zero
        (n := n) (a := a) (b := b) (c := c) (d := d) p).mpr herror)

theorem sqdiagReducedRootProfileFullPairProduct_target_mem_of_coeff_range
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p) ∈
      sqdiagZAdjointTargetSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact
    (sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p)).mp
      (sqdiagReducedRootProfileFullPairProduct_mem_presentation_of_coeff_rangeEmbed
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p
        (hcoeff p))

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileFullPairPresentationOfCoeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairPresentation n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p,
      sqdiagReducedRootProfileFullPairProduct_mem_presentation_of_coeff_rangeEmbed
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p
        (hcoeff p)⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x

@[simp]
theorem sqdiagReducedRootProfileFullPairPresentationOfCoeffRange_val
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileFullPairPresentationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd hcoeff p).1 =
      sqdiagReducedRootProfileFullPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p :=
  rfl

noncomputable def sqdiagReducedRootProfileFullRelationOfCoeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p) :
    SqdiagReducedRootProfile n b d →ₗ[F] SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointAmbientPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileFullPairPresentationOfCoeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff)

@[simp]
theorem sqdiagReducedRootProfileFullRelationOfCoeffRange_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullRelationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd hcoeff p)).1 =
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p := by
  change
    (sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairPresentationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd hcoeff p)).1.1.1 =
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p
  rw [sqdiagAdjointAmbientPairPresentationSum_root_apply]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 =
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p
  exact
    sqdiagReducedRootProfileFullPairProduct_root
      (n := n) (a := a) (b := b) (c := c) (d := d) p

theorem sqdiagReducedRootProfileFullRelationOfCoeffRange_mem_ZDiff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullRelationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd hcoeff p)).1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rw [sqdiagReducedRootProfileFullRelationOfCoeffRange_root]
  exact
    sqdiagReducedRootProfileRootTarget_mem_ZDiff
      (n := n) (b := b) (c := c) (d := d) hb hc hd p

theorem sqdiagReducedRootProfileFullRelationOfCoeffRange_mem_verticalOrthogonal_of_pair
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d)
    (hp :
      sqdiagReducedRootProfileFullPairPresentationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p ∈
        sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagReducedRootProfileFullRelationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d := by
  exact
    sqdiagAdjointAmbientPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileFullPairPresentationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p)
      hp

theorem sqdiagReducedRootProfileFullRelationOfCoeffRange_rootTarget_mem_annihilator_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullRelationOfCoeffRange
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd hcoeff p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p ∈
      sqdiagRootZeroACoeffAnnihilator n a b c d := by
  apply
    (sqdiagRootZeroACoeffAnnihilator_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p)).mpr
  intro A hA
  have hrootZero :=
    (sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileFullRelationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd hcoeff p)).mp (horth p) A hA
  change
    sqdiagRootCoeffApply
        (n := n) (b := b) (c := c) (d := d) A
        ((sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullRelationOfCoeffRange
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd hcoeff p)).1) = 0 at hrootZero
  rwa [sqdiagReducedRootProfileFullRelationOfCoeffRange_root
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd hcoeff p] at hrootZero

theorem sqdiagReducedRootProfileFullRelationOfCoeffRange_Q_eq_zero_of_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileFullPairProduct
              (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileFullPairProduct
                (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullRelationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p) = 0 := by
  change
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairPresentationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p) = 0
  apply
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileFullPairPresentationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p)
  intro A hA
  exact hzero p A hA

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileFullVerticalOrthogonalOfCoeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullRelationOfCoeffRange
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationVerticalOrthogonal n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileFullRelationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p,
      horth p⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileFullRelationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileFullRelationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff).map_smul r x

noncomputable def sqdiagReducedRootProfileFullToDefectOfCoeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullRelationOfCoeffRange
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  (sqdiagReducedRelationVerticalOrthogonalToRootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileFullVerticalOrthogonalOfCoeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff horth)

@[simp]
theorem sqdiagReducedRootProfileFullToDefectOfCoeffRange_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullRelationOfCoeffRange
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileFullToDefectOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff horth p).1.1 =
      sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullRelationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p) := by
  exact
    sqdiagReducedRelationVerticalOrthogonalToRootDefect_apply
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileFullVerticalOrthogonalOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff horth p)

@[simp]
theorem sqdiagReducedRootProfileFullToDefectOfCoeffRange_rootTarget
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileFullRelationOfCoeffRange
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileFullToDefectOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hcoeff horth p).1.1.1 =
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p := by
  rw [sqdiagReducedRootProfileFullToDefectOfCoeffRange_root,
    sqdiagReducedRootProfileFullRelationOfCoeffRange_root]

theorem sqdiagReducedRootProfileExternalPairProduct_mem_presentation_of_coeff_rangeEmbed
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (p : SqdiagReducedRootProfile n b d)
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    sqdiagReducedRootProfileExternalPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact
    sqdiagReducedRootProfileExternalPairProduct_mem_presentation_of_coeffWitness
      (n := n) (a := a) (b := b) (c := c) (d := d) p
      (sqdiagKCAdjointCoeff_exists_of_rangeEmbed
        (n := n) (a := a) (b := b) (c := c) (d := d) hc
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileExternalPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p)).2
        hcoeff)

abbrev sqdiagReducedRootProfileExternalCoeffInRange
    {n a b c d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) : Prop :=
  (sqdiagAdjointAmbientPairAdd
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRootProfileExternalPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 ∈
    LinearMap.range
      (sqdiagKCAdjointRangeEmbed
        (n := n) (a := a) (b := b) (d := d))

theorem sqdiagReducedRootProfileExternalPairProduct_target_mem_of_coeff_range
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p) ∈
      sqdiagZAdjointTargetSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  exact
    (sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileExternalPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p)).mp
      (sqdiagReducedRootProfileExternalPairProduct_mem_presentation_of_coeff_rangeEmbed
        (n := n) (a := a) (b := b) (c := c) (d := d) hc p
        (hcoeff p))

set_option synthInstance.maxHeartbeats 500000 in
-- The target is a nested ambient-presentation subtype over two range subtypes.
noncomputable def sqdiagReducedRootProfileExternalPairPresentationOfCoeffRange
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairPresentation n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileExternalPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p,
      sqdiagReducedRootProfileExternalPairProduct_mem_presentation_of_coeff_rangeEmbed
        (n := n) (a := a) (b := b) (c := c) (d := d) hc p
        (hcoeff p)⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileExternalPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileExternalPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x

@[simp]
theorem sqdiagReducedRootProfileExternalPairPresentationOfCoeffRange_val
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileExternalPairPresentationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p).1 =
      sqdiagReducedRootProfileExternalPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) p :=
  rfl

noncomputable def sqdiagReducedRootProfileExternalRelationOfCoeffRange
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p) :
    SqdiagReducedRootProfile n b d →ₗ[F] SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointAmbientPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileExternalPairPresentationOfCoeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff)

@[simp]
theorem sqdiagReducedRootProfileExternalRelationOfCoeffRange_root
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalRelationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p)).1 =
      pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
        pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1 := by
  change
    (sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalPairPresentationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p)).1.1.1 =
      pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
        pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1
  rw [sqdiagAdjointAmbientPairPresentationSum_root_apply]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 =
      pullYZ (n := n) (b := b) (c := c) (d := d) p.1.1.1 +
        pullZW (n := n) (b := b) (c := c) (d := d) p.1.2.1
  exact
    sqdiagReducedRootProfileExternalPairProduct_root
      (n := n) (a := a) (b := b) (c := c) (d := d) p

theorem sqdiagReducedRootProfileExternalRelationOfCoeffRange_mem_ZDiff
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalRelationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p)).1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rw [sqdiagReducedRootProfileExternalRelationOfCoeffRange_root]
  rw [← sqdiagReducedRootProfileExternalPairProduct_root
    (n := n) (a := a) (b := b) (c := c) (d := d) p]
  exact
    sqdiagReducedRootProfileExternalPairProduct_root_mem_ZDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) p

theorem sqdiagReducedRootProfileExternalRelationOfCoeffRange_mem_verticalOrthogonal_of_pair
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (p : SqdiagReducedRootProfile n b d)
    (hp :
      sqdiagReducedRootProfileExternalPairPresentationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p ∈
        sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagReducedRootProfileExternalRelationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d := by
  exact
    sqdiagAdjointAmbientPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileExternalPairPresentationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p)
      hp

theorem sqdiagReducedRootProfileExternalRelationOfCoeffRange_Q_eq_zero_of_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileExternalPairProduct
              (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileExternalPairProduct
                (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalRelationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p) = 0 := by
  change
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalPairPresentationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p) = 0
  apply
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileExternalPairPresentationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p)
  intro A hA
  exact hzero p A hA

set_option synthInstance.maxHeartbeats 500000 in
-- The codomain is the vertical-orthogonal kernel subtype of the reduced relation.
noncomputable def sqdiagReducedRootProfileExternalVerticalOrthogonalOfCoeffRange
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalRelationOfCoeffRange
            (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationVerticalOrthogonal n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileExternalRelationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p,
      horth p⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileExternalRelationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileExternalRelationOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff).map_smul r x

noncomputable def sqdiagReducedRootProfileExternalToDefectOfCoeffRange
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalRelationOfCoeffRange
            (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  (sqdiagReducedRelationVerticalOrthogonalToRootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileExternalVerticalOrthogonalOfCoeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff horth)

@[simp]
theorem sqdiagReducedRootProfileExternalToDefectOfCoeffRange_root
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c)
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalCoeffInRange
          (n := n) (a := a) (b := b) (c := c) (d := d) p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileExternalRelationOfCoeffRange
            (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileExternalToDefectOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff horth p).1.1 =
      sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileExternalRelationOfCoeffRange
          (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff p) := by
  exact
    sqdiagReducedRelationVerticalOrthogonalToRootDefect_apply
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileExternalVerticalOrthogonalOfCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hc hcoeff horth p)

noncomputable def sqdiagSquareBWIntersectionCoreParamSection
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SquareCoreParam n →ₗ[F] SquareBWIntersection n a b c d :=
  Classical.choose
    ((sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (sqdiagSquareBWIntersectionCoreParamRead_surjective
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)))

@[simp]
theorem sqdiagSquareBWIntersectionCoreParamRead_section
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SquareCoreParam n) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSquareBWIntersectionCoreParamSection
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) =
      p := by
  unfold sqdiagSquareBWIntersectionCoreParamSection
  let e :=
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (sqdiagSquareBWIntersectionCoreParamRead_surjective
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd))
  change
    ((sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
      (Classical.choose e)) p = p
  have hright := Classical.choose_spec e
  rw [hright]
  rfl

noncomputable def sqdiagSquareBWIntersectionCoreParamReadKernelEquivModelTraceKernel
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    LinearMap.ker
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd) ≃ₗ[F]
      LinearMap.ker (SquareBWModelTrace (n := n) (a := a) (c := c)) where
  toFun x :=
    let E :=
      SquareBWIntersectionEquivModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
    ⟨E x.1, by
      apply LinearMap.mem_ker.mpr
      have hx0 :
          sqdiagSquareBWIntersectionCoreParamRead
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x.1 = 0 :=
        LinearMap.mem_ker.mp x.2
      have hread :
          SquareCoreAllowedRead (n := n)
              (SquareBWModelTrace (n := n) (a := a) (c := c) (E x.1)) =
            SquareCoreAllowedRead (n := n) (0 : SquareCoreAllowed n) := by
        change
          sqdiagSquareBWIntersectionCoreParamRead
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x.1 =
            SquareCoreAllowedRead (n := n) (0 : SquareCoreAllowed n)
        rw [hx0, (SquareCoreAllowedRead (n := n)).map_zero]
      exact
        (SquareCoreAllowedEquivParam (n := n)).injective hread⟩
  invFun y :=
    let E :=
      SquareBWIntersectionEquivModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
    ⟨E.symm y.1, by
      apply LinearMap.mem_ker.mpr
      have htrace := LinearMap.mem_ker.mp y.2
      rw [sqdiagSquareBWIntersectionCoreParamRead_apply]
      change
        SquareCoreAllowedRead (n := n)
            (SquareBWModelTrace (n := n) (a := a) (c := c) (E (E.symm y.1))) = 0
      rw [E.apply_symm_apply, htrace]
      exact (SquareCoreAllowedRead (n := n)).map_zero⟩
  left_inv x := by
    apply Subtype.ext
    let E :=
      SquareBWIntersectionEquivModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
    change E.symm (E x.1) = x.1
    exact E.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    let E :=
      SquareBWIntersectionEquivModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
    change E (E.symm y.1) = y.1
    exact E.apply_symm_apply y.1
  map_add' x y := by
    apply Subtype.ext
    let E :=
      SquareBWIntersectionEquivModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
    change E (x.1 + y.1) = E x.1 + E y.1
    exact E.map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    let E :=
      SquareBWIntersectionEquivModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
    change E (r • x.1) = r • E x.1
    exact E.map_smul r x

noncomputable def sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    LinearMap.ker
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd) ≃ₗ[F]
      (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
        LinearMap.ker (SquareCompatTrace (n := n) (a := a))) :=
  (sqdiagSquareBWIntersectionCoreParamReadKernelEquivModelTraceKernel
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).trans
    (ker_SquareBWModelTrace_equiv (n := n) (a := a) (c := c))

@[simp]
theorem sqdiagSquareBWIntersectionCoreParamReadKernelEquivModelTraceKernel_val
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x :
      LinearMap.ker
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)) :
    (sqdiagSquareBWIntersectionCoreParamReadKernelEquivModelTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).1 =
      SquareBWIntersectionToModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x.1 := by
  rfl

@[simp]
theorem sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x :
      LinearMap.ker
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)) :
    (sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).1.1 =
      SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x.1 := by
  rfl

@[simp]
theorem sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel_compat
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x :
      LinearMap.ker
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)) :
    (sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).2.1 =
      SquareBWIntersectionCompatCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x.1 := by
  rfl

theorem sqdiagSquareBWIntersectionCoreParamRead_add_kernel
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d)
    (k :
      LinearMap.ker
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (x + k.1) =
      sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x := by
  rw [(sqdiagSquareBWIntersectionCoreParamRead
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).map_add]
  rw [LinearMap.mem_ker.mp k.2, add_zero]

theorem sqdiagSquareBWIntersectionRootCoeff_add_kernel
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d)
    (k :
      LinearMap.ker
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)) :
    SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
        (x + k.1) =
      SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x +
        (sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd k).1.1 := by
  rw [(SquareBWIntersectionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add]
  rw [sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel_root
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd k]

theorem sqdiagSquareBWIntersectionCompatCoeff_add_kernel
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d)
    (k :
      LinearMap.ker
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)) :
    SquareBWIntersectionCompatCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
        (x + k.1) =
      SquareBWIntersectionCompatCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x +
        (sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd k).2.1 := by
  rw [(SquareBWIntersectionCompatCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add]
  rw [sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel_compat
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd k]

noncomputable def sqdiagSquareBWIntersectionCoreParamSectionTwist
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SquareCoreParam n →ₗ[F] SquareBWIntersection n a b c d)
    (K :
      SquareCoreParam n →ₗ[F]
        LinearMap.ker
          (sqdiagSquareBWIntersectionCoreParamRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)) :
    SquareCoreParam n →ₗ[F] SquareBWIntersection n a b c d :=
  L +
    (LinearMap.ker
      (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)).subtype.comp K

@[simp]
theorem sqdiagSquareBWIntersectionCoreParamSectionTwist_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SquareCoreParam n →ₗ[F] SquareBWIntersection n a b c d)
    (K :
      SquareCoreParam n →ₗ[F]
        LinearMap.ker
          (sqdiagSquareBWIntersectionCoreParamRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd))
    (p : SquareCoreParam n) :
    sqdiagSquareBWIntersectionCoreParamSectionTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L K p =
      L p + (K p).1 :=
  rfl

theorem sqdiagSquareBWIntersectionCoreParamRead_sectionTwist
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SquareCoreParam n →ₗ[F] SquareBWIntersection n a b c d)
    (K :
      SquareCoreParam n →ₗ[F]
        LinearMap.ker
          (sqdiagSquareBWIntersectionCoreParamRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd))
    (p : SquareCoreParam n) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSquareBWIntersectionCoreParamSectionTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L K p) =
      sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd (L p) := by
  rw [sqdiagSquareBWIntersectionCoreParamSectionTwist_apply]
  exact
    sqdiagSquareBWIntersectionCoreParamRead_add_kernel
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd (L p) (K p)

theorem sqdiagSquareBWIntersectionCoreParamSectionTwist_is_section
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SquareCoreParam n →ₗ[F] SquareBWIntersection n a b c d)
    (K :
      SquareCoreParam n →ₗ[F]
        LinearMap.ker
          (sqdiagSquareBWIntersectionCoreParamRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd))
    (hL :
      ∀ p : SquareCoreParam n,
        sqdiagSquareBWIntersectionCoreParamRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd (L p) = p)
    (p : SquareCoreParam n) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSquareBWIntersectionCoreParamSectionTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L K p) =
      p := by
  rw [sqdiagSquareBWIntersectionCoreParamRead_sectionTwist]
  exact hL p

theorem sqdiagSquareBWIntersectionCoreParamSectionTwist_rootCoeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SquareCoreParam n →ₗ[F] SquareBWIntersection n a b c d)
    (K :
      SquareCoreParam n →ₗ[F]
        LinearMap.ker
          (sqdiagSquareBWIntersectionCoreParamRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd))
    (p : SquareCoreParam n) :
    SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
        (sqdiagSquareBWIntersectionCoreParamSectionTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L K p) =
      SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd (L p) +
        (sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd (K p)).1.1 := by
  rw [sqdiagSquareBWIntersectionCoreParamSectionTwist_apply]
  exact
    sqdiagSquareBWIntersectionRootCoeff_add_kernel
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd (L p) (K p)

theorem sqdiagSquareBWIntersectionCoreParamSectionTwist_compatCoeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SquareCoreParam n →ₗ[F] SquareBWIntersection n a b c d)
    (K :
      SquareCoreParam n →ₗ[F]
        LinearMap.ker
          (sqdiagSquareBWIntersectionCoreParamRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd))
    (p : SquareCoreParam n) :
    SquareBWIntersectionCompatCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
        (sqdiagSquareBWIntersectionCoreParamSectionTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L K p) =
      SquareBWIntersectionCompatCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd (L p) +
        (sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd (K p)).2.1 := by
  rw [sqdiagSquareBWIntersectionCoreParamSectionTwist_apply]
  exact
    sqdiagSquareBWIntersectionCompatCoeff_add_kernel
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd (L p) (K p)

theorem finrank_sqdiagSquareBWIntersectionCoreParamRead_ker
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker
          (sqdiagSquareBWIntersectionCoreParamRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)) =
      Module.finrank F (LinearMap.ker (SquareRootTrace (n := n) (c := c))) +
        Module.finrank F (LinearMap.ker (SquareCompatTrace (n := n) (a := a))) := by
  calc
    Module.finrank F
        (LinearMap.ker
          (sqdiagSquareBWIntersectionCoreParamRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd))
        = Module.finrank F
            (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
              LinearMap.ker (SquareCompatTrace (n := n) (a := a))) := by
          exact LinearEquiv.finrank_eq
            (sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)
    _ = Module.finrank F (LinearMap.ker (SquareRootTrace (n := n) (c := c))) +
        Module.finrank F (LinearMap.ker (SquareCompatTrace (n := n) (a := a))) := by
          rw [Module.finrank_prod]

theorem sqdiagSquareBWIntersection_root_mem_ZDiff_iff_range_pullYZW
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    x.1.1 ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) ↔
      x.1.1 ∈ LinearMap.range
        (pullYZW (n := n) (b := b) (c := c) (d := d)) := by
  constructor
  · intro hZ
    have hYW :
        x.1.1 ∈
          YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
            WDiffSpace (n := n) (b := b) (c := c) (d := d) :=
      (SquareBWIntersectionRootSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) x).2
    have hYZW :
        x.1.1 ∈
          (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
              ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
            WDiffSpace (n := n) (b := b) (c := c) (d := d) :=
      ⟨⟨hYW.1, hZ⟩, hYW.2⟩
    rwa [← range_pullYZW_eq_inf_YZW
      (n := n) (b := b) (c := c) (d := d) hb hc hd] at hYZW
  · intro hRange
    exact
      ((range_pullYZW_le_inf_YZW
        (n := n) (b := b) (c := c) (d := d)) hRange).1.2

theorem sqdiagSquareBWIntersection_root_mem_range_pullYZW_iff_rootCoeff_range_zMatrixSlices
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    x.1.1 ∈ LinearMap.range
        (pullYZW (n := n) (b := b) (c := c) (d := d)) ↔
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) := by
  have hiff :=
    pullYW_mem_range_pullYZW_iff_ywCoeff_range_zMatrixSlices
      (n := n) (b := b) (c := c) (d := d) hb hd
      (SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x)
  rwa [pullYW_SquareBWIntersectionRootCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x] at hiff

theorem sqdiagSquareBWIntersection_root_mem_ZDiff_iff_rootCoeff_range_zMatrixSlices
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    x.1.1 ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) ↔
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) := by
  rw [sqdiagSquareBWIntersection_root_mem_ZDiff_iff_range_pullYZW
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x,
    sqdiagSquareBWIntersection_root_mem_range_pullYZW_iff_rootCoeff_range_zMatrixSlices
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x]

theorem sqdiagSquareBWIntersection_coreBuildR_read_eq_rootTrace
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    coreBuildR (n := n)
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).1
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).2 =
      SquareRootTrace (n := n) (c := c)
        (SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) := by
  funext z
  apply Subtype.ext
  funext sy sw
  exact
    sqdiagSquareBWIntersection_coreBuildAVal_read_eq_trace_root
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x z sy sw

theorem sqdiagSquareBWIntersection_rootCoeff_range_zMatrixSlices_coreBuildR_read_mem_traceRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d)
    (hroot :
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    coreBuildR (n := n)
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).1
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).2 ∈
      LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) := by
  rcases hroot with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  rw [sqdiagSquareRootTraceZMatrixSlices_apply, hS]
  exact
    (sqdiagSquareBWIntersection_coreBuildR_read_eq_rootTrace
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).symm

noncomputable def sqdiagSquareBWIntersectionTargetCoeff
    {n a b c d : ℕ} [NeZero n] :
    SquareBWIntersection n a b c d →ₗ[F] CFun4 n a b d where
  toFun x := x.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem sqdiagSquareBWIntersectionTargetCoeff_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SquareBWIntersection n a b c d) :
    sqdiagSquareBWIntersectionTargetCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) x =
      x.1.2 :=
  rfl

noncomputable def sqdiagSquareRootTraceSectionLinear
    {n c : ℕ} [NeZero n] (hc : 0 < c) :
    SquareRootCore n →ₗ[F] YWCoeff n c where
  toFun R := SquareRootTraceSection (n := n) (c := c) hc R
  map_add' R R' := by
    funext z
    apply Subtype.ext
    funext sy sw
    by_cases hz : z = vecSumRep (n := n) (k := c) hc (vecSum z)
    · dsimp [SquareRootTraceSection]
      rw [if_pos hz, if_pos hz, if_pos hz]
      rfl
    · dsimp [SquareRootTraceSection]
      rw [if_neg hz, if_neg hz, if_neg hz]
      rfl
  map_smul' r R := by
    funext z
    apply Subtype.ext
    funext sy sw
    by_cases hz : z = vecSumRep (n := n) (k := c) hc (vecSum z)
    · dsimp [SquareRootTraceSection]
      rw [if_pos hz, if_pos hz]
      rfl
    · dsimp [SquareRootTraceSection]
      rw [if_neg hz, if_neg hz]
      rfl

@[simp]
theorem sqdiagSquareRootTraceSectionLinear_apply
    {n c : ℕ} [NeZero n] (hc : 0 < c) (R : SquareRootCore n) :
    sqdiagSquareRootTraceSectionLinear (n := n) (c := c) hc R =
      SquareRootTraceSection (n := n) (c := c) hc R :=
  rfl

@[simp]
theorem sqdiagSquareRootTrace_sectionLinear_trace
    {n c : ℕ} [NeZero n] (hc : 0 < c) (R : SquareRootCore n) :
    SquareRootTrace (n := n) (c := c)
        (sqdiagSquareRootTraceSectionLinear (n := n) (c := c) hc R) =
      R := by
  funext sz
  exact SquareRootTrace_section_apply (n := n) (c := c) hc R sz

noncomputable def sqdiagSquareCompatTraceSectionLinear
    {n a : ℕ} [NeZero n] :
    SquareCompatCore n →ₗ[F] SquareCompatCoeff n a where
  toFun S := SquareCompatTraceSection (n := n) (a := a) S
  map_add' S T := by
    funext p t
    apply Subtype.ext
    funext sy sw
    by_cases hp : p = 0
    · simp [SquareCompatTraceSection, hp]
    · simp [SquareCompatTraceSection, hp]
  map_smul' r S := by
    funext p t
    apply Subtype.ext
    funext sy sw
    by_cases hp : p = 0
    · simp [SquareCompatTraceSection, hp]
    · simp [SquareCompatTraceSection, hp]

@[simp]
theorem sqdiagSquareCompatTraceSectionLinear_apply
    {n a : ℕ} [NeZero n] (S : SquareCompatCore n) :
    sqdiagSquareCompatTraceSectionLinear (n := n) (a := a) S =
      SquareCompatTraceSection (n := n) (a := a) S :=
  rfl

@[simp]
theorem sqdiagSquareCompatTrace_sectionLinear_trace
    {n a : ℕ} [NeZero n] (S : SquareCompatCore n) :
    SquareCompatTrace (n := n) (a := a)
        (sqdiagSquareCompatTraceSectionLinear (n := n) (a := a) S) =
      S := by
  funext t
  exact SquareCompatTrace_section_apply (n := n) (a := a) S t

noncomputable def sqdiagSquareBWModelTraceSection
    {n a c : ℕ} [NeZero n] (hc : 0 < c) :
    SquareCoreAllowed n →ₗ[F] SquareBWModel n a c where
  toFun x :=
    ⟨(sqdiagSquareRootTraceSectionLinear (n := n) (c := c) hc x.1.1,
      sqdiagSquareCompatTraceSectionLinear (n := n) (a := a) x.1.2), by
        rw [mem_SquareBWModel_iff]
        change
          (SquareRootTrace (n := n) (c := c)
              (sqdiagSquareRootTraceSectionLinear (n := n) (c := c) hc x.1.1),
            SquareCompatTrace (n := n) (a := a)
              (sqdiagSquareCompatTraceSectionLinear (n := n) (a := a) x.1.2)) ∈
            SquareCoreAllowed n
        rw [sqdiagSquareRootTrace_sectionLinear_trace,
          sqdiagSquareCompatTrace_sectionLinear_trace]
        exact x.2⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · exact (sqdiagSquareRootTraceSectionLinear
        (n := n) (c := c) hc).map_add x.1.1 y.1.1
    · exact (sqdiagSquareCompatTraceSectionLinear
        (n := n) (a := a)).map_add x.1.2 y.1.2
  map_smul' r x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (sqdiagSquareRootTraceSectionLinear
        (n := n) (c := c) hc).map_smul r x.1.1
    · exact (sqdiagSquareCompatTraceSectionLinear
        (n := n) (a := a)).map_smul r x.1.2

@[simp]
theorem sqdiagSquareBWModelTrace_traceSection
    {n a c : ℕ} [NeZero n] (hc : 0 < c)
    (x : SquareCoreAllowed n) :
    SquareBWModelTrace (n := n) (a := a) (c := c)
        (sqdiagSquareBWModelTraceSection (n := n) (a := a) (c := c) hc x) =
      x := by
  apply Subtype.ext
  apply Prod.ext
  · exact sqdiagSquareRootTrace_sectionLinear_trace
      (n := n) (c := c) hc x.1.1
  · exact sqdiagSquareCompatTrace_sectionLinear_trace
      (n := n) (a := a) x.1.2

noncomputable def sqdiagSquareBWIntersectionCoreParamBuildExplicit
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SquareCoreParam n →ₗ[F] SquareBWIntersection n a b c d :=
  (SquareBWIntersectionEquivModel
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm.toLinearMap.comp
    ((sqdiagSquareBWModelTraceSection
        (n := n) (a := a) (c := c) hc).comp
      (SquareCoreAllowedEquivParam (n := n)).symm.toLinearMap)

@[simp]
theorem sqdiagSquareBWIntersectionCoreParamRead_buildExplicit
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SquareCoreParam n) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSquareBWIntersectionCoreParamBuildExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) =
      p := by
  change
    SquareCoreAllowedRead (n := n)
      (SquareBWModelTrace (n := n) (a := a) (c := c)
        (SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          ((SquareBWIntersectionEquivModel
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm
            (sqdiagSquareBWModelTraceSection
              (n := n) (a := a) (c := c) hc
              ((SquareCoreAllowedEquivParam (n := n)).symm p))))) = p
  let E :=
    SquareBWIntersectionEquivModel
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
  let m : SquareBWModel n a c :=
    sqdiagSquareBWModelTraceSection
      (n := n) (a := a) (c := c) hc
      ((SquareCoreAllowedEquivParam (n := n)).symm p)
  have hmodel :
      SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (E.symm m) = m := by
    change E (E.symm m) = m
    exact E.apply_symm_apply m
  change SquareCoreAllowedRead (n := n)
      (SquareBWModelTrace (n := n) (a := a) (c := c)
        (SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (E.symm m))) = p
  rw [hmodel]
  rw [sqdiagSquareBWModelTrace_traceSection]
  exact (SquareCoreAllowedEquivParam (n := n)).apply_symm_apply p

noncomputable def sqdiagSquareBWIntersectionBPairAmbient
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F] BPairAmbient n a b c d where
  toFun x :=
    BPairAmbientOfTraceData
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x)
      (SquareBWIntersectionCompatCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change
        pullYW (n := n) (b := b) (c := c) (d := d)
            (SquareBWIntersectionRootCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd (x + y)) =
          pullYW (n := n) (b := b) (c := c) (d := d)
              (SquareBWIntersectionRootCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) +
            pullYW (n := n) (b := b) (c := c) (d := d)
              (SquareBWIntersectionRootCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hd y)
      rw [(SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add,
        (pullYW (n := n) (b := b) (c := c) (d := d)).map_add]
    · apply Subtype.ext
      change
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
            (SquareBWIntersectionCompatCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd (x + y)) =
          SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
              (SquareBWIntersectionCompatCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) +
            SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
              (SquareBWIntersectionCompatCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hd y)
      rw [(SquareBWIntersectionCompatCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add,
        (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)).map_add]
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      change
        pullYW (n := n) (b := b) (c := c) (d := d)
            (SquareBWIntersectionRootCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd (r • x)) =
          r • pullYW (n := n) (b := b) (c := c) (d := d)
            (SquareBWIntersectionRootCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x)
      rw [(SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_smul,
        (pullYW (n := n) (b := b) (c := c) (d := d)).map_smul]
    · apply Subtype.ext
      change
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
            (SquareBWIntersectionCompatCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd (r • x)) =
          r • SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
            (SquareBWIntersectionCompatCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x)
      rw [(SquareBWIntersectionCompatCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_smul,
        (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)).map_smul]

noncomputable def sqdiagSquareBWIntersectionWPairAmbient
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F] WPairAmbient n a b c d where
  toFun x :=
    WPairAmbientOfTraceData
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x)
      (SquareBWIntersectionCompatCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change
        pullYW (n := n) (b := b) (c := c) (d := d)
            (SquareBWIntersectionRootCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd (x + y)) =
          pullYW (n := n) (b := b) (c := c) (d := d)
              (SquareBWIntersectionRootCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) +
            pullYW (n := n) (b := b) (c := c) (d := d)
              (SquareBWIntersectionRootCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hd y)
      rw [(SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add,
        (pullYW (n := n) (b := b) (c := c) (d := d)).map_add]
    · apply Subtype.ext
      change
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
            (SquareBWIntersectionCompatCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd (x + y)) =
          SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
              (SquareBWIntersectionCompatCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) +
            SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
              (SquareBWIntersectionCompatCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hd y)
      rw [(SquareBWIntersectionCompatCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add,
        (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)).map_add]
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      change
        pullYW (n := n) (b := b) (c := c) (d := d)
            (SquareBWIntersectionRootCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd (r • x)) =
          r • pullYW (n := n) (b := b) (c := c) (d := d)
            (SquareBWIntersectionRootCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x)
      rw [(SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_smul,
        (pullYW (n := n) (b := b) (c := c) (d := d)).map_smul]
    · apply Subtype.ext
      change
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
            (SquareBWIntersectionCompatCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd (r • x)) =
          r • SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
            (SquareBWIntersectionCompatCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x)
      rw [(SquareBWIntersectionCompatCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_smul,
        (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)).map_smul]

theorem sqdiagSquareBWIntersectionBPairAmbient_mem_range
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    sqdiagSquareBWIntersectionBPairAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x ∈
      LinearMap.range
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [← ker_BPairCurlMap_eq_range_SquareBMapAmbient
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc]
  simpa [sqdiagSquareBWIntersectionBPairAmbient, SquareBWIntersectionToModel,
    SquareBWIntersectionRead] using
    BPairAmbientOfTraceData_mem_ker_pairCurl
      (n := n) (a := a) (b := b) (c := c) (d := d) hb
      (SquareBWIntersectionToModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)

theorem sqdiagSquareBWIntersectionWPairAmbient_mem_range
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    sqdiagSquareBWIntersectionWPairAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x ∈
      LinearMap.range
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [← ker_WPairCurlMap_eq_range_SquareWMapAmbient
    (n := n) (a := a) (b := b) (c := c) (d := d) hc hd]
  simpa [sqdiagSquareBWIntersectionWPairAmbient, SquareBWIntersectionToModel,
    SquareBWIntersectionRead] using
    WPairAmbientOfTraceData_mem_ker_pairCurl
      (n := n) (a := a) (b := b) (c := c) (d := d) hd
      (SquareBWIntersectionToModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)

noncomputable def sqdiagSquareBWIntersectionBOnlyPairProduct
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d where
  toFun x :=
    (⟨sqdiagSquareBWIntersectionBPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x,
        sqdiagSquareBWIntersectionBPairAmbient_mem_range
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x⟩,
      0)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact
        (sqdiagSquareBWIntersectionBPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add x y
    · rfl
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      exact
        (sqdiagSquareBWIntersectionBPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_smul r x
    · rfl

@[simp]
theorem sqdiagSquareBWIntersectionBOnlyPairProduct_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionBOnlyPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).1 =
      x.1.1 := by
  change
    pullYW (n := n) (b := b) (c := c) (d := d)
        (SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) +
      0 =
    x.1.1
  rw [add_zero]
  exact
    pullYW_SquareBWIntersectionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x

@[simp]
theorem sqdiagSquareBWIntersectionBOnlyPairProduct_coeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionBOnlyPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).2 =
      x.1.2 := by
  change
    SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
        (SquareBWIntersectionCompatCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) +
      0 =
    x.1.2
  rw [add_zero]
  exact
    SquareCompatEmbed_SquareBWIntersectionCompatCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x

@[simp]
theorem sqdiagSquareBWIntersectionBOnlyPairProduct_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionBOnlyPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x) =
      x.1 := by
  apply Prod.ext
  · exact
      sqdiagSquareBWIntersectionBOnlyPairProduct_root
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x
  · exact
      sqdiagSquareBWIntersectionBOnlyPairProduct_coeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x

theorem sqdiagSquareBWIntersectionBOnlyPairProduct_mem_presentation
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d)
    (hx :
      x.1 ∈ sqdiagZAdjointTargetSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d)) :
    sqdiagSquareBWIntersectionBOnlyPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
  simpa using hx

noncomputable def sqdiagSquareBWIntersectionWOnlyPairProduct
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d where
  toFun x :=
    (0,
      ⟨sqdiagSquareBWIntersectionWPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x,
        sqdiagSquareBWIntersectionWPairAmbient_mem_range
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x⟩)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact
        (sqdiagSquareBWIntersectionWPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add x y
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact
        (sqdiagSquareBWIntersectionWPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_smul r x

@[simp]
theorem sqdiagSquareBWIntersectionWOnlyPairProduct_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionWOnlyPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).1 =
      x.1.1 := by
  change
    0 +
      pullYW (n := n) (b := b) (c := c) (d := d)
        (SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) =
    x.1.1
  rw [zero_add]
  exact
    pullYW_SquareBWIntersectionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x

@[simp]
theorem sqdiagSquareBWIntersectionWOnlyPairProduct_coeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionWOnlyPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).2 =
      x.1.2 := by
  change
    0 +
      SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
        (SquareBWIntersectionCompatCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) =
    x.1.2
  rw [zero_add]
  exact
    SquareCompatEmbed_SquareBWIntersectionCompatCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x

@[simp]
theorem sqdiagSquareBWIntersectionWOnlyPairProduct_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionWOnlyPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x) =
      x.1 := by
  apply Prod.ext
  · exact
      sqdiagSquareBWIntersectionWOnlyPairProduct_root
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x
  · exact
      sqdiagSquareBWIntersectionWOnlyPairProduct_coeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x

theorem sqdiagSquareBWIntersectionWOnlyPairProduct_mem_presentation
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d)
    (hx :
      x.1 ∈ sqdiagZAdjointTargetSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d)) :
    sqdiagSquareBWIntersectionWOnlyPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
  simpa using hx

noncomputable def sqdiagSquareBWIntersectionKernelPairProduct
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d where
  toFun x :=
    (⟨sqdiagSquareBWIntersectionBPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x,
        sqdiagSquareBWIntersectionBPairAmbient_mem_range
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x⟩,
      ⟨sqdiagSquareBWIntersectionWPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x,
        sqdiagSquareBWIntersectionWPairAmbient_mem_range
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x⟩)
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · exact
        (sqdiagSquareBWIntersectionBPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add x y
    · exact
        (sqdiagSquareBWIntersectionWPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add x y
  map_smul' r x := by
    apply Prod.ext <;> apply Subtype.ext
    · exact
        (sqdiagSquareBWIntersectionBPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_smul r x
    · exact
        (sqdiagSquareBWIntersectionWPairAmbient
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_smul r x

@[simp]
theorem sqdiagSquareBWIntersectionKernelPairProduct_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionKernelPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).1 = 0 := by
  change
    pullYW (n := n) (b := b) (c := c) (d := d)
        (SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) +
      pullYW (n := n) (b := b) (c := c) (d := d)
        (SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) =
    0
  exact F_module_add_self _

@[simp]
theorem sqdiagSquareBWIntersectionKernelPairProduct_coeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionKernelPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).2 = 0 := by
  change
    SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
        (SquareBWIntersectionCompatCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) +
      SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
        (SquareBWIntersectionCompatCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) =
    0
  exact F_module_add_self _

set_option synthInstance.maxHeartbeats 300000 in
noncomputable def sqdiagSquareBWIntersectionKernelPairPresentation
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F]
      SqdiagAdjointAmbientPairPresentation n a b c d where
  toFun x :=
    ⟨sqdiagSquareBWIntersectionKernelPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x,
      by
        rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
        apply (sqdiagZAdjointTargetSubmodule_mem_iff
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagSquareBWIntersectionKernelPairProduct
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x))).mpr
        constructor
        · rw [sqdiagSquareBWIntersectionKernelPairProduct_root
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x]
          exact (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).zero_mem
        · refine ⟨0, ?_⟩
          rw [sqdiagSquareBWIntersectionKernelPairProduct_coeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x]
          exact sqdiagKCAdjointCoeff_zero
            (n := n) (a := a) (b := b) (c := c) (d := d)⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagSquareBWIntersectionKernelPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagSquareBWIntersectionKernelPairProduct
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).map_smul r x

theorem sqdiagSquareBWIntersectionKernelPairPresentation_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    sqdiagSquareBWIntersectionKernelPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x ∈
      sqdiagAdjointAmbientPairPresentationVertical n a b c d := by
  apply sqdiagAdjointAmbientPairPresentation_mem_vertical_of_root_add_eq_zero
    (n := n) (a := a) (b := b) (c := c) (d := d)
  simpa [sqdiagSquareBWIntersectionKernelPairPresentation] using
    sqdiagSquareBWIntersectionKernelPairProduct_root
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x

noncomputable def sqdiagSharedMatrixCoreParam
    {n : ℕ} [NeZero n] :
    MatrixZeroSum n →ₗ[F] SquareCoreParam n where
  toFun S := (S, 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem sqdiagSharedMatrixCoreParam_fst
    {n : ℕ} [NeZero n] (S : MatrixZeroSum n) :
    (sqdiagSharedMatrixCoreParam (n := n) S).1 = S :=
  rfl

@[simp]
theorem sqdiagSharedMatrixCoreParam_snd
    {n : ℕ} [NeZero n] (S : MatrixZeroSum n) :
    (sqdiagSharedMatrixCoreParam (n := n) S).2 = 0 :=
  rfl

noncomputable def sqdiagSharedMatrixIntersectionExplicit
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    MatrixZeroSum n →ₗ[F] SquareBWIntersection n a b c d :=
  (sqdiagSquareBWIntersectionCoreParamBuildExplicit
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    (sqdiagSharedMatrixCoreParam (n := n))

@[simp]
theorem sqdiagSharedMatrixIntersectionExplicit_read
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSharedMatrixIntersectionExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S) =
      (S, 0) := by
  change
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSquareBWIntersectionCoreParamBuildExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagSharedMatrixCoreParam (n := n) S)) =
      (S, 0)
  simpa using
    sqdiagSquareBWIntersectionCoreParamRead_buildExplicit
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagSharedMatrixCoreParam (n := n) S)

@[simp]
theorem sqdiagSharedMatrixIntersectionExplicit_read_matrix
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSharedMatrixIntersectionExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)).1 =
      S := by
  exact congrArg Prod.fst
    (sqdiagSharedMatrixIntersectionExplicit_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

@[simp]
theorem sqdiagSharedMatrixIntersectionExplicit_read_line
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSharedMatrixIntersectionExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)).2 =
      0 := by
  exact congrArg Prod.snd
    (sqdiagSharedMatrixIntersectionExplicit_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

noncomputable def sqdiagLineCoreParam
    {n : ℕ} [NeZero n] :
    LineZeroSum n →ₗ[F] SquareCoreParam n where
  toFun P := (0, P)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem sqdiagLineCoreParam_fst
    {n : ℕ} [NeZero n] (P : LineZeroSum n) :
    (sqdiagLineCoreParam (n := n) P).1 = 0 :=
  rfl

@[simp]
theorem sqdiagLineCoreParam_snd
    {n : ℕ} [NeZero n] (P : LineZeroSum n) :
    (sqdiagLineCoreParam (n := n) P).2 = P :=
  rfl

noncomputable def sqdiagSquareCoreAllowedRoot
    {n : ℕ} [NeZero n] :
    SquareCoreAllowed n →ₗ[F] SquareRootCore n where
  toFun x := x.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def sqdiagSquareCoreParamRootBuild
    {n : ℕ} [NeZero n] :
    SquareCoreParam n →ₗ[F] SquareRootCore n :=
  (sqdiagSquareCoreAllowedRoot (n := n)).comp
    (SquareCoreAllowedEquivParam (n := n)).symm.toLinearMap

@[simp]
theorem sqdiagSquareCoreParamRootBuild_apply
    {n : ℕ} [NeZero n] (p : SquareCoreParam n) :
    sqdiagSquareCoreParamRootBuild (n := n) p =
      coreBuildR (n := n) p.1 p.2 :=
  rfl

noncomputable def sqdiagMatrixConstantRootCore
    {n : ℕ} [NeZero n] :
    MatrixZeroSum n →ₗ[F] SquareRootCore n :=
  (sqdiagSquareCoreParamRootBuild (n := n)).comp
    (sqdiagSharedMatrixCoreParam (n := n))

@[simp]
theorem sqdiagMatrixConstantRootCore_apply
    {n : ℕ} [NeZero n] (S : MatrixZeroSum n) :
    sqdiagMatrixConstantRootCore (n := n) S =
      coreBuildR (n := n) S 0 :=
  rfl

noncomputable def sqdiagLineCoreBuildR
    {n : ℕ} [NeZero n] :
    LineZeroSum n →ₗ[F] SquareRootCore n :=
  (sqdiagSquareCoreParamRootBuild (n := n)).comp
    (sqdiagLineCoreParam (n := n))

@[simp]
theorem sqdiagLineCoreBuildR_apply
    {n : ℕ} [NeZero n] (P : LineZeroSum n) :
    sqdiagLineCoreBuildR (n := n) P =
      coreBuildR (n := n) 0 P :=
  rfl

theorem sqdiagSquareCoreParamRootBuild_decomp
    {n : ℕ} [NeZero n] (S : MatrixZeroSum n) (P : LineZeroSum n) :
    sqdiagSquareCoreParamRootBuild (n := n) (S, P) =
      sqdiagMatrixConstantRootCore (n := n) S +
        sqdiagLineCoreBuildR (n := n) P := by
  have hparam :
      (S, P) =
        sqdiagSharedMatrixCoreParam (n := n) S +
          sqdiagLineCoreParam (n := n) P := by
    apply Prod.ext <;> simp
  rw [hparam]
  exact (sqdiagSquareCoreParamRootBuild (n := n)).map_add
    (sqdiagSharedMatrixCoreParam (n := n) S)
    (sqdiagLineCoreParam (n := n) P)

theorem sqdiag_coreBuildR_decomp
    {n : ℕ} [NeZero n] (S : MatrixZeroSum n) (P : LineZeroSum n) :
    coreBuildR (n := n) S P =
      sqdiagMatrixConstantRootCore (n := n) S +
        sqdiagLineCoreBuildR (n := n) P := by
  simpa using
    sqdiagSquareCoreParamRootBuild_decomp (n := n) S P

theorem sqdiagMatrixConstantRootCore_mem_range_lineCoreBuildR_of_coreBuildR_eq_zero
    {n : ℕ} [NeZero n] (S : MatrixZeroSum n) (P : LineZeroSum n)
    (hR : coreBuildR (n := n) S P = 0) :
    sqdiagMatrixConstantRootCore (n := n) S ∈
      LinearMap.range (sqdiagLineCoreBuildR (n := n)) := by
  refine ⟨P, ?_⟩
  have hsum :
      sqdiagMatrixConstantRootCore (n := n) S +
          sqdiagLineCoreBuildR (n := n) P = 0 := by
    rw [← sqdiag_coreBuildR_decomp (n := n) S P]
    exact hR
  exact (add_eq_zero_iff_eq_of_F_module _ _).mp hsum |>.symm

noncomputable def sqdiagLineCoreBuildRToRange
    {n : ℕ} [NeZero n] :
    LineZeroSum n →ₗ[F]
      LinearMap.range (sqdiagLineCoreBuildR (n := n)) :=
  LinearMap.codRestrict
    (LinearMap.range (sqdiagLineCoreBuildR (n := n)))
    (sqdiagLineCoreBuildR (n := n))
    (fun P => ⟨P, rfl⟩)

theorem sqdiagLineCoreBuildRToRange_surjective
    {n : ℕ} [NeZero n] :
    Function.Surjective (sqdiagLineCoreBuildRToRange (n := n)) := by
  intro y
  rcases y.2 with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  apply Subtype.ext
  exact hP

noncomputable def sqdiagLineCoreBuildRRangeSection
    {n : ℕ} [NeZero n] :
    LinearMap.range (sqdiagLineCoreBuildR (n := n)) →ₗ[F]
      LineZeroSum n :=
  Classical.choose
    ((sqdiagLineCoreBuildRToRange (n := n)).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (sqdiagLineCoreBuildRToRange_surjective (n := n))))

@[simp]
theorem sqdiagLineCoreBuildRToRange_section
    {n : ℕ} [NeZero n]
    (y : LinearMap.range (sqdiagLineCoreBuildR (n := n))) :
    sqdiagLineCoreBuildRToRange (n := n)
        (sqdiagLineCoreBuildRRangeSection (n := n) y) =
      y := by
  unfold sqdiagLineCoreBuildRRangeSection
  let e :=
    (sqdiagLineCoreBuildRToRange (n := n)).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (sqdiagLineCoreBuildRToRange_surjective (n := n)))
  change
    ((sqdiagLineCoreBuildRToRange (n := n)).comp
      (Classical.choose e)) y = y
  have hright := Classical.choose_spec e
  rw [hright]
  rfl

theorem sqdiagLineCoreBuildR_rangeSection_apply
    {n : ℕ} [NeZero n]
    (y : LinearMap.range (sqdiagLineCoreBuildR (n := n))) :
    sqdiagLineCoreBuildR (n := n)
        (sqdiagLineCoreBuildRRangeSection (n := n) y) =
      y.1 := by
  have hsection := sqdiagLineCoreBuildRToRange_section (n := n) y
  simpa [sqdiagLineCoreBuildRToRange] using congrArg Subtype.val hsection

noncomputable def sqdiagMatrixConstantRootCoreLineLift
    {n : ℕ} [NeZero n]
    (hM :
      LinearMap.range (sqdiagMatrixConstantRootCore (n := n)) ≤
        LinearMap.range (sqdiagLineCoreBuildR (n := n))) :
    MatrixZeroSum n →ₗ[F] LineZeroSum n :=
  (sqdiagLineCoreBuildRRangeSection (n := n)).comp
    (LinearMap.codRestrict
      (LinearMap.range (sqdiagLineCoreBuildR (n := n)))
      (sqdiagMatrixConstantRootCore (n := n))
      (fun S => hM ⟨S, rfl⟩))

theorem sqdiagLineCoreBuildR_matrixConstantRootCoreLineLift
    {n : ℕ} [NeZero n]
    (hM :
      LinearMap.range (sqdiagMatrixConstantRootCore (n := n)) ≤
        LinearMap.range (sqdiagLineCoreBuildR (n := n)))
    (S : MatrixZeroSum n) :
    sqdiagLineCoreBuildR (n := n)
        (sqdiagMatrixConstantRootCoreLineLift (n := n) hM S) =
      sqdiagMatrixConstantRootCore (n := n) S := by
  let y : LinearMap.range (sqdiagLineCoreBuildR (n := n)) :=
    ⟨sqdiagMatrixConstantRootCore (n := n) S, hM ⟨S, rfl⟩⟩
  have hy := sqdiagLineCoreBuildR_rangeSection_apply (n := n) y
  simpa [sqdiagMatrixConstantRootCoreLineLift, y] using hy

theorem sqdiag_coreBuildR_matrixConstantRootCoreLineLift_eq_zero
    {n : ℕ} [NeZero n]
    (hM :
      LinearMap.range (sqdiagMatrixConstantRootCore (n := n)) ≤
        LinearMap.range (sqdiagLineCoreBuildR (n := n)))
    (S : MatrixZeroSum n) :
    coreBuildR (n := n) S
        (sqdiagMatrixConstantRootCoreLineLift (n := n) hM S) =
      0 := by
  rw [sqdiag_coreBuildR_decomp,
    sqdiagLineCoreBuildR_matrixConstantRootCoreLineLift (n := n) hM S]
  exact F_module_add_self _

noncomputable def sqdiagReducedRootProfileLineLift
    {n b d : ℕ} [NeZero n]
    (hM :
      LinearMap.range (sqdiagMatrixConstantRootCore (n := n)) ≤
        LinearMap.range (sqdiagLineCoreBuildR (n := n))) :
    SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n where
  toFun p := sqdiagMatrixConstantRootCoreLineLift (n := n) hM p.2
  map_add' p q := by
    exact (sqdiagMatrixConstantRootCoreLineLift (n := n) hM).map_add p.2 q.2
  map_smul' r p := by
    exact (sqdiagMatrixConstantRootCoreLineLift (n := n) hM).map_smul r p.2

theorem sqdiagReducedRootProfileLineLift_coreBuildR_eq_zero
    {n b d : ℕ} [NeZero n]
    (hM :
      LinearMap.range (sqdiagMatrixConstantRootCore (n := n)) ≤
        LinearMap.range (sqdiagLineCoreBuildR (n := n)))
    (p : SqdiagReducedRootProfile n b d) :
    coreBuildR (n := n) p.2
        (sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM p) =
      0 :=
  sqdiag_coreBuildR_matrixConstantRootCoreLineLift_eq_zero (n := n) hM p.2

noncomputable def sqdiagReducedRootProfileCoreParamWithLine
    {n b d : ℕ} [NeZero n]
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] SquareCoreParam n where
  toFun p := (p.2, L p)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · exact L.map_add x y
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · exact L.map_smul r x

@[simp]
theorem sqdiagReducedRootProfileCoreParamWithLine_fst
    {n b d : ℕ} [NeZero n]
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileCoreParamWithLine
      (n := n) (b := b) (d := d) L p).1 = p.2 :=
  rfl

@[simp]
theorem sqdiagReducedRootProfileCoreParamWithLine_snd
    {n b d : ℕ} [NeZero n]
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileCoreParamWithLine
      (n := n) (b := b) (d := d) L p).2 = L p :=
  rfl

@[simp]
theorem sqdiagReducedRootProfileCoreParamWithLine_zero
    {n b d : ℕ} [NeZero n]
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileCoreParamWithLine
        (n := n) (b := b) (d := d)
        (0 : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) p =
      (p.2, 0) :=
  rfl

noncomputable def sqdiagReducedRootProfileCoreBuildRWithLine
    {n b d : ℕ} [NeZero n]
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] SquareRootCore n :=
  (sqdiagSquareCoreParamRootBuild (n := n)).comp
    (sqdiagReducedRootProfileCoreParamWithLine
      (n := n) (b := b) (d := d) L)

@[simp]
theorem sqdiagReducedRootProfileCoreBuildRWithLine_apply
    {n b d : ℕ} [NeZero n]
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileCoreBuildRWithLine
        (n := n) (b := b) (d := d) L p =
      coreBuildR (n := n) p.2 (L p) :=
  rfl

noncomputable def sqdiagReducedRootProfileIntersectionExplicitWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] SquareBWIntersection n a b c d :=
  (sqdiagSquareBWIntersectionCoreParamBuildExplicit
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    (sqdiagReducedRootProfileCoreParamWithLine
      (n := n) (b := b) (d := d) L)

@[simp]
theorem sqdiagReducedRootProfileIntersectionExplicitWithLine_read
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) =
      (p.2, L p) := by
  change
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSquareBWIntersectionCoreParamBuildExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileCoreParamWithLine
            (n := n) (b := b) (d := d) L p)) =
      (p.2, L p)
  simpa using
    sqdiagSquareBWIntersectionCoreParamRead_buildExplicit
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileCoreParamWithLine
        (n := n) (b := b) (d := d) L p)

@[simp]
theorem sqdiagReducedRootProfileIntersectionExplicitWithLine_read_matrix
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 =
      p.2 := by
  exact congrArg Prod.fst
    (sqdiagReducedRootProfileIntersectionExplicitWithLine_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)

@[simp]
theorem sqdiagReducedRootProfileIntersectionExplicitWithLine_read_line
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 =
      L p := by
  exact congrArg Prod.snd
    (sqdiagReducedRootProfileIntersectionExplicitWithLine_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)

theorem sqdiagReducedRootProfileIntersectionExplicitWithLine_trace_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) (z sy sw : I n) :
    coreBuildAVal (n := n) p.2 (L p) z sy sw =
      ((SquareBWModelTrace (n := n) (a := a) (c := c)
        (SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionExplicitWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L p))).1.1 z).1 sy sw := by
  have h :=
    sqdiagSquareBWIntersection_coreBuildAVal_read_eq_trace_root
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L p) z sy sw
  rw [sqdiagReducedRootProfileIntersectionExplicitWithLine_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p] at h
  exact h

theorem sqdiagReducedRootProfileIntersectionExplicitWithLine_trace_compat
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) (t sy sw : I n) :
    (coreBuildS (n := n) p.2 (L p) t).1 sy sw =
      ((SquareBWModelTrace (n := n) (a := a) (c := c)
        (SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionExplicitWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L p))).1.2 t).1 sy sw := by
  have h :=
    sqdiagSquareBWIntersection_coreBuildS_read_eq_trace_compat
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L p) t sy sw
  rw [sqdiagReducedRootProfileIntersectionExplicitWithLine_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p] at h
  exact h

@[simp]
theorem sqdiagReducedRootProfileIntersectionExplicitWithLine_root_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileIntersectionExplicitWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 =
      pullYW (n := n) (b := b) (c := c) (d := d)
        (sqdiagSquareRootTraceSectionLinear (n := n) (c := c) hc
          (coreBuildR (n := n) p.2 (L p))) :=
  rfl

theorem sqdiagReducedRootProfileIntersectionExplicitWithLine_root_eq_zero_of_coreBuildR
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hR : coreBuildR (n := n) p.2 (L p) = 0) :
    (sqdiagReducedRootProfileIntersectionExplicitWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 = 0 := by
  rw [sqdiagReducedRootProfileIntersectionExplicitWithLine_root_target,
    hR]
  rw [(sqdiagSquareRootTraceSectionLinear (n := n) (c := c) hc).map_zero]
  exact (pullYW (n := n) (b := b) (c := c) (d := d)).map_zero

theorem sqdiagReducedRootProfileIntersectionExplicitWithLine_root_mem_ZDiff_of_coreBuildR
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hR : coreBuildR (n := n) p.2 (L p) = 0) :
    (sqdiagReducedRootProfileIntersectionExplicitWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rw [sqdiagReducedRootProfileIntersectionExplicitWithLine_root_eq_zero_of_coreBuildR
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p hR]
  exact (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).zero_mem

@[simp]
theorem sqdiagReducedRootProfileIntersectionExplicitWithLine_coeff_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileIntersectionExplicitWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 =
      SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
        (sqdiagSquareCompatTraceSectionLinear (n := n) (a := a)
          (coreBuildS (n := n) p.2 (L p))) :=
  rfl

@[simp]
theorem sqdiagReducedRootProfileIntersectionExplicitWithLine_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (0 : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) p =
      sqdiagSharedMatrixIntersectionExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2 :=
  rfl

noncomputable def sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] YWCoeff n c :=
  (SquareBWIntersectionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).comp
    (sqdiagReducedRootProfileIntersectionExplicitWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)

@[simp]
theorem sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p =
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
          (sqdiagReducedRootProfileIntersectionExplicitWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :=
  rfl

noncomputable def sqdiagReducedRootProfileIntersectionExplicitCoeffWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] CFun4 n a b d :=
  (sqdiagSquareBWIntersectionTargetCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileIntersectionExplicitWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)

@[simp]
theorem sqdiagReducedRootProfileIntersectionExplicitCoeffWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionExplicitCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p =
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 :=
  rfl

noncomputable def sqdiagReducedRootProfileNormalizedCoeffWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] CFun4 n a b d :=
  sqdiagReducedRootProfileFullCoeffMap
      (n := n) (a := a) (b := b) (c := c) (d := d) +
    sqdiagReducedRootProfileIntersectionExplicitCoeffWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L

@[simp]
theorem sqdiagReducedRootProfileNormalizedCoeffWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p =
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 :=
  rfl

noncomputable def sqdiagReducedRootProfileCoreParamBOnlyPairProductWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  (sqdiagSquareBWIntersectionBOnlyPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    (sqdiagReducedRootProfileIntersectionExplicitWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)

@[simp]
theorem sqdiagReducedRootProfileCoreParamBOnlyPairProductWithLine_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileCoreParamBOnlyPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) =
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1 := by
  change
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionBOnlyPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionExplicitWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)) =
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1
  exact
    sqdiagSquareBWIntersectionBOnlyPairProduct_pairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)

noncomputable def sqdiagReducedRootProfileNormalizedPairProductWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  sqdiagReducedRootProfileFullPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) +
    sqdiagReducedRootProfileCoreParamBOnlyPairProductWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L

@[simp]
theorem sqdiagReducedRootProfileNormalizedPairProductWithLine_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) =
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1 := by
  change
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
          sqdiagReducedRootProfileCoreParamBOnlyPairProductWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) =
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1
  rw [(sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
    sqdiagReducedRootProfileCoreParamBOnlyPairProductWithLine_pairAdd]

theorem sqdiagReducedRootProfileNormalizedPairProductWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 := by
  rw [sqdiagReducedRootProfileNormalizedPairProductWithLine_pairAdd]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 +
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1
  rw [sqdiagReducedRootProfileFullPairProduct_root]

theorem sqdiagReducedRootProfileNormalizedPairProductWithLine_coeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 =
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 := by
  rw [sqdiagReducedRootProfileNormalizedPairProductWithLine_pairAdd]
  rfl

theorem sqdiagReducedRootProfileNormalizedPairProductWithLine_coeff_traceSection
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 =
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
          (sqdiagSquareCompatTraceSectionLinear (n := n) (a := a)
            (coreBuildS (n := n) p.2 (L p))) := by
  rw [sqdiagReducedRootProfileNormalizedPairProductWithLine_coeff]
  rfl

theorem sqdiagReducedRootProfileNormalizedPairProductWithLine_root_mem_ZDiff_iff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) ↔
    (sqdiagReducedRootProfileIntersectionExplicitWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  let A : RootTarget n b c d :=
    sqdiagReducedRootProfileRootTarget
      (n := n) (b := b) (c := c) (d := d) p
  let B : RootTarget n b c d :=
    (sqdiagReducedRootProfileIntersectionExplicitWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1
  have hA : A ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
    dsimp [A]
    exact
      sqdiagReducedRootProfileRootTarget_mem_ZDiff
        (n := n) (b := b) (c := c) (d := d) hb hc hd p
  have hroot :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 =
        A + B := by
    dsimp [A, B]
    exact
      sqdiagReducedRootProfileNormalizedPairProductWithLine_root
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
  constructor
  · intro h
    have hsum : A + B ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
      rwa [hroot] at h
    have hBA :
        (A + B) + A ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem hsum hA
    have hEq : (A + B) + A = B := by
      calc
        (A + B) + A = B + (A + A) := by abel
        _ = B + 0 := by rw [F_module_add_self A]
        _ = B := by rw [add_zero]
    rw [hEq] at hBA
    exact hBA
  · intro hB
    rw [hroot]
    exact
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem hA hB

theorem sqdiagReducedRootProfileNormalizedPairProductWithLine_mem_presentation_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hZ :
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) ∈
        sqdiagZAdjointTargetSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d)) :
    sqdiagReducedRootProfileNormalizedPairProductWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
  exact hZ

abbrev sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) : Prop :=
  sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairProductWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) ∈
    sqdiagZAdjointTargetSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
      ∃ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 := by
  exact
    sqdiagZAdjointTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p))

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionRoot
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
      ∃ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 := by
  rw [sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p,
    sqdiagReducedRootProfileNormalizedPairProductWithLine_root_mem_ZDiff_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p]

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_of_root_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d))
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  exact
    (sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mpr
      ⟨hroot,
        sqdiagKCAdjointCoeff_exists_of_rangeEmbed
          (n := n) (a := a) (b := b) (c := c) (d := d) hc
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2
          hcoeff⟩

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_of_intersectionRoot_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d))
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  exact
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_of_root_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
      ((sqdiagReducedRootProfileNormalizedPairProductWithLine_root_mem_ZDiff_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mpr hroot)
      hcoeff

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionRoot_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  constructor
  · intro h
    have hpair :=
      (sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionRoot
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mp h
    refine ⟨hpair.1, ?_⟩
    have hcoeff :
        (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
          LinearMap.range
            (sqdiagKCAdjointRangeEmbed
              (n := n) (a := a) (b := b) (d := d)) :=
      (sqdiagKCAdjointCoeff_exists_iff_rangeEmbed
        (n := n) (a := a) (b := b) (c := c) (d := d) hc
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2).mp
        hpair.2
    rwa [sqdiagReducedRootProfileNormalizedPairProductWithLine_coeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p] at hcoeff
  · intro h
    have hcoeff :
        (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
          LinearMap.range
            (sqdiagKCAdjointRangeEmbed
              (n := n) (a := a) (b := b) (d := d)) := by
      rw [sqdiagReducedRootProfileNormalizedPairProductWithLine_coeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p]
      exact h.2
    exact
      sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_of_intersectionRoot_coeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p h.1 hcoeff

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionRoot_rangePullYZW_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
        LinearMap.range
          (pullYZW (n := n) (b := b) (c := c) (d := d)) ∧
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  rw [sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionRoot_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p,
    sqdiagSquareBWIntersection_root_mem_ZDiff_iff_range_pullYZW
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)]

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionRootCoeff_rangeZMatrixSlices_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
          (sqdiagReducedRootProfileIntersectionExplicitWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) ∧
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  rw [sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionRoot_rangePullYZW_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p,
    sqdiagSquareBWIntersection_root_mem_range_pullYZW_iff_rootCoeff_range_zMatrixSlices
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)]

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionMaps_range
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) ∧
      sqdiagReducedRootProfileNormalizedCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  rw [sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionRootCoeff_rangeZMatrixSlices_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p]
  rfl

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  exact
    (sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mpr
      ⟨hroot ⟨p, rfl⟩, hcoeff ⟨p, rfl⟩⟩

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  intro p
  exact
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hroot hcoeff p

theorem sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine_range_le_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    LinearMap.range
        (sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
      LinearMap.range
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) := by
  intro y hy
  rcases hy with ⟨p, rfl⟩
  exact
    ((sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mp (hZ p)).1

theorem sqdiagReducedRootProfileNormalizedCoeffWithLine_range_le_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    LinearMap.range
        (sqdiagReducedRootProfileNormalizedCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
      LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) := by
  intro y hy
  rcases hy with ⟨p, rfl⟩
  exact
    ((sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mp (hZ p)).2

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_forall_iff_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    (∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) ↔
    LinearMap.range
        (sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
      LinearMap.range
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) ∧
    LinearMap.range
        (sqdiagReducedRootProfileNormalizedCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
      LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) := by
  constructor
  · intro hZ
    exact
      ⟨sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine_range_le_of_target
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ,
        sqdiagReducedRootProfileNormalizedCoeffWithLine_range_le_of_target
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ⟩
  · intro hmaps
    exact
      sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hmaps.1 hmaps.2

theorem sqdiagReducedRootProfileIntersectionExplicitRootCoeff_range_zMatrixSlices_coreBuildR_mem_traceRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    coreBuildR (n := n) p.2 (L p) ∈
      LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) := by
  have h :=
    sqdiagSquareBWIntersection_rootCoeff_range_zMatrixSlices_coreBuildR_read_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
      hroot
  change
    coreBuildR (n := n)
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionExplicitWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionExplicitWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
      LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) at h
  rw [sqdiagReducedRootProfileIntersectionExplicitWithLine_read
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p] at h
  exact h

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_le_traceRange_of_explicitRootCoeff_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) ≤
      LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) := by
  intro R hR
  rcases hR with ⟨p, rfl⟩
  simpa using
    sqdiagReducedRootProfileIntersectionExplicitRootCoeff_range_zMatrixSlices_coreBuildR_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
      (hroot ⟨p, rfl⟩)

theorem sqdiagReducedRootProfileIntersectionExplicitRootCoeff_range_zMatrixSlices_coreBuildR_mem_zeroSumProfileM_one
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := 1) (d := d)
          hb Nat.zero_lt_one hd L p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := 1))) :
    coreBuildR (n := n) p.2 (L p) ∈
      ZeroSumProfileM n (MatrixZeroSum n) := by
  have htrace :=
    sqdiagReducedRootProfileIntersectionExplicitRootCoeff_range_zMatrixSlices_coreBuildR_mem_traceRange
      (n := n) (a := a) (b := b) (c := 1) (d := d)
      hb Nat.zero_lt_one hd L p hroot
  simpa using htrace

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_le_zeroSumProfileM_of_explicitRootCoeff_range_le_one
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := 1) (d := d)
            hb Nat.zero_lt_one hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := 1))) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) ≤
      ZeroSumProfileM n (MatrixZeroSum n) := by
  have htrace :=
    sqdiagReducedRootProfileCoreBuildRWithLine_range_le_traceRange_of_explicitRootCoeff_range_le
      (n := n) (a := a) (b := b) (c := 1) (d := d)
      hb Nat.zero_lt_one hd L hroot
  simpa using htrace

theorem sqdiagReducedRootProfileIntersectionExplicitRootCoeff_range_zMatrixSlices_coreBuildR_mem_zeroSumProfileM_of_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    coreBuildR (n := n) p.2 (L p) ∈
      ZeroSumProfileM n (MatrixZeroSum n) := by
  have htrace :=
    sqdiagReducedRootProfileIntersectionExplicitRootCoeff_range_zMatrixSlices_coreBuildR_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L p hroot
  rw [sqdiagSquareRootTraceZMatrixSlices_range_eq_zeroSumProfileM_of_odd
    (n := n) (c := c) hc hn] at htrace
  exact htrace

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_le_zeroSumProfileM_of_explicitRootCoeff_range_le_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) ≤
      ZeroSumProfileM n (MatrixZeroSum n) := by
  have htrace :=
    sqdiagReducedRootProfileCoreBuildRWithLine_range_le_traceRange_of_explicitRootCoeff_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hroot
  rw [sqdiagSquareRootTraceZMatrixSlices_range_eq_zeroSumProfileM_of_odd
    (n := n) (c := c) hc hn] at htrace
  exact htrace

theorem sqdiagReducedRootProfileIntersectionExplicitRootCoeff_range_zMatrixSlices_coreBuildR_eq_zero_of_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    coreBuildR (n := n) p.2 (L p) = 0 := by
  have htrace :=
    sqdiagReducedRootProfileIntersectionExplicitRootCoeff_range_zMatrixSlices_coreBuildR_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L p hroot
  rw [sqdiagSquareRootTraceZMatrixSlices_range_eq_bot_of_even_two_le
    (n := n) (c := c) hn hc2] at htrace
  simpa using htrace

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_eq_bot_of_explicitRootCoeff_range_le_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionExplicitRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) =
      ⊥ := by
  apply le_antisymm
  · have htrace :=
      sqdiagReducedRootProfileCoreBuildRWithLine_range_le_traceRange_of_explicitRootCoeff_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hroot
    rw [sqdiagSquareRootTraceZMatrixSlices_range_eq_bot_of_even_two_le
      (n := n) (c := c) hn hc2] at htrace
    exact htrace
  · exact bot_le

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_coreBuildR_mem_zeroSumProfileM_of_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hZ :
      sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    coreBuildR (n := n) p.2 (L p) ∈
      ZeroSumProfileM n (MatrixZeroSum n) := by
  have hmaps :=
    (sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mp hZ
  exact
    sqdiagReducedRootProfileIntersectionExplicitRootCoeff_range_zMatrixSlices_coreBuildR_mem_zeroSumProfileM_of_odd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd hn L p hmaps.1

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_le_zeroSumProfileM_of_explicitTarget_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) ≤
      ZeroSumProfileM n (MatrixZeroSum n) := by
  intro R hR
  rcases hR with ⟨p, rfl⟩
  rw [sqdiagReducedRootProfileCoreBuildRWithLine_apply]
  exact
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_coreBuildR_mem_zeroSumProfileM_of_odd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd hn L p (hZ p)

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_coreBuildR_eq_zero_of_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hZ :
      sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    coreBuildR (n := n) p.2 (L p) = 0 := by
  have hmaps :=
    (sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mp hZ
  exact
    sqdiagReducedRootProfileIntersectionExplicitRootCoeff_range_zMatrixSlices_coreBuildR_eq_zero_of_even_two_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd hn hc2 L p hmaps.1

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_eq_bot_of_explicitTarget_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) =
      ⊥ := by
  apply le_antisymm
  · intro R hR
    rcases hR with ⟨p, rfl⟩
    have hzero :=
      sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_coreBuildR_eq_zero_of_even_two_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd hn hc2 L p (hZ p)
    rw [sqdiagReducedRootProfileCoreBuildRWithLine_apply, hzero]
    exact Submodule.zero_mem _
  · exact bot_le

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_of_coreBuildR_eq_zero_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hR : coreBuildR (n := n) p.2 (L p) = 0)
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  exact
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_of_intersectionRoot_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
      (sqdiagReducedRootProfileIntersectionExplicitWithLine_root_mem_ZDiff_of_coreBuildR
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p hR)
      hcoeff

theorem sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_forall_of_lineLift_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hM :
      LinearMap.range (sqdiagMatrixConstantRootCore (n := n)) ≤
        LinearMap.range (sqdiagLineCoreBuildR (n := n)))
    (hcoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
              (sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM) p)).2 ∈
          LinearMap.range
            (sqdiagKCAdjointRangeEmbed
              (n := n) (a := a) (b := b) (d := d))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM) p := by
  intro p
  exact
    sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_of_coreBuildR_eq_zero_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM) p
      (sqdiagReducedRootProfileLineLift_coreBuildR_eq_zero
        (n := n) (b := b) (d := d) hM p)
      (hcoeff p)

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileNormalizedPairPresentationWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairPresentation n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileNormalizedPairProductWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p,
      sqdiagReducedRootProfileNormalizedPairProductWithLine_mem_presentation_of_target
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
        (hZ p)⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedPairProductWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedPairProductWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).map_smul r x

noncomputable def sqdiagReducedRootProfileNormalizedRelationWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    SqdiagReducedRootProfile n b d →ₗ[F] SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointAmbientPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileNormalizedPairPresentationWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ)

@[simp]
theorem sqdiagReducedRootProfileNormalizedRelationWithLine_root_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p)).1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 := by
  change
    (sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairPresentationWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p)).1.1.1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1
  rw [sqdiagAdjointAmbientPairPresentationSum_root_apply]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1
  rfl

theorem sqdiagReducedRootProfileNormalizedRelationWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p)).1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 := by
  rw [sqdiagReducedRootProfileNormalizedRelationWithLine_root_pairAdd,
    sqdiagReducedRootProfileNormalizedPairProductWithLine_pairAdd]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 +
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1
  rw [sqdiagReducedRootProfileFullPairProduct_root]

theorem sqdiagReducedRootProfileNormalizedRelationWithLine_mem_verticalOrthogonal_of_pair
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (p : SqdiagReducedRootProfile n b d)
    (hp :
      sqdiagReducedRootProfileNormalizedPairPresentationWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
        sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagReducedRootProfileNormalizedRelationWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d := by
  exact
    sqdiagAdjointAmbientPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairPresentationWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p)
      hp

theorem sqdiagReducedRootProfileNormalizedRelationWithLine_Q_eq_zero_of_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p) = 0 := by
  change
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairPresentationWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p) = 0
  apply
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairPresentationWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p)
  intro A hA
  exact hzero p A hA

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileNormalizedVerticalOrthogonalWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationVerticalOrthogonal n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileNormalizedRelationWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p,
      horth p⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedRelationWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedRelationWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ).map_smul r x

noncomputable def sqdiagReducedRootProfileNormalizedToDefectWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  (sqdiagReducedRelationVerticalOrthogonalToRootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileNormalizedVerticalOrthogonalWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth)

@[simp]
theorem sqdiagReducedRootProfileNormalizedToDefectWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileNormalizedToDefectWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p).1.1 =
      sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p) := by
  exact
    sqdiagReducedRelationVerticalOrthogonalToRootDefect_apply
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedVerticalOrthogonalWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p)

@[simp]
theorem sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileNormalizedToDefectWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p).1.1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 := by
  rw [sqdiagReducedRootProfileNormalizedToDefectWithLine_root,
    sqdiagReducedRootProfileNormalizedRelationWithLine_root]

theorem sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_coreBuildR_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d)
    (hR : coreBuildR (n := n) p.2 (L p) = 0) :
    (sqdiagReducedRootProfileNormalizedToDefectWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p).1.1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p := by
  have hroot :=
    sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p
  have hinter :
      (sqdiagReducedRootProfileIntersectionExplicitWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 = 0 :=
    sqdiagReducedRootProfileIntersectionExplicitWithLine_root_eq_zero_of_coreBuildR
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p hR
  calc
    (sqdiagReducedRootProfileNormalizedToDefectWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p).1.1.1
        =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionExplicitWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 := hroot
    _ =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p + 0 := by rw [hinter]
    _ =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p := by rw [add_zero]

theorem sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_target_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileNormalizedToDefectWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p).1.1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p := by
  exact
    sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_coreBuildR_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p
      (sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine_coreBuildR_eq_zero_of_even_two_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd hn hc2 L p (hZ p))

theorem sqdiagReducedRootProfileNormalizedToDefectWithLine_bijective_iff_rootValue
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth) ↔
      (∀ p q : SqdiagReducedRootProfile n b d,
          (sqdiagReducedRootProfileNormalizedToDefectWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ horth p).1.1.1 =
          (sqdiagReducedRootProfileNormalizedToDefectWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ horth q).1.1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            (sqdiagReducedRootProfileNormalizedToDefectWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hZ horth p).1.1.1 = R0.1.1.1) := by
  constructor
  · intro hbij
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hbij.1
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hroot
    · intro R0
      rcases hbij.2 R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      exact congrArg
        (fun R0 : sqdiagReducedRelationRootDefect n a b c d => R0.1.1.1)
        hp
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hp
      apply hinj
      exact congrArg
        (fun R0 : sqdiagReducedRelationRootDefect n a b c d => R0.1.1.1)
        hp
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hp

theorem sqdiagReducedRootProfileNormalizedToDefectWithLine_bijective_iff_rootTarget
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth) ↔
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionExplicitWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionExplicitWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionExplicitWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p).1.1 =
              R0.1.1.1) := by
  rw [sqdiagReducedRootProfileNormalizedToDefectWithLine_bijective_iff_rootValue
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ horth]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
      have hq :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth q
      exact hp.trans (hroot.trans hq.symm)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
      exact hrootp.symm.trans hp
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
      have hq :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth q
      exact hp.symm.trans (hroot.trans hq)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
      exact hrootp.trans hp

theorem sqdiagReducedRootProfileNormalizedToDefectWithLine_bijective_iff_skeletonRootTarget_of_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth) ↔
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p =
              R0.1.1.1) := by
  rw [sqdiagReducedRootProfileNormalizedToDefectWithLine_bijective_iff_rootValue
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ horth]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_target_even_two_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd hn hc2 L hZ horth p
      have hq :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_target_even_two_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd hn hc2 L hZ horth q
      exact hp.trans (hroot.trans hq.symm)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_target_even_two_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd hn hc2 L hZ horth p
      exact hrootp.symm.trans hp
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_target_even_two_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd hn hc2 L hZ horth p
      have hq :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_target_even_two_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd hn hc2 L hZ horth q
      exact hp.symm.trans (hroot.trans hq)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_target_even_two_le
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd hn hc2 L hZ horth p
      exact hrootp.trans hp

theorem sqdiagReducedRootProfileNormalizedToDefectWithLine_bijective_iff_skeletonRootTarget_of_lineLift
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hM :
      LinearMap.range (sqdiagMatrixConstantRootCore (n := n)) ≤
        LinearMap.range (sqdiagLineCoreBuildR (n := n)))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM) p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
            (sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM)
            hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd
          (sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM)
          hZ horth) ↔
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p =
              R0.1.1.1) := by
  let L := sqdiagReducedRootProfileLineLift (n := n) (b := b) (d := d) hM
  rw [sqdiagReducedRootProfileNormalizedToDefectWithLine_bijective_iff_rootValue
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ horth]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_coreBuildR_eq_zero
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
          (sqdiagReducedRootProfileLineLift_coreBuildR_eq_zero
            (n := n) (b := b) (d := d) hM p)
      have hq :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_coreBuildR_eq_zero
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth q
          (sqdiagReducedRootProfileLineLift_coreBuildR_eq_zero
            (n := n) (b := b) (d := d) hM q)
      exact hp.trans (hroot.trans hq.symm)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_coreBuildR_eq_zero
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
          (sqdiagReducedRootProfileLineLift_coreBuildR_eq_zero
            (n := n) (b := b) (d := d) hM p)
      exact hrootp.symm.trans hp
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_coreBuildR_eq_zero
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
          (sqdiagReducedRootProfileLineLift_coreBuildR_eq_zero
            (n := n) (b := b) (d := d) hM p)
      have hq :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_coreBuildR_eq_zero
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth q
          (sqdiagReducedRootProfileLineLift_coreBuildR_eq_zero
            (n := n) (b := b) (d := d) hM q)
      exact hp.symm.trans (hroot.trans hq)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileNormalizedToDefectWithLine_rootTarget_eq_skeleton_of_coreBuildR_eq_zero
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
          (sqdiagReducedRootProfileLineLift_coreBuildR_eq_zero
            (n := n) (b := b) (d := d) hM p)
      exact hrootp.trans hp

noncomputable def sqdiagReducedRootProfileIntersectionSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] SquareBWIntersection n a b c d :=
  (sqdiagSquareBWIntersectionCoreParamSection
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    (sqdiagReducedRootProfileCoreParamWithLine
      (n := n) (b := b) (d := d) L)

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionWithLine_read
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) =
      (p.2, L p) := by
  change
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSquareBWIntersectionCoreParamSection
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileCoreParamWithLine
            (n := n) (b := b) (d := d) L p)) =
      (p.2, L p)
  simpa using
    sqdiagSquareBWIntersectionCoreParamRead_section
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileCoreParamWithLine
        (n := n) (b := b) (d := d) L p)

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionWithLine_read_matrix
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 =
      p.2 := by
  exact congrArg Prod.fst
    (sqdiagReducedRootProfileIntersectionSectionWithLine_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionWithLine_read_line
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 =
      L p := by
  exact congrArg Prod.snd
    (sqdiagReducedRootProfileIntersectionSectionWithLine_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)

noncomputable def sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a)))) :
    SqdiagReducedRootProfile n b d →ₗ[F] SquareBWIntersection n a b c d :=
  sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L +
    (LinearMap.ker
      (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)).subtype.comp
      ((sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm.toLinearMap.comp T)

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p =
      sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p +
        ((sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm (T p)).1 :=
  rfl

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_read
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) =
      (p.2, L p) := by
  rw [sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_apply]
  rw [sqdiagSquareBWIntersectionCoreParamRead_add_kernel
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd]
  exact
    sqdiagReducedRootProfileIntersectionSectionWithLine_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p

theorem sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_rootCoeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) =
      SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) +
        (T p).1.1 := by
  rw [sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_apply]
  rw [sqdiagSquareBWIntersectionRootCoeff_add_kernel
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd]
  have hroot :
      (sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        ((sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm (T p))).1.1 =
        (T p).1.1 := by
    exact congrArg (fun u => u.1.1)
      ((sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).apply_symm_apply (T p))
  rw [hroot]

theorem sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 =
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
        pullYW (n := n) (b := b) (c := c) (d := d) (T p).1.1 := by
  rw [sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_apply]
  change
    (sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
      (((sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm (T p)).1).1.1 =
    (sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
      pullYW (n := n) (b := b) (c := c) (d := d) (T p).1.1
  have hrootCoeff :
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
          (((sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm (T p)).1) =
        (T p).1.1 := by
    let e :=
      sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
    have hrootProjection :
        (e (e.symm (T p))).1.1 =
          SquareBWIntersectionRootCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
            ((e.symm (T p)).1) := by
      exact
        sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel_root
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd (e.symm (T p))
    have hrootApply :
        (e (e.symm (T p))).1.1 = (T p).1.1 := by
      exact congrArg (fun u => u.1.1)
        (e.apply_symm_apply (T p))
    change
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
          ((e.symm (T p)).1) =
        (T p).1.1
    exact hrootProjection.symm.trans hrootApply
  rw [← pullYW_SquareBWIntersectionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
      (((sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm (T p)).1),
    hrootCoeff]

theorem sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_coeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.2 =
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 +
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) (T p).2.1 := by
  rw [sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_apply]
  change
    (sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 +
      (((sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm (T p)).1).1.2 =
    (sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 +
      SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) (T p).2.1
  have hcompatCoeff :
      SquareBWIntersectionCompatCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
          (((sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm (T p)).1) =
        (T p).2.1 := by
    let e :=
      sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
    have hcompatProjection :
        (e (e.symm (T p))).2.1 =
          SquareBWIntersectionCompatCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
            ((e.symm (T p)).1) := by
      exact
        sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel_compat
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd (e.symm (T p))
    have hcompatApply :
        (e (e.symm (T p))).2.1 = (T p).2.1 := by
      exact congrArg (fun u => u.2.1)
        (e.apply_symm_apply (T p))
    change
      SquareBWIntersectionCompatCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
          ((e.symm (T p)).1) =
        (T p).2.1
    exact hcompatProjection.symm.trans hcompatApply
  rw [← SquareCompatEmbed_SquareBWIntersectionCompatCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
      (((sqdiagSquareBWIntersectionCoreParamReadKernelEquivTraceKernel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm (T p)).1),
    hcompatCoeff]

noncomputable def sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] YWCoeff n c :=
  (SquareBWIntersectionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).comp
    (sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p =
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :=
  rfl

noncomputable def sqdiagReducedRootProfileIntersectionSectionRootWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] RootTarget n b c d where
  toFun p :=
    (sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1
  map_add' x y := by
    have hmap :=
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).map_add x y
    change
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L (x + y)).1.1 =
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L x).1.1 +
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L y).1.1
    rw [hmap]
    rfl
  map_smul' r x := by
    have hmap :=
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).map_smul r x
    change
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L (r • x)).1.1 =
        r •
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L x).1.1
    rw [hmap]
    rfl

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionRootWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionSectionRootWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p =
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 :=
  rfl

noncomputable def sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a)))) :
    SqdiagReducedRootProfile n b d →ₗ[F] RootTarget n b c d where
  toFun p :=
    (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1
  map_add' x y := by
    have hmap :=
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T).map_add x y
    change
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T (x + y)).1.1 =
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T x).1.1 +
          (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T y).1.1
    rw [hmap]
    rfl
  map_smul' r x := by
    have hmap :=
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T).map_smul r x
    change
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T (r • x)).1.1 =
        r •
          (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T x).1.1
    rw [hmap]
    rfl

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p =
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 :=
  rfl

theorem sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine_eq
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p =
      sqdiagReducedRootProfileIntersectionSectionRootWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p +
        pullYW (n := n) (b := b) (c := c) (d := d) (T p).1.1 := by
  exact
    sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_root
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p

noncomputable def sqdiagRootTraceKernelPullYWEvalMap
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker (SquareRootTrace (n := n) (c := c)) →ₗ[F]
      Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) :=
  ((sqdiagRootZeroACoeffEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (pullYW (n := n) (b := b) (c := c) (d := d))).comp
    (LinearMap.ker (SquareRootTrace (n := n) (c := c))).subtype

@[simp]
theorem sqdiagRootTraceKernelPullYWEvalMap_apply
    {n a b c d : ℕ} [NeZero n]
    (M : LinearMap.ker (SquareRootTrace (n := n) (c := c))) :
    sqdiagRootTraceKernelPullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d) M =
      sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
        (pullYW (n := n) (b := b) (c := c) (d := d) M.1) :=
  rfl

abbrev sqdiagRootTraceKernelZSliceCoeffSpace
    (n c : ℕ) [NeZero n] : Submodule F (YWCoeff n c) :=
  LinearMap.ker (SquareRootTrace (n := n) (c := c)) ⊓
    LinearMap.range (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))

noncomputable def sqdiagRootTraceKernelZSliceCoeffSpaceToTraceKernel
    {n c : ℕ} [NeZero n] :
    sqdiagRootTraceKernelZSliceCoeffSpace n c →ₗ[F]
      LinearMap.ker (SquareRootTrace (n := n) (c := c)) where
  toFun M := ⟨M.1, M.2.1⟩
  map_add' M N := by
    apply Subtype.ext
    rfl
  map_smul' r M := by
    apply Subtype.ext
    rfl

theorem sqdiagRootTraceKernelZSliceCoeffSpace_mem_range
    {n c : ℕ} [NeZero n]
    (M : sqdiagRootTraceKernelZSliceCoeffSpace n c) :
    M.1 ∈ LinearMap.range (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) :=
  M.2.2

noncomputable def sqdiagRootTraceKernelZSlicePullYWEvalMap
    {n a b c d : ℕ} [NeZero n] :
    sqdiagRootTraceKernelZSliceCoeffSpace n c →ₗ[F]
      Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) :=
  (sqdiagRootTraceKernelPullYWEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagRootTraceKernelZSliceCoeffSpaceToTraceKernel
      (n := n) (c := c))

theorem sqdiagRootTraceKernelZSlicePullYWEvalMap_range_le_traceKernelPullYWEvalMap
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagRootTraceKernelZSlicePullYWEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
      LinearMap.range
        (sqdiagRootTraceKernelPullYWEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro φ hφ
  rcases hφ with ⟨M, rfl⟩
  exact
    ⟨sqdiagRootTraceKernelZSliceCoeffSpaceToTraceKernel
        (n := n) (c := c) M, rfl⟩

noncomputable def sqdiagReducedRootProfileRootZeroDemandMap
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) :=
  ((sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d))) +
    ((sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileIntersectionSectionRootWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))

@[simp]
theorem sqdiagReducedRootProfileRootZeroDemandMap_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileRootZeroDemandMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L p =
      sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p) +
        sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileIntersectionSectionRootWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :=
  rfl

theorem
    sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_iff_exists_linear_correction
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    LinearMap.range
        (sqdiagReducedRootProfileRootZeroDemandMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
      LinearMap.range
        (sqdiagRootTraceKernelZSlicePullYWEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      ∃ K : SqdiagReducedRootProfile n b d →ₗ[F]
          sqdiagRootTraceKernelZSliceCoeffSpace n c,
        (sqdiagRootTraceKernelZSlicePullYWEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
          sqdiagReducedRootProfileRootZeroDemandMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L := by
  exact
    linearMap_range_le_iff_exists_comp
      (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d))
      (sqdiagReducedRootProfileRootZeroDemandMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_linear_correction
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (K : SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagRootTraceKernelZSliceCoeffSpace n c)
    (hK :
      (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
        sqdiagReducedRootProfileRootZeroDemandMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) :
    LinearMap.range
        (((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d))) +
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileIntersectionSectionRootWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
      LinearMap.range
        (sqdiagRootTraceKernelZSlicePullYWEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  have hDemand :
      LinearMap.range
          (sqdiagReducedRootProfileRootZeroDemandMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) :=
    (sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_iff_exists_linear_correction
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L).mpr ⟨K, hK⟩
  simpa [sqdiagReducedRootProfileRootZeroDemandMap] using hDemand

theorem sqdiagReducedRootProfile_rootZeroEvalRangeLe_of_rootZeroZSliceEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    LinearMap.range
        (((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d))) +
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileIntersectionSectionRootWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
      LinearMap.range
        (sqdiagRootTraceKernelPullYWEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro φ hφ
  exact
    sqdiagRootTraceKernelZSlicePullYWEvalMap_range_le_traceKernelPullYWEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (hZSliceEvalRange hφ)

noncomputable def sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      LinearMap.ker (SquareRootTrace (n := n) (c := c)) :=
  linearMapLiftOfRangeLe
    (sqdiagRootTraceKernelPullYWEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d))
    (((sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d))) +
      ((sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileIntersectionSectionRootWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)))
    hEvalRange

theorem
    sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe_eval_pullYW
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
        (pullYW (n := n) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hEvalRange p).1) =
      sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p) +
        sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileIntersectionSectionRootWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) := by
  let f :=
    sqdiagRootTraceKernelPullYWEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let g :=
    ((sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d))) +
      ((sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileIntersectionSectionRootWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))
  have hcomp := linearMap_comp_liftOfRangeLe f g hEvalRange
  have hp := congrArg
    (fun T : SqdiagReducedRootProfile n b d →ₗ[F]
        Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) => T p)
    hcomp
  simpa [f, g, sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe]
    using hp

noncomputable def sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
        LinearMap.ker (SquareCompatTrace (n := n) (a := a))) :=
  LinearMap.prod
    (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hEvalRange)
    0

@[simp]
theorem sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe_compat
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hEvalRange p).2.1 = 0 :=
  rfl

theorem
    sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine_eval_eq_rootTarget_of_rootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p) =
      sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
            (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange) p) := by
  let E :=
    sqdiagRootZeroACoeffEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let R :=
    sqdiagReducedRootProfileRootTarget
      (n := n) (b := b) (c := c) (d := d) p
  let I :=
    sqdiagReducedRootProfileIntersectionSectionRootWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
  let K :=
    sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hEvalRange p
  have hcorr :
      E (pullYW (n := n) (b := b) (c := c) (d := d) K.1) =
        E R + E I := by
    simpa [E, R, I, K] using
      sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe_eval_pullYW
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hEvalRange p
  have hroot :
      sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange) p =
        I + pullYW (n := n) (b := b) (c := c) (d := d) K.1 := by
    simpa [I, K, sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe] using
      sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine_eq
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
        (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange) p
  calc
    E R = E R + 0 := by rw [add_zero]
    _ = E R + (E I + E I) := by
          rw [F_module_add_self (E I), add_zero]
    _ = E I + (E R + E I) := by abel
    _ = E I + E (pullYW (n := n) (b := b) (c := c) (d := d) K.1) := by
          rw [hcorr]
    _ = E (I + pullYW (n := n) (b := b) (c := c) (d := d) K.1) := by
          rw [E.map_add]
    _ =
        E (sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange) p) := by
          rw [hroot]

theorem
    sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine_comp_eq_rootTarget_of_rootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    (sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d)) =
    (sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
        (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange)) := by
  apply LinearMap.ext
  intro p
  exact
      sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine_eval_eq_rootTarget_of_rootZeroEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hEvalRange p

noncomputable def sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagRootTraceKernelZSliceCoeffSpace n c :=
  linearMapLiftOfRangeLe
    (sqdiagRootTraceKernelZSlicePullYWEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d))
    (((sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d))) +
      ((sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileIntersectionSectionRootWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)))
    hZSliceEvalRange

theorem
    sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLe_eval_pullYW
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
        (pullYW (n := n) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
            hZSliceEvalRange p).1) =
      sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p) +
        sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileIntersectionSectionRootWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) := by
  let f :=
    sqdiagRootTraceKernelZSlicePullYWEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let g :=
    ((sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d))) +
      ((sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileIntersectionSectionRootWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))
  have hcomp := linearMap_comp_liftOfRangeLe f g hZSliceEvalRange
  have hp := congrArg
    (fun T : SqdiagReducedRootProfile n b d →ₗ[F]
        Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) => T p)
    hcomp
  simpa [f, g,
    sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLe,
    sqdiagRootTraceKernelZSlicePullYWEvalMap,
    sqdiagRootTraceKernelZSliceCoeffSpaceToTraceKernel] using hp

noncomputable def sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
        LinearMap.ker (SquareCompatTrace (n := n) (a := a))) :=
  LinearMap.prod
    ((sqdiagRootTraceKernelZSliceCoeffSpaceToTraceKernel
        (n := n) (c := c)).comp
      (sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZSliceEvalRange))
    0

theorem
    sqdiagReducedRootProfileIntersectionSectionRootTraceKernelZSliceTwistWithLine_eval_eq_rootTarget_of_rootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p) =
      sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
            (sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hZSliceEvalRange) p) := by
  let E :=
    sqdiagRootZeroACoeffEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  let R :=
    sqdiagReducedRootProfileRootTarget
      (n := n) (b := b) (c := c) (d := d) p
  let I :=
    sqdiagReducedRootProfileIntersectionSectionRootWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
  let K :=
    sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange p
  let T :=
    sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange
  have hcorr :
      E (pullYW (n := n) (b := b) (c := c) (d := d) K.1) =
        E R + E I := by
    simpa [E, R, I, K] using
      sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLe_eval_pullYW
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZSliceEvalRange p
  have hroot :
      sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p =
        I + pullYW (n := n) (b := b) (c := c) (d := d) K.1 := by
    simpa [I, K, T,
      sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe,
      sqdiagRootTraceKernelZSliceCoeffSpaceToTraceKernel] using
      sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine_eq
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p
  calc
    E R = E R + 0 := by rw [add_zero]
    _ = E R + (E I + E I) := by
          rw [F_module_add_self (E I), add_zero]
    _ = E I + (E R + E I) := by abel
    _ = E I + E (pullYW (n := n) (b := b) (c := c) (d := d) K.1) := by
          rw [hcorr]
    _ = E (I + pullYW (n := n) (b := b) (c := c) (d := d) K.1) := by
          rw [E.map_add]
    _ =
        E (sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) := by
          rw [hroot]

noncomputable def sqdiagReducedRootProfileIntersectionSectionCoeffWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] CFun4 n a b d :=
  (sqdiagSquareBWIntersectionTargetCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionCoeffWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionSectionCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p =
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 :=
  rfl

noncomputable def sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F] CFun4 n a b d :=
  sqdiagReducedRootProfileFullCoeffMap
      (n := n) (a := a) (b := b) (c := c) (d := d) +
    sqdiagReducedRootProfileIntersectionSectionCoeffWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L

@[simp]
theorem sqdiagReducedRootProfileNormalizedSectionCoeffWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p =
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 :=
  rfl

noncomputable def sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a)))) :
    SqdiagReducedRootProfile n b d →ₗ[F] YWCoeff n c :=
  (SquareBWIntersectionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).comp
    (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T)

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p =
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
          (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) :=
  rfl

theorem sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine_eq
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p =
      sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p +
        (T p).1.1 := by
  exact
    sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_rootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p

noncomputable def sqdiagReducedRootProfileIntersectionSectionCoeffTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a)))) :
    SqdiagReducedRootProfile n b d →ₗ[F] CFun4 n a b d :=
  (sqdiagSquareBWIntersectionTargetCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T)

@[simp]
theorem sqdiagReducedRootProfileIntersectionSectionCoeffTraceKernelTwistWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionSectionCoeffTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p =
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.2 :=
  rfl

theorem sqdiagReducedRootProfileIntersectionSectionCoeffTraceKernelTwistWithLine_eq
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileIntersectionSectionCoeffTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p =
      sqdiagReducedRootProfileIntersectionSectionCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p +
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) (T p).2.1 := by
  exact
    sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_coeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p

noncomputable def sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a)))) :
    SqdiagReducedRootProfile n b d →ₗ[F] CFun4 n a b d :=
  sqdiagReducedRootProfileFullCoeffMap
      (n := n) (a := a) (b := b) (c := c) (d := d) +
    sqdiagReducedRootProfileIntersectionSectionCoeffTraceKernelTwistWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T

@[simp]
theorem sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p =
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.2 :=
  rfl

theorem sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_eq
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p =
      sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p +
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) (T p).2.1 := by
  rw [sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_apply,
    sqdiagReducedRootProfileNormalizedSectionCoeffWithLine_apply,
    sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_coeff]
  abel

theorem sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_eq_of_rootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
        (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange) p =
      sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  rw [sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L]
  simp

theorem sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    LinearMap.range
        (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange)) ≤
      LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) := by
  intro C hC
  rcases hC with ⟨p, rfl⟩
  rw [sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_eq_of_rootZeroEvalRangeLe
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hEvalRange p]
  exact hcoeff ⟨p, rfl⟩

noncomputable def sqdiagReducedRootProfileYZCorrectionYDiffSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun p :=
    ⟨(sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p),
      by
        exact
          (YDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem
            (SquareBWIntersectionRootSubmodule
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileIntersectionSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2.1
            ((range_pullYZ_le_inf_YZ
              (n := n) (b := b) (c := c) (d := d)
              ⟨Z p, rfl⟩).1)⟩
  map_add' x y := by
    apply Subtype.ext
    change
      (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L (x + y)).1.1 +
          pullYZ (n := n) (b := b) (c := c) (d := d) (Z (x + y)) =
        ((sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L x).1.1 +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z x)) +
          ((sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L y).1.1 +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z y))
    rw [(sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).map_add,
      Z.map_add,
      (pullYZ (n := n) (b := b) (c := c) (d := d)).map_add]
    have hIadd :
        ((sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L x) +
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L y)).1.1 =
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L x).1.1 +
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L y).1.1 := by
      rfl
    rw [hIadd]
    abel
  map_smul' r x := by
    apply Subtype.ext
    change
      (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L (r • x)).1.1 +
          pullYZ (n := n) (b := b) (c := c) (d := d) (Z (r • x)) =
        r •
          ((sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L x).1.1 +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z x))
    rw [(sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).map_smul,
      Z.map_smul,
      (pullYZ (n := n) (b := b) (c := c) (d := d)).map_smul]
    have hIsmul :
        (r • sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L x).1.1 =
          r • (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L x).1.1 := by
      rfl
    rw [hIsmul, smul_add]

@[simp]
theorem sqdiagReducedRootProfileYZCorrectionYDiffSectionWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileYZCorrectionYDiffSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p).1 =
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) :=
  rfl

noncomputable def sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d) :
    SqdiagReducedRootProfile n b d →ₗ[F] BFun4 n a c d :=
  (sqdiagKBRootSection
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileYZCorrectionYDiffSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z)

@[simp]
theorem sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p) =
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) := by
  simp [sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine]

noncomputable def sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  LinearMap.prod
    ((SquareBMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d)).rangeRestrict.comp
      (sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z))
    0

@[simp]
theorem sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 =
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) := by
  change
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p) +
      0 =
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
          pullYZ (n := n) (b := b) (c := c) (d := d) (Z p)
  rw [sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine_root, add_zero]

@[simp]
theorem sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine_coeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 =
      ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
        (sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p) := by
  change
    ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
        (sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p) +
      0 =
      ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
        (sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
  rw [add_zero]

noncomputable def sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  (sqdiagSquareBWIntersectionBOnlyPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    (sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)

@[simp]
theorem sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionWithLine_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) =
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1 := by
  change
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionBOnlyPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)) =
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1
  exact
    sqdiagSquareBWIntersectionBOnlyPairProduct_pairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)

noncomputable def sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a)))) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  (sqdiagSquareBWIntersectionBOnlyPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T)

@[simp]
theorem sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionTraceKernelTwistWithLine_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) =
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1 := by
  change
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionBOnlyPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)) =
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1
  exact
    sqdiagSquareBWIntersectionBOnlyPairProduct_pairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)

noncomputable def sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  sqdiagReducedRootProfileFullPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) +
    (sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L +
      sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z)

@[simp]
theorem sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p) =
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        ((sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1 +
          sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)) := by
  change
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
          (sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p +
            sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)) =
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        ((sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1 +
          sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p))
  rw [(sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
    (sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
    sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionWithLine_pairAdd]

theorem sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) := by
  rw [sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_pairAdd]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 +
      ((sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1) =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p)
  rw [sqdiagReducedRootProfileFullPairProduct_root,
    sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine_root]
  change
    sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p +
      ((sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
        ((sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
          pullYZ (n := n) (b := b) (c := c) (d := d) (Z p))) =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p)
  rw [show
      (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
        ((sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
          pullYZ (n := n) (b := b) (c := c) (d := d) (Z p)) =
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) by
      calc
        (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
          ((sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p)) =
            ((sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 +
              (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1) +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) := by
                abel
        _ = 0 + pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) := by
              rw [F_module_add_self]
        _ = pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) := by
              rw [zero_add]]

theorem sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_root_mem_ZDiff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rw [sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_root]
  exact
    (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem
      (sqdiagReducedRootProfileRootTarget_mem_ZDiff
        (n := n) (b := b) (c := c) (d := d) hb hc hd p)
      ((range_pullYZ_le_inf_YZ
        (n := n) (b := b) (c := c) (d := d)
        ⟨Z p, rfl⟩).2)

theorem sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_coeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 =
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        ((sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 +
          ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
            (sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)) := by
  rw [sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_pairAdd]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).2 +
      ((sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 +
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2) =
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        ((sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 +
          ((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d)))
            (sqdiagReducedRootProfileYZCorrectionBSourceSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p))
  rw [sqdiagReducedRootProfileFullCoeffMap_apply,
    sqdiagReducedRootProfileYZCorrectionBPairProductSectionWithLine_coeff]

abbrev sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d) : Prop :=
  sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p) ∈
    sqdiagZAdjointTargetSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine_of_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d)
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p := by
  exact
    (sqdiagZAdjointTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p))).mpr
      ⟨sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_root_mem_ZDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p,
        sqdiagKCAdjointCoeff_exists_of_rangeEmbed
          (n := n) (a := a) (b := b) (c := c) (d := d) hc
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2
          hcoeff⟩

theorem sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_mem_presentation_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (p : SqdiagReducedRootProfile n b d)
    (hZ :
      sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p) :
    sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
  exact hZ

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairPresentation n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p,
      sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_mem_presentation_of_target
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p
        (hZ p)⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z).map_smul r x

noncomputable def sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p) :
    SqdiagReducedRootProfile n b d →ₗ[F] SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointAmbientPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ)

@[simp]
theorem sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_root_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p)).1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 := by
  change
    (sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p)).1.1.1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1
  rw [sqdiagAdjointAmbientPairPresentationSum_root_apply]
  rfl

theorem sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p)).1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) := by
  rw [sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_root_pairAdd,
    sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_root]

theorem
    sqdiagReducedRootProfileYZCorrected_rootZeroACoeffSpace_annihilates_root_forall_iff_rootTarget_mem_annihilator
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d) :
    (∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L Z p)).1 = 0) ↔
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d := by
  constructor
  · intro hann p
    apply
      (sqdiagRootZeroACoeffAnnihilator_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p +
          pullYZ (n := n) (b := b) (c := c) (d := d) (Z p))).mpr
    intro A hA
    rw [← sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_root
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p]
    exact hann p A hA
  · intro hroot p A hA
    have hzero :=
      (sqdiagRootZeroACoeffAnnihilator_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p +
          pullYZ (n := n) (b := b) (c := c) (d := d) (Z p))).mp
        (hroot p) A hA
    rw [sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine_root]
    exact hzero

theorem sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_pair
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (p : SqdiagReducedRootProfile n b d)
    (hp :
      sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
        sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d := by
  exact
    sqdiagAdjointAmbientPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p)
      hp

theorem sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hpair :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ p ∈
          sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_pair
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ p (hpair p)

theorem
    sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L Z p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L Z hZ p ∈
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
  refine
    sqdiagAdjointAmbientPairPresentation_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L Z hZ p) ?_
  intro A hA
  simpa [sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine] using
    hann p A hA

theorem
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L Z p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ
    (sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ hann)
    p

theorem
    sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_mem_annihilator_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L Z hZ p ∈
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
  have hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L Z p)).1 = 0 :=
    (sqdiagReducedRootProfileYZCorrected_rootZeroACoeffSpace_annihilates_root_forall_iff_rootTarget_mem_annihilator
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z).mpr hroot
  exact
    sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ hann p

theorem
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_mem_annihilator_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ
    (sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_mem_annihilator_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ hroot)
    p

theorem sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_Q_eq_zero_of_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p) = 0 := by
  change
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p) = 0
  apply
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileYZCorrectedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p)
  intro A hA
  exact hzero p A hA

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileYZCorrectedVerticalOrthogonalSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationVerticalOrthogonal n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p,
      horth p⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ).map_smul r x

noncomputable def sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  (sqdiagReducedRelationVerticalOrthogonalToRootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileYZCorrectedVerticalOrthogonalSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ horth)

@[simp]
theorem sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ horth p).1.1 =
      sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p) := by
  exact
    sqdiagReducedRelationVerticalOrthogonalToRootDefect_apply
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileYZCorrectedVerticalOrthogonalSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ horth p)

@[simp]
theorem sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_rootTarget
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ horth p).1.1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) := by
  rw [sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_root,
    sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_root]

noncomputable def sqdiagReducedRootProfileYZCorrectedDefectEquivSectionWithLine_of_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth)) :
    SqdiagReducedRootProfile n b d ≃ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  LinearEquiv.ofBijective
    (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth)
    hbij

theorem sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_bijective_iff_rootValue
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth) ↔
      (∀ p q : SqdiagReducedRootProfile n b d,
          (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ horth p).1.1.1 =
          (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ horth q).1.1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L Z hZ horth p).1.1.1 = R0.1.1.1) := by
  constructor
  · intro hbij
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hbij.1
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hroot
    · intro R0
      rcases hbij.2 R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      exact congrArg
        (fun R0 : sqdiagReducedRelationRootDefect n a b c d => R0.1.1.1)
        hp
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hp
      apply hinj
      exact congrArg
        (fun R0 : sqdiagReducedRelationRootDefect n a b c d => R0.1.1.1)
        hp
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hp

theorem sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_bijective_iff_rootTarget
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth) ↔
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            pullYZ (n := n) (b := b) (c := c) (d := d) (Z q) →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              pullYZ (n := n) (b := b) (c := c) (d := d) (Z p) =
              R0.1.1.1) := by
  rw [sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_bijective_iff_rootValue
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L Z hZ horth]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth p
      have hq :=
        sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth q
      exact hp.trans (hroot.trans hq.symm)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth p
      exact hrootp.symm.trans hp
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth p
      have hq :=
        sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth q
      exact hp.symm.trans (hroot.trans hq)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth p
      exact hrootp.trans hp

noncomputable def sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  sqdiagReducedRootProfileFullPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) +
    sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L

@[simp]
theorem sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) =
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1 := by
  change
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
          sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) =
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1
  rw [(sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
    sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionWithLine_pairAdd]

theorem sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 := by
  rw [sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_pairAdd]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 +
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1
  rw [sqdiagReducedRootProfileFullPairProduct_root]

theorem sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_coeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 =
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 := by
  rw [sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_pairAdd]
  rfl

theorem sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_root_mem_ZDiff_iff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) ↔
    (sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  let A : RootTarget n b c d :=
    sqdiagReducedRootProfileRootTarget
      (n := n) (b := b) (c := c) (d := d) p
  let B : RootTarget n b c d :=
    (sqdiagReducedRootProfileIntersectionSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1
  have hA : A ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
    dsimp [A]
    exact
      sqdiagReducedRootProfileRootTarget_mem_ZDiff
        (n := n) (b := b) (c := c) (d := d) hb hc hd p
  have hroot :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 =
        A + B := by
    dsimp [A, B]
    exact
      sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_root
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
  constructor
  · intro h
    have hsum : A + B ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
      rwa [hroot] at h
    have hBA :
        (A + B) + A ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem hsum hA
    have hEq : (A + B) + A = B := by
      calc
        (A + B) + A = B + (A + A) := by abel
        _ = B + 0 := by rw [F_module_add_self A]
        _ = B := by rw [add_zero]
    rw [hEq] at hBA
    exact hBA
  · intro hB
    rw [hroot]
    exact
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem hA hB

noncomputable def sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a)))) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  sqdiagReducedRootProfileFullPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) +
    sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionTraceKernelTwistWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T

@[simp]
theorem sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) =
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1 := by
  change
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
          sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) =
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1
  rw [(sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
    sqdiagReducedRootProfileCoreParamBOnlyPairProductSectionTraceKernelTwistWithLine_pairAdd]

theorem sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 := by
  rw [sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_pairAdd]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 +
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1
  rw [sqdiagReducedRootProfileFullPairProduct_root]

theorem sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_coeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).2 =
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.2 := by
  rw [sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_pairAdd]
  rfl

theorem sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_root_mem_ZDiff_iff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) ↔
    (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  let A : RootTarget n b c d :=
    sqdiagReducedRootProfileRootTarget
      (n := n) (b := b) (c := c) (d := d) p
  let B : RootTarget n b c d :=
    (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1
  have hA : A ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
    dsimp [A]
    exact
      sqdiagReducedRootProfileRootTarget_mem_ZDiff
        (n := n) (b := b) (c := c) (d := d) hb hc hd p
  have hroot :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).1 =
        A + B := by
    dsimp [A, B]
    exact
      sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_root
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p
  constructor
  · intro h
    have hsum : A + B ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
      rwa [hroot] at h
    have hBA :
        (A + B) + A ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem hsum hA
    have hEq : (A + B) + A = B := by
      calc
        (A + B) + A = B + (A + A) := by abel
        _ = B + 0 := by rw [F_module_add_self A]
        _ = B := by rw [add_zero]
    rw [hEq] at hBA
    exact hBA
  · intro hB
    rw [hroot]
    exact
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem hA hB

abbrev sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) : Prop :=
  sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) ∈
    sqdiagZAdjointTargetSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ↔
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T p)).1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
      ∃ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p)).2 := by
  exact
    sqdiagZAdjointTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T p))

theorem
    sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_mem_presentation_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d)
    (hZ :
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) :
    sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
  exact hZ

abbrev sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) : Prop :=
  sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) ∈
    sqdiagZAdjointTargetSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_mem_presentation_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hZ :
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
  exact hZ

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
      ∃ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 := by
  exact
    sqdiagZAdjointTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p))

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionRoot
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
      ∃ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 := by
  rw [sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p,
    sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_root_mem_ZDiff_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p]

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_of_root_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d))
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  exact
    (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mpr
      ⟨hroot,
        sqdiagKCAdjointCoeff_exists_of_rangeEmbed
          (n := n) (a := a) (b := b) (c := c) (d := d) hc
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2
          hcoeff⟩

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_of_intersectionRoot_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d))
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  exact
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_of_root_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
      ((sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_root_mem_ZDiff_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mpr hroot)
      hcoeff

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionRoot_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  constructor
  · intro h
    have hpair :=
      (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionRoot
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mp h
    refine ⟨hpair.1, ?_⟩
    have hcoeff :
        (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
          LinearMap.range
            (sqdiagKCAdjointRangeEmbed
              (n := n) (a := a) (b := b) (d := d)) :=
      (sqdiagKCAdjointCoeff_exists_iff_rangeEmbed
        (n := n) (a := a) (b := b) (c := c) (d := d) hc
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2).mp
        hpair.2
    rwa [sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_coeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p] at hcoeff
  · intro h
    have hcoeff :
        (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
          LinearMap.range
            (sqdiagKCAdjointRangeEmbed
              (n := n) (a := a) (b := b) (d := d)) := by
      rw [sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_coeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p]
      exact h.2
    exact
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_of_intersectionRoot_coeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p h.1 hcoeff

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionRoot_rangePullYZW_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 ∈
        LinearMap.range
          (pullYZW (n := n) (b := b) (c := c) (d := d)) ∧
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  rw [sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionRoot_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p,
    sqdiagSquareBWIntersection_root_mem_ZDiff_iff_range_pullYZW
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)]

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionRootCoeff_rangeZMatrixSlices_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) ∧
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  rw [sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionRoot_rangePullYZW_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p,
    sqdiagSquareBWIntersection_root_mem_range_pullYZW_iff_rootCoeff_range_zMatrixSlices
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)]

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionMaps_range
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ↔
      sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) ∧
      sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  rw [sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionRootCoeff_rangeZMatrixSlices_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p]
  rfl

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  exact
      (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mpr
      ⟨hroot ⟨p, rfl⟩, hcoeff ⟨p, rfl⟩⟩

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  intro p
  exact
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hroot hcoeff p

theorem sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine_range_le_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    LinearMap.range
        (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
      LinearMap.range
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) := by
  intro C hC
  rcases hC with ⟨p, rfl⟩
  exact
    ((sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mp
      (hZ p)).1

theorem sqdiagReducedRootProfileNormalizedSectionCoeffWithLine_range_le_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    LinearMap.range
        (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
      LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) := by
  intro C hC
  rcases hC with ⟨p, rfl⟩
  exact
    ((sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mp
      (hZ p)).2

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_iff_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    (∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) ↔
    LinearMap.range
        (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
      LinearMap.range
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) ∧
    LinearMap.range
        (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
      LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) := by
  constructor
  · intro hZ
    exact
      ⟨sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine_range_le_of_target
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ,
        sqdiagReducedRootProfileNormalizedSectionCoeffWithLine_range_le_of_target
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ⟩
  · intro hmaps
    exact
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hmaps.1 hmaps.2

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_linear_lifts
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (R : SqdiagReducedRootProfile n b d →ₗ[F]
      ZeroSumProfileM n (MatrixZeroSum n))
    (hR :
      (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)).comp R =
        sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)
    (C : SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagKCAdjointRangeModel n b d)
    (hC :
      (sqdiagKCAdjointRangeEmbed
        (n := n) (a := a) (b := b) (d := d)).comp C =
        sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p := by
  have hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) :=
    (linearMap_range_le_iff_exists_comp
      (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))
      (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L)).mpr ⟨R, hR⟩
  have hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) :=
    (linearMap_range_le_iff_exists_comp
      (sqdiagKCAdjointRangeEmbed
        (n := n) (a := a) (b := b) (d := d))
      (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L)).mpr ⟨C, hC⟩
  exact
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hroot hcoeff

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionRoot
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ↔
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
      ∃ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p)).2 := by
  rw [sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p,
    sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_root_mem_ZDiff_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p]

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_of_root_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d))
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p := by
  exact
    (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).mpr
      ⟨hroot,
        sqdiagKCAdjointCoeff_exists_of_rangeEmbed
          (n := n) (a := a) (b := b) (c := c) (d := d) hc
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).2
          hcoeff⟩

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_of_intersectionRoot_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d))
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p := by
  exact
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_of_root_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p
      ((sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_root_mem_ZDiff_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).mpr hroot)
      hcoeff

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionRoot_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ↔
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  constructor
  · intro h
    have hpair :=
      (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionRoot
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).mp h
    refine ⟨hpair.1, ?_⟩
    have hcoeff :
        (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).2 ∈
          LinearMap.range
            (sqdiagKCAdjointRangeEmbed
              (n := n) (a := a) (b := b) (d := d)) :=
      (sqdiagKCAdjointCoeff_exists_iff_rangeEmbed
        (n := n) (a := a) (b := b) (c := c) (d := d) hc
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).2).mp
        hpair.2
    rwa [sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_coeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p] at hcoeff
  · intro h
    have hcoeff :
        (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).2 ∈
          LinearMap.range
            (sqdiagKCAdjointRangeEmbed
              (n := n) (a := a) (b := b) (d := d)) := by
      rw [sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_coeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p]
      exact h.2
    exact
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_of_intersectionRoot_coeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p h.1 hcoeff

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionRoot_rangePullYZW_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ↔
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 ∈
        LinearMap.range
          (pullYZW (n := n) (b := b) (c := c) (d := d)) ∧
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  rw [sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionRoot_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p,
    sqdiagSquareBWIntersection_root_mem_ZDiff_iff_range_pullYZW
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)]

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionRootCoeff_rangeZMatrixSlices_coeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ↔
      SquareBWIntersectionRootCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
          (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) ∧
      sqdiagReducedRootProfileFullCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.2 ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  rw [sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionRoot_rangePullYZW_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p,
    sqdiagSquareBWIntersection_root_mem_range_pullYZW_iff_rootCoeff_range_zMatrixSlices
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)]

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionMaps_range
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ↔
      sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) ∧
      sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ∈
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
  rw [sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionRootCoeff_rangeZMatrixSlices_coeffRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p]
  rfl

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p := by
  exact
    (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).mpr
      ⟨hroot ⟨p, rfl⟩, hcoeff ⟨p, rfl⟩⟩

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p := by
  intro p
  exact
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hroot hcoeff p

theorem sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine_range_le_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) :
    LinearMap.range
        (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
      LinearMap.range
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) := by
  intro C hC
  rcases hC with ⟨p, rfl⟩
  exact
    ((sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).mp
      (hZ p)).1

theorem sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) :
    LinearMap.range
        (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
      LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) := by
  intro C hC
  rcases hC with ⟨p, rfl⟩
  exact
    ((sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).mp
      (hZ p)).2

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_iff_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a)))) :
    (∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) ↔
    LinearMap.range
        (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
      LinearMap.range
        (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) ∧
    LinearMap.range
        (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
      LinearMap.range
        (sqdiagKCAdjointRangeEmbed
          (n := n) (a := a) (b := b) (d := d)) := by
  constructor
  · intro hZ
    exact
      ⟨sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine_range_le_of_target
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ,
        sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_target
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ⟩
  · intro hmaps
    exact
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hmaps.1 hmaps.2

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcorrectionRootCoeff :
      ∀ p : SqdiagReducedRootProfile n b d,
        (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange p).1 ∈
          LinearMap.range
            (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
        (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange) p := by
  let T :=
    sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange
  have hmaps0 :=
    (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_iff_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).mp hZ0
  have hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) := by
    intro C hC
    rcases hC with ⟨p, rfl⟩
    rw [sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine_eq]
    exact
      (LinearMap.range (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))).add_mem
        (hmaps0.1 ⟨p, rfl⟩)
        (by
          simpa [T, sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe] using
            hcorrectionRootCoeff p)
  have hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
    simpa [T] using
      sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_range_le_of_rootZeroEvalRangeLe
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hEvalRange hmaps0.2
  exact
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hroot hcoeff

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcorrectionRootCoeffRange :
      LinearMap.range
          ((LinearMap.ker (SquareRootTrace (n := n) (c := c))).subtype.comp
            (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange)) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
        (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange) p := by
  exact
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_rootZeroEvalRangeLe_target_correctionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hZ0
      (fun p => by
        simpa using hcorrectionRootCoeffRange ⟨p, rfl⟩)

theorem sqdiagReducedRootProfile_rootZeroZSliceEvalRangeLe_of_rootZeroEvalRangeLe_correctionRootCoeff_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hcorrectionRootCoeffRange :
      LinearMap.range
          ((LinearMap.ker (SquareRootTrace (n := n) (c := c))).subtype.comp
            (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange)) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    LinearMap.range
        (((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d))) +
          ((sqdiagRootZeroACoeffEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d)).comp
            (sqdiagReducedRootProfileIntersectionSectionRootWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
      LinearMap.range
        (sqdiagRootTraceKernelZSlicePullYWEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro φ hφ
  rcases hφ with ⟨p, rfl⟩
  let K :=
    sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange p
  let KZ : sqdiagRootTraceKernelZSliceCoeffSpace n c :=
    ⟨K.1,
      ⟨K.2,
        by
          simpa [K] using hcorrectionRootCoeffRange ⟨p, rfl⟩⟩⟩
  refine ⟨KZ, ?_⟩
  have hcorr :=
    sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe_eval_pullYW
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange p
  simpa [K, KZ, sqdiagRootTraceKernelZSlicePullYWEvalMap,
    sqdiagRootTraceKernelZSliceCoeffSpaceToTraceKernel] using hcorr

noncomputable def
    sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLeOfCorrectionRootCoeffRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hcorrectionRootCoeffRange :
      LinearMap.range
          ((LinearMap.ker (SquareRootTrace (n := n) (c := c))).subtype.comp
            (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange)) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagRootTraceKernelZSliceCoeffSpace n c := by
  let C :=
    sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange
  exact
    LinearMap.codRestrict
      (sqdiagRootTraceKernelZSliceCoeffSpace n c)
      ((LinearMap.ker (SquareRootTrace (n := n) (c := c))).subtype.comp C)
      (fun p => by
        constructor
        · exact (C p).2
        · simpa [C] using hcorrectionRootCoeffRange ⟨p, rfl⟩)

set_option synthInstance.maxHeartbeats 500000 in
theorem
    sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLeOfCorrectionRootCoeffRange_comp_demandMap
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hcorrectionRootCoeffRange :
      LinearMap.range
          ((LinearMap.ker (SquareRootTrace (n := n) (c := c))).subtype.comp
            (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange)) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLeOfCorrectionRootCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hEvalRange hcorrectionRootCoeffRange) =
    sqdiagReducedRootProfileRootZeroDemandMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L := by
  apply LinearMap.ext
  intro p
  let C :=
    sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange
  have hcorr :=
    sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe_eval_pullYW
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange p
  simpa [sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLeOfCorrectionRootCoeffRange,
    sqdiagRootTraceKernelZSlicePullYWEvalMap,
    sqdiagRootTraceKernelZSliceCoeffSpaceToTraceKernel,
    sqdiagReducedRootProfileRootZeroDemandMap, C] using hcorr

theorem
    sqdiagReducedRootProfile_exists_linear_correction_of_rootZeroEvalRangeLe_correctionRootCoeff_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hcorrectionRootCoeffRange :
      LinearMap.range
          ((LinearMap.ker (SquareRootTrace (n := n) (c := c))).subtype.comp
            (sqdiagReducedRootProfileRootTraceKernelCorrectionOfRootZeroEvalRangeLe
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hEvalRange)) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    ∃ K : SqdiagReducedRootProfile n b d →ₗ[F]
        sqdiagRootTraceKernelZSliceCoeffSpace n c,
      (sqdiagRootTraceKernelZSlicePullYWEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp K =
        sqdiagReducedRootProfileRootZeroDemandMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L := by
  refine
    ⟨sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLeOfCorrectionRootCoeffRange
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hEvalRange hcorrectionRootCoeffRange, ?_⟩
  exact
    sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLeOfCorrectionRootCoeffRange_comp_demandMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange hcorrectionRootCoeffRange

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelZSliceTwistWithLine_forall_of_rootZeroZSliceEvalRangeLe_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ0 :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
        (sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange) p := by
  let T :=
    sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange
  have hmaps0 :=
    (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_iff_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).mp hZ0
  have hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)) := by
    intro C hC
    rcases hC with ⟨p, rfl⟩
    rw [sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine_eq]
    exact
      (LinearMap.range (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))).add_mem
        (hmaps0.1 ⟨p, rfl⟩)
        (by
          simpa [T,
            sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe,
            sqdiagRootTraceKernelZSliceCoeffSpaceToTraceKernel] using
            sqdiagRootTraceKernelZSliceCoeffSpace_mem_range
              (sqdiagReducedRootProfileRootTraceKernelZSliceCorrectionOfRootZeroEvalRangeLe
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L hZSliceEvalRange p))
  have hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)) := by
    intro C hC
    rcases hC with ⟨p, rfl⟩
    rw [sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_eq]
    simpa [T, sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe] using
      hmaps0.2 ⟨p, rfl⟩
  exact
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hroot hcoeff

theorem sqdiagReducedRootProfileIntersectionSectionRootCoeff_range_zMatrixSlices_coreBuildR_mem_traceRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    coreBuildR (n := n) p.2 (L p) ∈
      LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) := by
  have h :=
    sqdiagSquareBWIntersection_rootCoeff_range_zMatrixSlices_coreBuildR_read_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
      hroot
  change
    coreBuildR (n := n)
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 ∈
      LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) at h
  rw [sqdiagReducedRootProfileIntersectionSectionWithLine_read
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p] at h
  exact h

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_le_traceRange_of_intersectionRootCoeff_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) ≤
      LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) := by
  intro R hR
  rcases hR with ⟨p, rfl⟩
  simpa using
    sqdiagReducedRootProfileIntersectionSectionRootCoeff_range_zMatrixSlices_coreBuildR_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
      (hroot ⟨p, rfl⟩)

theorem sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwist_range_zMatrixSlices_coreBuildR_mem_traceRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    coreBuildR (n := n) p.2 (L p) ∈
      LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) := by
  have h :=
    sqdiagSquareBWIntersection_rootCoeff_range_zMatrixSlices_coreBuildR_read_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
      hroot
  change
    coreBuildR (n := n)
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).1
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).2 ∈
      LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) at h
  rw [sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist_read
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p] at h
  exact h

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_le_traceRange_of_traceKernelTwistRootCoeff_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) ≤
      LinearMap.range
        (sqdiagSquareRootTraceZMatrixSlices (n := n) (c := c)) := by
  intro R hR
  rcases hR with ⟨p, rfl⟩
  simpa using
    sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwist_range_zMatrixSlices_coreBuildR_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T p (hroot ⟨p, rfl⟩)

theorem sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwist_range_zMatrixSlices_coreBuildR_eq_zero_of_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    coreBuildR (n := n) p.2 (L p) = 0 := by
  have htrace :=
    sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwist_range_zMatrixSlices_coreBuildR_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T p hroot
  rw [sqdiagSquareRootTraceZMatrixSlices_range_eq_bot_of_even_two_le
    (n := n) (c := c) hn hc2] at htrace
  simpa using htrace

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_eq_bot_of_traceKernelTwistRootCoeff_range_le_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) =
      ⊥ := by
  apply le_antisymm
  · have htrace :=
      sqdiagReducedRootProfileCoreBuildRWithLine_range_le_traceRange_of_traceKernelTwistRootCoeff_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hroot
    rw [sqdiagSquareRootTraceZMatrixSlices_range_eq_bot_of_even_two_le
      (n := n) (c := c) hn hc2] at htrace
    exact htrace
  · exact bot_le

theorem sqdiagReducedRootProfileIntersectionSectionRootCoeff_range_zMatrixSlices_coreBuildR_mem_zeroSumProfileM_one
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := 1) (d := d)
          hb Nat.zero_lt_one hd L p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := 1))) :
    coreBuildR (n := n) p.2 (L p) ∈
      ZeroSumProfileM n (MatrixZeroSum n) := by
  have htrace :=
    sqdiagReducedRootProfileIntersectionSectionRootCoeff_range_zMatrixSlices_coreBuildR_mem_traceRange
      (n := n) (a := a) (b := b) (c := 1) (d := d)
      hb Nat.zero_lt_one hd L p hroot
  simpa using htrace

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_le_zeroSumProfileM_of_intersectionRootCoeff_range_le_one
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := 1) (d := d)
            hb Nat.zero_lt_one hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := 1))) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) ≤
      ZeroSumProfileM n (MatrixZeroSum n) := by
  have htrace :=
    sqdiagReducedRootProfileCoreBuildRWithLine_range_le_traceRange_of_intersectionRootCoeff_range_le
      (n := n) (a := a) (b := b) (c := 1) (d := d)
      hb Nat.zero_lt_one hd L hroot
  simpa using htrace

theorem sqdiagReducedRootProfileIntersectionSectionRootCoeff_range_zMatrixSlices_coreBuildR_mem_zeroSumProfileM_of_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    coreBuildR (n := n) p.2 (L p) ∈
      ZeroSumProfileM n (MatrixZeroSum n) := by
  have htrace :=
    sqdiagReducedRootProfileIntersectionSectionRootCoeff_range_zMatrixSlices_coreBuildR_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L p hroot
  rw [sqdiagSquareRootTraceZMatrixSlices_range_eq_zeroSumProfileM_of_odd
    (n := n) (c := c) hc hn] at htrace
  exact htrace

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_le_zeroSumProfileM_of_intersectionRootCoeff_range_le_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) ≤
      ZeroSumProfileM n (MatrixZeroSum n) := by
  have htrace :=
    sqdiagReducedRootProfileCoreBuildRWithLine_range_le_traceRange_of_intersectionRootCoeff_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hroot
  rw [sqdiagSquareRootTraceZMatrixSlices_range_eq_zeroSumProfileM_of_odd
    (n := n) (c := c) hc hn] at htrace
  exact htrace

theorem sqdiagReducedRootProfileIntersectionSectionRootCoeff_range_zMatrixSlices_coreBuildR_eq_zero_of_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hroot :
      sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L p ∈
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    coreBuildR (n := n) p.2 (L p) = 0 := by
  have htrace :=
    sqdiagReducedRootProfileIntersectionSectionRootCoeff_range_zMatrixSlices_coreBuildR_mem_traceRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L p hroot
  rw [sqdiagSquareRootTraceZMatrixSlices_range_eq_bot_of_even_two_le
    (n := n) (c := c) hn hc2] at htrace
  simpa using htrace

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_eq_bot_of_intersectionRootCoeff_range_le_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c))) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) =
      ⊥ := by
  apply le_antisymm
  · have htrace :=
      sqdiagReducedRootProfileCoreBuildRWithLine_range_le_traceRange_of_intersectionRootCoeff_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hroot
    rw [sqdiagSquareRootTraceZMatrixSlices_range_eq_bot_of_even_two_le
      (n := n) (c := c) hn hc2] at htrace
    exact htrace
  · exact bot_le

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_coreBuildR_mem_zeroSumProfileM_of_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hZ :
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    coreBuildR (n := n) p.2 (L p) ∈
      ZeroSumProfileM n (MatrixZeroSum n) := by
  have hmaps :=
    (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mp hZ
  exact
    sqdiagReducedRootProfileIntersectionSectionRootCoeff_range_zMatrixSlices_coreBuildR_mem_zeroSumProfileM_of_odd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd hn L p hmaps.1

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_le_zeroSumProfileM_of_target_odd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Odd n)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) ≤
      ZeroSumProfileM n (MatrixZeroSum n) := by
  intro R hR
  rcases hR with ⟨p, rfl⟩
  rw [sqdiagReducedRootProfileCoreBuildRWithLine_apply]
  exact
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_coreBuildR_mem_zeroSumProfileM_of_odd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd hn L p (hZ p)

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_coreBuildR_eq_zero_of_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hZ :
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    coreBuildR (n := n) p.2 (L p) = 0 := by
  have hmaps :=
    (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff_intersectionMaps_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).mp hZ
  exact
    sqdiagReducedRootProfileIntersectionSectionRootCoeff_range_zMatrixSlices_coreBuildR_eq_zero_of_even_two_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd hn hc2 L p hmaps.1

theorem sqdiagReducedRootProfileCoreBuildRWithLine_range_eq_bot_of_target_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    LinearMap.range
        (sqdiagReducedRootProfileCoreBuildRWithLine
          (n := n) (b := b) (d := d) L) =
      ⊥ := by
  apply le_antisymm
  · intro R hR
    rcases hR with ⟨p, rfl⟩
    have hzero :=
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_coreBuildR_eq_zero_of_even_two_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd hn hc2 L p (hZ p)
    rw [sqdiagReducedRootProfileCoreBuildRWithLine_apply, hzero]
    exact Submodule.zero_mem _
  · exact bot_le

theorem sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_matrixConstantRoot_mem_range_lineCoreBuildR_of_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (p : SqdiagReducedRootProfile n b d)
    (hZ :
      sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    sqdiagMatrixConstantRootCore (n := n) p.2 ∈
      LinearMap.range (sqdiagLineCoreBuildR (n := n)) := by
  exact
    sqdiagMatrixConstantRootCore_mem_range_lineCoreBuildR_of_coreBuildR_eq_zero
      (n := n) p.2 (L p)
      (sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_coreBuildR_eq_zero_of_even_two_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd hn hc2 L p hZ)

theorem sqdiagMatrixConstantRootCore_range_le_lineCoreBuildR_range_of_target_even_two_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Even n) (hc2 : 2 ≤ c)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    LinearMap.range (sqdiagMatrixConstantRootCore (n := n)) ≤
      LinearMap.range (sqdiagLineCoreBuildR (n := n)) := by
  intro R hR
  rcases hR with ⟨S, rfl⟩
  let p : SqdiagReducedRootProfile n b d := ((0, 0), S)
  exact
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_matrixConstantRoot_mem_range_lineCoreBuildR_of_even_two_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd hn hc2 L p (hZ p)

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairPresentation n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p,
      sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_mem_presentation_of_target
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p
        (hZ p)⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).map_smul r x

noncomputable def sqdiagReducedRootProfileNormalizedRelationSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    SqdiagReducedRootProfile n b d →ₗ[F] SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointAmbientPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ)

@[simp]
theorem sqdiagReducedRootProfileNormalizedRelationSectionWithLine_root_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p)).1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 := by
  change
    (sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p)).1.1.1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1
  rw [sqdiagAdjointAmbientPairPresentationSum_root_apply]
  rfl

theorem sqdiagReducedRootProfileNormalizedRelationSectionWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p)).1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 := by
  rw [sqdiagReducedRootProfileNormalizedRelationSectionWithLine_root_pairAdd,
    sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_root]

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairPresentation n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p,
      sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_mem_presentation_of_target
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p
        (hZ p)⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T).map_smul r x

noncomputable def sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) :
    SqdiagReducedRootProfile n b d →ₗ[F] SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointAmbientPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ)

@[simp]
theorem sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_root_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p)).1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).1 := by
  change
    (sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p)).1.1.1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).1
  rw [sqdiagAdjointAmbientPairPresentationSum_root_apply]
  rfl

theorem sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p)).1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 := by
  rw [sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_root_pairAdd,
    sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_root]

theorem sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_Q_eq_zero_of_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p) = 0 := by
  change
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p) = 0
  apply
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p)
  intro A hA
  exact hzero p A hA

theorem
    sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_annihilates_root_forall_iff_rootTarget_add_intersection_mem_annihilator
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    (∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0) ↔
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d := by
  constructor
  · intro hann p
    apply
      (sqdiagRootZeroACoeffAnnihilator_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p +
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L p).1.1)).mpr
    intro A hA
    rw [← sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_root
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p]
    exact hann p A hA
  · intro hroot p A hA
    have hzero :=
      (sqdiagRootZeroACoeffAnnihilator_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p +
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L p).1.1)).mp
        (hroot p) A hA
    rw [sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_root]
    exact hzero

theorem
    sqdiagReducedRootProfileNormalizedSectionWithLine_rootTarget_add_intersection_mem_annihilator_forall_iff_rootZeroACoeffEval_eq
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) :
    (∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d) ↔
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 := by
  constructor
  · intro hroot p
    let E :=
      sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
    let R :=
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p
    let I :=
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L p).1.1
    have hzero : E (R + I) = 0 := by
      exact LinearMap.mem_ker.mp (hroot p)
    have hsum : E R + E I = 0 := by
      simpa [E, R, I] using hzero
    calc
      E R = E R + 0 := by rw [add_zero]
      _ = E R + (E I + E I) := by
          rw [F_module_add_self (E I), add_zero]
      _ = (E R + E I) + E I := by abel
      _ = 0 + E I := by rw [hsum]
      _ = E I := by rw [zero_add]
  · intro heval p
    let E :=
      sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
    let R :=
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p
    let I :=
      (sqdiagReducedRootProfileIntersectionSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L p).1.1
    apply LinearMap.mem_ker.mpr
    change E (R + I) = 0
    rw [E.map_add]
    have hRI : E R = E I := by
      simpa [E, R, I] using heval p
    rw [hRI, F_module_add_self]

theorem
    sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffEval_eq_forall_of_comp_rootTarget_eq_intersectionRoot
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hcomp :
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d)) =
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileIntersectionSectionRootWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L)) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileRootTarget
            (n := n) (b := b) (c := c) (d := d) p) =
        sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileIntersectionSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L p).1.1 := by
  intro p
  have hp := congrArg (fun f => f p) hcomp
  simpa using hp

theorem sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (p : SqdiagReducedRootProfile n b d)
    (hp :
      sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
        sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d := by
  exact
    sqdiagAdjointAmbientPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p)
      hp

theorem sqdiagReducedRootProfileNormalizedRelationSectionWithLine_Q_eq_zero_of_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p) = 0 := by
  change
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p) = 0
  apply
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p)
  intro A hA
  exact hzero p A hA

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileNormalizedVerticalOrthogonalSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationVerticalOrthogonal n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p,
      horth p⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ).map_smul r x

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileNormalizedVerticalOrthogonalSectionTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationVerticalOrthogonal n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p,
      horth p⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ).map_smul r x

noncomputable def sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  (sqdiagReducedRelationVerticalOrthogonalToRootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileNormalizedVerticalOrthogonalSectionTraceKernelTwistWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ horth)

@[simp]
theorem sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ horth p).1.1 =
      sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p) := by
  exact
    sqdiagReducedRelationVerticalOrthogonalToRootDefect_apply
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedVerticalOrthogonalSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ horth p)

@[simp]
theorem sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_rootTarget
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ horth p).1.1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p).1.1 := by
  rw [sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_root,
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_root]

noncomputable def sqdiagReducedRootProfileNormalizedDefectEquivSectionTraceKernelTwistWithLine_of_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth)) :
    SqdiagReducedRootProfile n b d ≃ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  LinearEquiv.ofBijective
    (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ horth)
    hbij

theorem sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_bijective_iff_rootValue
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth) ↔
      (∀ p q : SqdiagReducedRootProfile n b d,
          (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ horth p).1.1.1 =
          (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ horth q).1.1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T hZ horth p).1.1.1 = R0.1.1.1) := by
  constructor
  · intro hbij
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hbij.1
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hroot
    · intro R0
      rcases hbij.2 R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      exact congrArg
        (fun R0 : sqdiagReducedRelationRootDefect n a b c d => R0.1.1.1)
        hp
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hp
      apply hinj
      exact congrArg
        (fun R0 : sqdiagReducedRelationRootDefect n a b c d => R0.1.1.1)
        hp
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hp

theorem sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_bijective_iff_rootTarget
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth) ↔
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLineTraceKernelTwist
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p).1.1 =
              R0.1.1.1) := by
  rw [sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_bijective_iff_rootValue
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L T hZ horth]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth p
      have hq :=
        sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth q
      exact hp.trans (hroot.trans hq.symm)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth p
      exact hrootp.symm.trans hp
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth p
      have hq :=
        sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth q
      exact hp.symm.trans (hroot.trans hq)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth p
      exact hrootp.trans hp

noncomputable def sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  (sqdiagReducedRelationVerticalOrthogonalToRootDefect
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileNormalizedVerticalOrthogonalSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth)

@[simp]
theorem sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p).1.1 =
      sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p) := by
  exact
    sqdiagReducedRelationVerticalOrthogonalToRootDefect_apply
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedVerticalOrthogonalSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p)

@[simp]
theorem sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_rootTarget
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ horth p).1.1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagReducedRootProfileIntersectionSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p).1.1 := by
  rw [sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_root,
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine_root]

theorem sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_bijective_iff_rootValue
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth) ↔
      (∀ p q : SqdiagReducedRootProfile n b d,
          (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ horth p).1.1.1 =
          (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ horth q).1.1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hZ horth p).1.1.1 = R0.1.1.1) := by
  constructor
  · intro hbij
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hbij.1
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hroot
    · intro R0
      rcases hbij.2 R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      exact congrArg
        (fun R0 : sqdiagReducedRelationRootDefect n a b c d => R0.1.1.1)
        hp
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hp
      apply hinj
      exact congrArg
        (fun R0 : sqdiagReducedRelationRootDefect n a b c d => R0.1.1.1)
        hp
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hp

theorem sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_bijective_iff_rootTarget
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth) ↔
      (∀ p q : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 =
          sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) q +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L q).1.1 →
            p = q) ∧
        (∀ R0 : sqdiagReducedRelationRootDefect n a b c d,
          ∃ p : SqdiagReducedRootProfile n b d,
            sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p).1.1 =
              R0.1.1.1) := by
  rw [sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_bijective_iff_rootValue
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ horth]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
      have hq :=
        sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth q
      exact hp.trans (hroot.trans hq.symm)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
      exact hrootp.symm.trans hp
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, ?_⟩
    · intro p q hroot
      apply hinj
      have hp :=
        sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
      have hq :=
        sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth q
      exact hp.symm.trans (hroot.trans hq)
    · intro R0
      rcases hsurj R0 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have hrootp :=
        sqdiagReducedRootProfileNormalizedToDefectSectionWithLine_rootTarget
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth p
      exact hrootp.trans hp

noncomputable def sqdiagReducedRootProfileCoreParamBOnlyPairProductExplicit
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  (sqdiagSquareBWIntersectionBOnlyPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    ((sqdiagSharedMatrixIntersectionExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
      (LinearMap.snd F
        ((LinearMap.ker (SquareRootTrace (n := n) (c := d)) ×
          LinearMap.ker (SquareRootTrace (n := n) (c := b))))
        (MatrixZeroSum n)))

@[simp]
theorem sqdiagReducedRootProfileCoreParamBOnlyPairProductExplicit_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileCoreParamBOnlyPairProductExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) =
      (sqdiagSharedMatrixIntersectionExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2).1 := by
  change
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSquareBWIntersectionBOnlyPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagSharedMatrixIntersectionExplicit
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2)) =
      (sqdiagSharedMatrixIntersectionExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2).1
  exact
    sqdiagSquareBWIntersectionBOnlyPairProduct_pairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagSharedMatrixIntersectionExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2)

@[simp]
theorem sqdiagReducedRootProfileCoreParamBOnlyPairProductWithLine_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileCoreParamBOnlyPairProductWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (0 : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) p =
      sqdiagReducedRootProfileCoreParamBOnlyPairProductExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p :=
  rfl

noncomputable def sqdiagReducedRootProfileNormalizedPairProductExplicit
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairProduct n a b c d :=
  sqdiagReducedRootProfileFullPairProduct
      (n := n) (a := a) (b := b) (c := c) (d := d) +
    sqdiagReducedRootProfileCoreParamBOnlyPairProductExplicit
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd

@[simp]
theorem sqdiagReducedRootProfileNormalizedPairProductExplicit_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) =
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        (sqdiagSharedMatrixIntersectionExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2).1 := by
  change
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p +
          sqdiagReducedRootProfileCoreParamBOnlyPairProductExplicit
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) =
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileFullPairProduct
            (n := n) (a := a) (b := b) (c := c) (d := d) p) +
        (sqdiagSharedMatrixIntersectionExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2).1
  rw [(sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
    sqdiagReducedRootProfileCoreParamBOnlyPairProductExplicit_pairAdd]

@[simp]
theorem sqdiagReducedRootProfileNormalizedPairProductWithLine_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedPairProductWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (0 : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n) p =
      sqdiagReducedRootProfileNormalizedPairProductExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p :=
  rfl

theorem sqdiagReducedRootProfileNormalizedPairProductExplicit_mem_presentation_of_target
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d)
    (hZ :
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductExplicit
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) ∈
        sqdiagZAdjointTargetSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d)) :
    sqdiagReducedRootProfileNormalizedPairProductExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p ∈
      sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
  exact hZ

abbrev sqdiagReducedRootProfileNormalizedTargetInZAdjointExplicit
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) : Prop :=
  sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairProductExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) ∈
    sqdiagZAdjointTargetSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d)

set_option synthInstance.maxHeartbeats 500000 in
noncomputable def sqdiagReducedRootProfileNormalizedPairPresentationExplicit
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      SqdiagAdjointAmbientPairPresentation n a b c d where
  toFun p :=
    ⟨sqdiagReducedRootProfileNormalizedPairProductExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p,
      sqdiagReducedRootProfileNormalizedPairProductExplicit_mem_presentation_of_target
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p
        (hZ p)⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedPairProductExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact
      (sqdiagReducedRootProfileNormalizedPairProductExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).map_smul r x

noncomputable def sqdiagReducedRootProfileNormalizedRelationExplicit
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) :
    SqdiagReducedRootProfile n b d →ₗ[F] SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointAmbientPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagReducedRootProfileNormalizedPairPresentationExplicit
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hZ)

@[simp]
theorem sqdiagReducedRootProfileNormalizedRelationExplicit_root_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hZ p)).1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p)).1 := by
  change
    (sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairPresentationExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hZ p)).1.1.1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p)).1
  rw [sqdiagAdjointAmbientPairPresentationSum_root_apply]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p)).1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p)).1
  rfl

theorem sqdiagReducedRootProfileNormalizedRelationExplicit_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedRelationExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd hZ p)).1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagSharedMatrixIntersectionExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2).1.1 := by
  rw [sqdiagReducedRootProfileNormalizedRelationExplicit_root_pairAdd,
    sqdiagReducedRootProfileNormalizedPairProductExplicit_pairAdd]
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileFullPairProduct
          (n := n) (a := a) (b := b) (c := c) (d := d) p)).1 +
      (sqdiagSharedMatrixIntersectionExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2).1.1 =
      sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d) p +
        (sqdiagSharedMatrixIntersectionExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2).1.1
  rw [sqdiagReducedRootProfileFullPairProduct_root]

noncomputable def sqdiagSharedMatrixKernelPairPresentationExplicit
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    MatrixZeroSum n →ₗ[F]
      SqdiagAdjointAmbientPairPresentation n a b c d :=
  (sqdiagSquareBWIntersectionKernelPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    (sqdiagSharedMatrixIntersectionExplicit
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)

theorem sqdiagSharedMatrixKernelPairPresentationExplicit_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagSharedMatrixKernelPairPresentationExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S ∈
      sqdiagAdjointAmbientPairPresentationVertical n a b c d := by
  exact
    sqdiagSquareBWIntersectionKernelPairPresentation_mem_vertical
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSharedMatrixIntersectionExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

theorem sqdiagSharedMatrixKernelPairPresentationExplicit_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagSharedMatrixKernelPairPresentationExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S ∈
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d :=
  sqdiagAdjointAmbientPairPresentationVertical_le_verticalOrthogonal
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagSharedMatrixKernelPairPresentationExplicit_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

noncomputable def sqdiagSharedMatrixKernelRelationExplicit
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    MatrixZeroSum n →ₗ[F] SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointAmbientPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagSharedMatrixKernelPairPresentationExplicit
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)

@[simp]
theorem sqdiagSharedMatrixKernelRelationExplicit_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixKernelRelationExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)) = 0 := by
  apply Subtype.ext
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixKernelPairPresentationExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S).1).1 = 0
  have hroot :=
    sqdiagSharedMatrixKernelPairPresentationExplicit_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S
  exact
    sqdiagAdjointAmbientPairPresentationVertical_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagSharedMatrixKernelPairPresentationExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)
      hroot

theorem sqdiagSharedMatrixKernelRelationExplicit_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagSharedMatrixKernelRelationExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S ∈
      sqdiagReducedRelationVertical n a b c d := by
  rw [LinearMap.mem_ker]
  exact
    sqdiagSharedMatrixKernelRelationExplicit_root
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S

theorem sqdiagSharedMatrixKernelRelationExplicit_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagSharedMatrixKernelRelationExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRelationVertical_le_verticalOrthogonal
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagSharedMatrixKernelRelationExplicit_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

theorem sqdiagSharedMatrixKernelRelationExplicit_Q_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixKernelRelationExplicit
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S) = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_mem_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagSharedMatrixKernelRelationExplicit
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)
    (sqdiagSharedMatrixKernelRelationExplicit_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

theorem sqdiag_coreBuildJ_zero_line_eq_const
    {n : ℕ} [NeZero n] (t : I n) :
    coreBuildJ (n := n) (0 : LineZeroSum n) t =
      coreBuildJ (n := n) (0 : LineZeroSum n) 0 := by
  let g : I n → MatrixZeroSum n := coreBuildJ (n := n) (0 : LineZeroSum n)
  have hstep : ∀ s : I n, g (s + 1) = g s := by
    intro s
    have hJ := coreBuildJ_step (n := n) (0 : LineZeroSum n) s
    have hzero : coreIncrMatrix (n := n) (0 : LineZeroSum n) s = 0 := by
      apply Subtype.ext
      funext sy sw
      rfl
    rw [hzero] at hJ
    exact (add_eq_zero_iff_eq_of_F_module _ _).mp hJ |>.symm
  simpa [g] using zmod_step_const g hstep t

theorem sqdiag_coreBuildS_zero_line
    {n : ℕ} [NeZero n] (S : MatrixZeroSum n) (t : I n) :
    coreBuildS (n := n) S (0 : LineZeroSum n) t = S := by
  apply Subtype.ext
  funext sy sw
  unfold coreBuildS
  have hJ :=
    congrArg (fun M : MatrixZeroSum n => M.1 sy sw)
      (sqdiag_coreBuildJ_zero_line_eq_const (n := n) t)
  have hJval :
      (coreBuildJ (n := n) (0 : LineZeroSum n) t).1 sy sw =
        (coreBuildJ (n := n) (0 : LineZeroSum n) 0).1 sy sw := by
    simpa using hJ
  change
    S.1 sy sw +
        (coreBuildJ (n := n) (0 : LineZeroSum n) t).1 sy sw +
      (coreBuildJ (n := n) (0 : LineZeroSum n) 0).1 sy sw =
      S.1 sy sw
  rw [hJval]
  have hdouble :
      (coreBuildJ (n := n) (0 : LineZeroSum n) 0).1 sy sw +
          (coreBuildJ (n := n) (0 : LineZeroSum n) 0).1 sy sw = 0 :=
    F_add_self _
  rw [add_assoc, hdouble, add_zero]

@[simp]
theorem sqdiag_coreBuildAVal_zero_line
    {n : ℕ} [NeZero n] (S : MatrixZeroSum n) (z sy sw : I n) :
    coreBuildAVal (n := n) S (0 : LineZeroSum n) z sy sw =
      S.1 sy sw := by
  unfold coreBuildAVal
  rw [sqdiag_coreBuildS_zero_line]
  simp

noncomputable def sqdiagReducedRootProfileSharedRelation
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SqdiagReducedRootProfile n b d →ₗ[F] SqdiagReducedRelation n a b c d :=
  (sqdiagSharedMatrixKernelRelationExplicit
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    ((LinearMap.snd F
      ((LinearMap.ker (SquareRootTrace (n := n) (c := d)) ×
        LinearMap.ker (SquareRootTrace (n := n) (c := b))))
      (MatrixZeroSum n)))

@[simp]
theorem sqdiagReducedRootProfileSharedRelation_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileSharedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) = 0 :=
  sqdiagSharedMatrixKernelRelationExplicit_root
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p.2

theorem sqdiagReducedRootProfileSharedRelation_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileSharedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p ∈
      sqdiagReducedRelationVertical n a b c d := by
  rw [LinearMap.mem_ker]
  exact
    sqdiagReducedRootProfileSharedRelation_root
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p

theorem sqdiagReducedRootProfileSharedRelation_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileSharedRelation
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRelationVertical_le_verticalOrthogonal
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRootProfileSharedRelation_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p)

theorem sqdiagReducedRootProfile_sharedMatrix_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileSharedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p) = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_mem_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRootProfileSharedRelation
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p)
    (sqdiagReducedRootProfileSharedRelation_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd p)

noncomputable def sqdiagSharedMatrixIntersection
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    MatrixZeroSum n →ₗ[F] SquareBWIntersection n a b c d :=
  (sqdiagSquareBWIntersectionCoreParamSection
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    (sqdiagSharedMatrixCoreParam (n := n))

@[simp]
theorem sqdiagSharedMatrixIntersection_read
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSharedMatrixIntersection
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S) =
      (S, 0) := by
  change
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSquareBWIntersectionCoreParamSection
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          (sqdiagSharedMatrixCoreParam (n := n) S)) =
      (S, 0)
  simpa using
    sqdiagSquareBWIntersectionCoreParamRead_section
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
      (sqdiagSharedMatrixCoreParam (n := n) S)

@[simp]
theorem sqdiagSharedMatrixIntersection_read_matrix
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSharedMatrixIntersection
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)).1 =
      S := by
  exact congrArg Prod.fst
    (sqdiagSharedMatrixIntersection_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

@[simp]
theorem sqdiagSharedMatrixIntersection_read_line
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSharedMatrixIntersection
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)).2 =
      0 := by
  exact congrArg Prod.snd
    (sqdiagSharedMatrixIntersection_read
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

noncomputable def sqdiagSharedMatrixKernelPairPresentation
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    MatrixZeroSum n →ₗ[F]
      SqdiagAdjointAmbientPairPresentation n a b c d :=
  (sqdiagSquareBWIntersectionKernelPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).comp
    (sqdiagSharedMatrixIntersection
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)

theorem sqdiagSharedMatrixKernelPairPresentation_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagSharedMatrixKernelPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S ∈
      sqdiagAdjointAmbientPairPresentationVertical n a b c d := by
  exact
    sqdiagSquareBWIntersectionKernelPairPresentation_mem_vertical
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
        (sqdiagSharedMatrixIntersection
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

theorem sqdiagSharedMatrixKernelPairPresentation_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagSharedMatrixKernelPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S ∈
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d :=
  sqdiagAdjointAmbientPairPresentationVertical_le_verticalOrthogonal
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagSharedMatrixKernelPairPresentation_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

noncomputable def sqdiagSharedMatrixKernelRelation
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    MatrixZeroSum n →ₗ[F] SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointAmbientPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagSharedMatrixKernelPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)

@[simp]
theorem sqdiagSharedMatrixKernelRelation_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    (sqdiagReducedRelationRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixKernelRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)) = 0 := by
  apply Subtype.ext
  change
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixKernelPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S).1).1 = 0
  have hroot :=
    sqdiagSharedMatrixKernelPairPresentation_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S
  exact
    sqdiagAdjointAmbientPairPresentationVertical_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagSharedMatrixKernelPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)
      hroot

theorem sqdiagSharedMatrixKernelRelation_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagSharedMatrixKernelRelation
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S ∈
      sqdiagReducedRelationVertical n a b c d := by
  rw [LinearMap.mem_ker]
  exact
    sqdiagSharedMatrixKernelRelation_root
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S

theorem sqdiagSharedMatrixKernelRelation_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagSharedMatrixKernelRelation
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRelationVertical_le_verticalOrthogonal
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagSharedMatrixKernelRelation_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

theorem sqdiagSharedMatrixKernelRelation_Q_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : MatrixZeroSum n) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagSharedMatrixKernelRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S) = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_mem_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagSharedMatrixKernelRelation
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)
    (sqdiagSharedMatrixKernelRelation_mem_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd S)

theorem sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_rootProfile_equiv_repr
    {n a b c d : ℕ} [NeZero n]
    (e :
      sqdiagReducedRelationRootDefect n a b c d ≃ₗ[F]
        SqdiagReducedRootProfile n b d)
    (repr :
      SqdiagReducedRootProfile n b d →ₗ[F]
        sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hdef :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRelationVerticalOrthogonalToRootDefect
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (repr p) =
          e.symm p)
    (hQ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (repr p).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  refine
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_defect_section
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (repr.comp e.toLinearMap) ?_ ?_ x hx
  · intro R0
    have h := hdef (e R0)
    exact h.trans (e.symm_apply_apply R0)
  · intro R0
    exact hQ (e R0)

theorem sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_rootProfile_repr
    {n a b c d : ℕ} [NeZero n]
    (e :
      SqdiagReducedRootProfile n b d ≃ₗ[F]
        sqdiagReducedRelationRootDefect n a b c d)
    (repr :
      SqdiagReducedRootProfile n b d →ₗ[F]
        sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hdef :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRelationVerticalOrthogonalToRootDefect
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (repr p) =
          e p)
    (hQ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRelationQ
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (repr p).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  refine
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_defect_section
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (repr.comp e.symm.toLinearMap) ?_ ?_ x hx
  · intro R0
    have h := hdef (e.symm R0)
    exact h.trans (e.apply_symm_apply R0)
  · intro R0
    exact hQ (e.symm R0)

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionTraceKernelTwistWithLine_profile_equiv
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (e :
      SqdiagReducedRootProfile n b d ≃ₗ[F]
        sqdiagReducedRelationRootDefect n a b c d)
    (hdef :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ horth p =
          e p)
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_rootProfile_repr
      (n := n) (a := a) (b := b) (c := c) (d := d) e
      (sqdiagReducedRootProfileNormalizedVerticalOrthogonalSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ horth)
      (by
        intro p
        change
          sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T hZ horth p =
            e p
        exact hdef p)
      (by
        intro p
        exact
          sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_Q_eq_zero_of_rootCoeff_zero
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ hzero p)
      x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionTraceKernelTwistWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let e :=
    sqdiagReducedRootProfileNormalizedDefectEquivSectionTraceKernelTwistWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ horth hbij
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionTraceKernelTwistWithLine_profile_equiv
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ horth e (by intro p; rfl) hzero x hx

noncomputable def sqdiagReducedRootProfileNormalizedDefectEquivWithLine_of_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth)) :
    SqdiagReducedRootProfile n b d ≃ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  LinearEquiv.ofBijective
    (sqdiagReducedRootProfileNormalizedToDefectWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth)
    hbij

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let e :=
    sqdiagReducedRootProfileNormalizedDefectEquivWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_rootProfile_repr
      (n := n) (a := a) (b := b) (c := c) (d := d) e
      (sqdiagReducedRootProfileNormalizedVerticalOrthogonalWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth)
      (by
        intro p
        rfl)
      (by
        intro p
        exact
          sqdiagReducedRootProfileNormalizedRelationWithLine_Q_eq_zero_of_rootCoeff_zero
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hzero p)
      x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_profile_equiv
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (e :
      SqdiagReducedRootProfile n b d ≃ₗ[F]
        sqdiagReducedRelationRootDefect n a b c d)
    (hdef :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ horth p =
          e p)
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_rootProfile_repr
      (n := n) (a := a) (b := b) (c := c) (d := d) e
      (sqdiagReducedRootProfileNormalizedVerticalOrthogonalSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth)
      (by
        intro p
        change
          sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hZ horth p =
            e p
        exact hdef p)
      (by
        intro p
        exact
          sqdiagReducedRootProfileNormalizedRelationSectionWithLine_Q_eq_zero_of_rootCoeff_zero
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hzero p)
      x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_YZCorrectedSectionWithLine_profile_equiv
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (e :
      SqdiagReducedRootProfile n b d ≃ₗ[F]
        sqdiagReducedRelationRootDefect n a b c d)
    (hdef :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ horth p =
          e p)
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_rootProfile_repr
      (n := n) (a := a) (b := b) (c := c) (d := d) e
      (sqdiagReducedRootProfileYZCorrectedVerticalOrthogonalSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L Z hZ horth)
      (by
        intro p
        change
          sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L Z hZ horth p =
            e p
        exact hdef p)
      (by
        intro p
        exact
          sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine_Q_eq_zero_of_rootCoeff_zero
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L Z hZ hzero p)
      x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_YZCorrectedSectionWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (Z : SqdiagReducedRootProfile n b d →ₗ[F] YZCoeff n d)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileYZCorrectedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileYZCorrectedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L Z hZ horth))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileYZCorrectedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L Z p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let e :=
    sqdiagReducedRootProfileYZCorrectedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth hbij
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_YZCorrectedSectionWithLine_profile_equiv
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L Z hZ horth e
      (by
        intro p
        rfl)
      hzero x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_equiv_profile
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (e :
      sqdiagReducedRelationRootDefect n a b c d ≃ₗ[F]
        SqdiagReducedRootProfile n b d)
    (hdef :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ horth p =
          e.symm p)
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_rootProfile_equiv_repr
      (n := n) (a := a) (b := b) (c := c) (d := d) e
      (sqdiagReducedRootProfileNormalizedVerticalOrthogonalSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth)
      (by
        intro p
        change
          sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L hZ horth p =
            e.symm p
        exact hdef p)
      (by
        intro p
        exact
          sqdiagReducedRootProfileNormalizedRelationSectionWithLine_Q_eq_zero_of_rootCoeff_zero
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hzero p)
      x hx

noncomputable def sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth)) :
    SqdiagReducedRootProfile n b d ≃ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  LinearEquiv.ofBijective
    (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth)
    hbij

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let e :=
    sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_profile_equiv
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth e
      (by
        intro p
        rfl)
      hzero x hx

theorem sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hpair :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ p (hpair p)

theorem sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_polar_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hpolar :
      ∀ (p : SqdiagReducedRootProfile n b d)
        (y : SqdiagAdjointAmbientPairPresentation n a b c d),
        y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d →
          sqdiagAdjointAmbientPairPresentationPolar
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L hZ p) y = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d :=
  (sqdiagAdjointAmbientPairPresentation_mem_verticalOrthogonal_iff_polar_eq_zero
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ p)).mpr (hpolar p)

theorem sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_polar_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hpolar :
      ∀ (p : SqdiagReducedRootProfile n b d)
        (y : SqdiagAdjointAmbientPairPresentation n a b c d),
        y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d →
          sqdiagAdjointAmbientPairPresentationPolar
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L hZ p) y = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ p
    (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_polar_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hpolar p)

theorem sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_annihilates_root_of_relation_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
      A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p)).1 = 0 := by
  intro p A hA
  have hrootZero :=
    (sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p)).mp (horth p) A hA
  change
    sqdiagRootCoeffApply
        (n := n) (b := b) (c := c) (d := d) A
        ((sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p)).1) = 0 at hrootZero
  rwa [sqdiagReducedRootProfileNormalizedRelationSectionWithLine_root_pairAdd
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ p] at hrootZero

noncomputable def sqdiagReducedRootProfileNormalizedDefectEquivPairSectionWithLine_of_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hpair :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hpair))) :
    SqdiagReducedRootProfile n b d ≃ₗ[F]
      sqdiagReducedRelationRootDefect n a b c d :=
  sqdiagReducedRootProfileNormalizedDefectEquivSectionWithLine_of_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ
    (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hpair)
    hbij

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hpair :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hpair)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hpair)
      hbij hzero x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_polar_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hpolar :
      ∀ (p : SqdiagReducedRootProfile n b d)
        (y : SqdiagAdjointAmbientPairPresentation n a b c d),
        y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d →
          sqdiagAdjointAmbientPairPresentationPolar
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L hZ p) y = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_polar_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hpolar)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_polar_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hpolar)
      hbij hzero x hx

theorem sqdiagReducedRootProfileNormalizedWithLine_rootZeroACoeffSpace_annihilates_root_of_relation_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
      A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p)).1 = 0 := by
  intro p A hA
  have hrootZero :=
    (sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedRelationWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p)).mp (horth p) A hA
  change
    sqdiagRootCoeffApply
        (n := n) (b := b) (c := c) (d := d) A
        ((sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedRelationWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p)).1) = 0 at hrootZero
  rwa [sqdiagReducedRootProfileNormalizedRelationWithLine_root_pairAdd
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ p] at hrootZero

theorem sqdiagReducedRootProfileNormalizedPairPresentationWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedPairPresentationWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p ∈
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
  refine
    sqdiagAdjointAmbientPairPresentation_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairPresentationWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p) ?_
  intro A hA
  simpa [sqdiagReducedRootProfileNormalizedPairPresentationWithLine] using
    hann p A hA

theorem sqdiagReducedRootProfileNormalizedRelationWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedRelationWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileNormalizedRelationWithLine_mem_verticalOrthogonal_of_pair
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ p
    (sqdiagReducedRootProfileNormalizedPairPresentationWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann p)

theorem sqdiagReducedRootProfileNormalizedRelationWithLine_mem_verticalOrthogonal_forall_iff_rootZeroACoeffSpace_annihilates_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    (∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedRelationWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
        sqdiagReducedRelationVerticalOrthogonal n a b c d) ↔
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0 := by
  constructor
  · intro horth
    exact
      sqdiagReducedRootProfileNormalizedWithLine_rootZeroACoeffSpace_annihilates_root_of_relation_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth
  · intro hann
    exact
      sqdiagReducedRootProfileNormalizedRelationWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hann

theorem sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p ∈
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
  refine
    sqdiagAdjointAmbientPairPresentation_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p) ?_
  intro A hA
  simpa [sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine] using
    hann p A hA

theorem sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hann)
    p

theorem sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_forall_iff_rootZeroACoeffSpace_annihilates_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    (∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
        sqdiagReducedRelationVerticalOrthogonal n a b c d) ↔
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0 := by
  constructor
  · intro horth
    exact
      sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_annihilates_root_of_relation_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth
  · intro hann
    exact
      sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hann

theorem
    sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p ∈
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
  have hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0 :=
    (sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_annihilates_root_forall_iff_rootTarget_add_intersection_mem_annihilator
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).mpr hroot
  exact
    sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann p

theorem
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ
    (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hroot)
    p

theorem
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_forall_iff_rootTarget_add_intersection_mem_annihilator
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    (∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
        sqdiagReducedRelationVerticalOrthogonal n a b c d) ↔
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d := by
  constructor
  · intro horth
    have hann :
        ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) A
                (sqdiagAdjointAmbientPairAdd
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                    (n := n) (a := a) (b := b) (c := c) (d := d)
                    hb hc hd L p)).1 = 0 :=
      sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_annihilates_root_of_relation_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ horth
    exact
      (sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_annihilates_root_forall_iff_rootTarget_add_intersection_mem_annihilator
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).mp hann
  · intro hroot
    exact
      sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hroot

theorem
    sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (heval :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p ∈
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
  have hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d :=
    (sqdiagReducedRootProfileNormalizedSectionWithLine_rootTarget_add_intersection_mem_annihilator_forall_iff_rootZeroACoeffEval_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).mpr heval
  exact
    sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hroot p

theorem
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (heval :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_pair_forall
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ
    (sqdiagReducedRootProfileNormalizedPairPresentationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ heval)
    p

theorem
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_comp_eq
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hcomp :
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileRootTarget
          (n := n) (b := b) (c := c) (d := d)) =
      (sqdiagRootZeroACoeffEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagReducedRootProfileIntersectionSectionRootWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ
    (sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffEval_eq_forall_of_comp_rootTarget_eq_intersectionRoot
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hcomp)
    p

theorem sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_pair
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (p : SqdiagReducedRootProfile n b d)
    (hp :
      sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
        sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d := by
  exact
    sqdiagAdjointAmbientPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p)
      hp

theorem
    sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (heval :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ p ∈
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
  have hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L T p)).1 = 0 := by
    intro p A hA
    let E :=
      sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
    let R :=
      sqdiagReducedRootProfileRootTarget
        (n := n) (b := b) (c := c) (d := d) p
    let I :=
      sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p
    have hmem : R + I ∈ sqdiagRootZeroACoeffAnnihilator n a b c d := by
      apply LinearMap.mem_ker.mpr
      change E (R + I) = 0
      rw [E.map_add]
      have hRI : E R = E I := by
        simpa [E, R, I] using heval p
      rw [hRI, F_module_add_self]
    have hzero :=
      (sqdiagRootZeroACoeffAnnihilator_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (R + I)).mp hmem A hA
    rw [sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_root]
    simpa [R, I] using hzero
  refine
    sqdiagAdjointAmbientPairPresentation_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ p) ?_
  intro A hA
  simpa [sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine] using
    hann p A hA

theorem
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (heval :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p))
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_pair
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L T hZ p
    (sqdiagReducedRootProfileNormalizedPairPresentationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ heval p)

theorem
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelPullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hEvalRange) p)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
        (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hEvalRange) hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L
    (sqdiagReducedRootProfileTraceKernelTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange)
    hZ
    (sqdiagReducedRootProfileIntersectionSectionRootTraceKernelTwistWithLine_eval_eq_rootTarget_of_rootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hEvalRange)
    p

theorem
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelZSliceTwistWithLine_mem_verticalOrthogonal_of_rootZeroZSliceEvalRangeLe
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZSliceEvalRange :
      LinearMap.range
          (((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d))) +
            ((sqdiagRootZeroACoeffEvalMap
                (n := n) (a := a) (b := b) (c := c) (d := d)).comp
              (sqdiagReducedRootProfileIntersectionSectionRootWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L))) ≤
        LinearMap.range
          (sqdiagRootTraceKernelZSlicePullYWEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
          (sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZSliceEvalRange) p)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L
        (sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZSliceEvalRange) hZ p ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d :=
  sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L
    (sqdiagReducedRootProfileTraceKernelZSliceTwistOfRootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange)
    hZ
    (sqdiagReducedRootProfileIntersectionSectionRootTraceKernelZSliceTwistWithLine_eval_eq_rootTarget_of_rootZeroEvalRangeLe
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZSliceEvalRange)
    p

theorem sqdiagReducedRootProfileNormalizedSectionTraceKernelTwistWithLine_rootZeroACoeffSpace_annihilates_root_of_relation_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
      A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p)).1 = 0 := by
  intro p A hA
  have hrootZero :=
    (sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ p)).mp (horth p) A hA
  change
    sqdiagRootCoeffApply
        (n := n) (b := b) (c := c) (d := d) A
        ((sqdiagReducedRelationRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p)).1) = 0 at hrootZero
  rwa [sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine_root_pairAdd
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L T hZ p] at hrootZero

theorem sqdiagReducedRootProfileNormalizedSectionTraceKernelTwistWithLine_rootCoeff_zero_of_rootZeroACoeffSpace_coeff_repr
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L T p)).1 = 0)
    (hcoeffRootZero :
      ∀ p : SqdiagReducedRootProfile n b d,
        ∃ B : RootTarget n b c d,
          B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) B =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L T p)).2) :
    ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T p)).2 →
      sqdiagRootCoeffApply
          (n := n) (b := b) (c := c) (d := d) A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L T p)).1 = 0 := by
  intro p A hA
  rcases hcoeffRootZero p with ⟨B, hBrootZero, hB⟩
  have hrootZ :
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T p)).1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
    ((sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T p).mp (hZ p)).1
  have hsame :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B :=
    hA.trans hB.symm
  have heq :=
    sqdiagRootCoeffApply_eq_of_KCAdjointCoeff_eq_of_mem_ZDiff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      A B
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T p)).1
      hsame hrootZ
  rw [heq]
  exact hann p B hBrootZero

theorem
    sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_forall_iff_rootZeroACoeffEval_eq
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    (∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedRelationSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
        sqdiagReducedRelationVerticalOrthogonal n a b c d) ↔
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 := by
  constructor
  · intro horth
    have hroot :
        ∀ p : SqdiagReducedRootProfile n b d,
          sqdiagReducedRootProfileRootTarget
                (n := n) (b := b) (c := c) (d := d) p +
              (sqdiagReducedRootProfileIntersectionSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p).1.1 ∈
            sqdiagRootZeroACoeffAnnihilator n a b c d :=
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_forall_iff_rootTarget_add_intersection_mem_annihilator
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ).mp horth
    exact
      (sqdiagReducedRootProfileNormalizedSectionWithLine_rootTarget_add_intersection_mem_annihilator_forall_iff_rootZeroACoeffEval_eq
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).mp hroot
  · intro heval
    exact
      sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ heval

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_annihilates_root_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hann)
      hbij hzero x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootTarget_add_intersection_mem_annihilator_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hroot)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hroot)
      hbij hzero x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffEval_eq_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (heval :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p) =
          sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ heval)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ
      (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffEval_eq_forall
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ heval)
      hbij hzero x hx

theorem sqdiagReducedRootProfileNormalizedSectionWithLine_rootCoeff_zero_of_rootZeroACoeffSpace_coeff_repr
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hcoeffRootZero :
      ∀ p : SqdiagReducedRootProfile n b d,
        ∃ B : RootTarget n b c d,
          B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) B =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).2) :
    ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
      sqdiagRootCoeffApply
          (n := n) (b := b) (c := c) (d := d) A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0 := by
  intro p A hA
  rcases hcoeffRootZero p with ⟨B, hBrootZero, hB⟩
  have hrootZ :
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
    ((sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L p).mp (hZ p)).1
  have hsame :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B :=
    hA.trans hB.symm
  have heq :=
    sqdiagRootCoeffApply_eq_of_KCAdjointCoeff_eq_of_mem_ZDiff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      A B
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1
      hsame hrootZ
  rw [heq]
  exact hann p B hBrootZero

theorem sqdiagRootZeroACoeffSpace_coeff_repr_of_KCAdjointMap_range
    {n a b c d : ℕ} [NeZero n]
    (C : CFun4 n a b d)
    (hC :
      C ∈ LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (hrootZero :
      (⟨C, hC⟩ :
        ↑(LinearMap.range
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))) ∈
        LinearMap.range
          (sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    ∃ B : RootTarget n b c d,
      B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) B = C := by
  rcases hrootZero with ⟨B, hB⟩
  refine ⟨B.1, B.2, ?_⟩
  have hval := congrArg Subtype.val hB
  change
    sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d) B.1 = C
      at hval
  simpa [sqdiagKCAdjointMap_apply] using hval

theorem sqdiagRootZeroACoeffSpace_coeff_repr_of_reducedRelationVerticalCoeffMap_range
    {n a b c d : ℕ} [NeZero n]
    (C :
      ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d))))
    (hC :
      C ∈ LinearMap.range
        (sqdiagReducedRelationVerticalCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) :
    ∃ B : RootTarget n b c d,
      B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) B = C.1 := by
  exact
    sqdiagRootZeroACoeffSpace_coeff_repr_of_KCAdjointMap_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      C.1 C.2
      (by
        rw [sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap_range_eq_reducedRelationVerticalCoeffMap_range
          (n := n) (a := a) (b := b) (c := c) (d := d)]
        exact hC)

noncomputable def sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (p : SqdiagReducedRootProfile n b d) :
    ↑(LinearMap.range
      (sqdiagKCAdjointMap
        (n := n) (a := a) (b := b) (c := c) (d := d))) :=
  ⟨(sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2, by
    rcases ((sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L p).mp (hZ p)).2 with ⟨A, hA⟩
    exact ⟨A, by simpa [sqdiagKCAdjointMap_apply] using hA⟩⟩

@[simp]
theorem sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine_val
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ p).1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 :=
  rfl

noncomputable def sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) where
  toFun p :=
    sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p
  map_add' x y := by
    apply Subtype.ext
    have hmap :=
      (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).map_add x y
    simpa [sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine_val,
      sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_coeff,
      sqdiagReducedRootProfileNormalizedSectionCoeffWithLine_apply] using hmap
  map_smul' r x := by
    apply Subtype.ext
    have hmap :=
      (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).map_smul r x
    simpa [sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine_val,
      sqdiagReducedRootProfileNormalizedPairProductSectionWithLine_coeff,
      sqdiagReducedRootProfileNormalizedSectionCoeffWithLine_apply] using hmap

@[simp]
theorem sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p =
      sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p :=
  rfl

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine_mem_reducedVerticalCoeffMap_range_of_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hrange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ p ∈
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro p
  exact hrange ⟨p, rfl⟩

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine_range_le_reducedVerticalCoeffMap_iff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p) :
    LinearMap.range
        (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
      LinearMap.range
        (sqdiagReducedRelationVerticalCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  constructor
  · intro hrange
    exact
      sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine_mem_reducedVerticalCoeffMap_range_of_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hrange
  · intro hpoint C hC
    rcases hC with ⟨p, rfl⟩
    exact hpoint p

noncomputable def sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (p : SqdiagReducedRootProfile n b d) :
    ↑(LinearMap.range
      (sqdiagKCAdjointMap
        (n := n) (a := a) (b := b) (c := c) (d := d))) :=
  ⟨(sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).2, by
    rcases ((sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T p).mp (hZ p)).2 with ⟨A, hA⟩
    exact ⟨A, by simpa [sqdiagKCAdjointMap_apply] using hA⟩⟩

@[simp]
theorem sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine_val
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (p : SqdiagReducedRootProfile n b d) :
    (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ p).1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)).2 :=
  rfl

noncomputable def sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) :
    SqdiagReducedRootProfile n b d →ₗ[F]
      ↑(LinearMap.range
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) where
  toFun p :=
    sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p
  map_add' x y := by
    apply Subtype.ext
    have hmap :=
      (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T).map_add x y
    simpa [sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine_val,
      sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_coeff,
      sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_apply] using hmap
  map_smul' r x := by
    apply Subtype.ext
    have hmap :=
      (sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T).map_smul r x
    simpa [sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine_val,
      sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine_coeff,
      sqdiagReducedRootProfileNormalizedSectionCoeffTraceKernelTwistWithLine_apply] using hmap

@[simp]
theorem sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (p : SqdiagReducedRootProfile n b d) :
    sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ p =
      sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ p :=
  rfl

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine_mem_reducedVerticalCoeffMap_range_of_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (hrange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ p ∈
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro p
  exact hrange ⟨p, rfl⟩

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine_range_le_reducedVerticalCoeffMap_iff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) :
    LinearMap.range
        (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ) ≤
      LinearMap.range
        (sqdiagReducedRelationVerticalCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  constructor
  · intro hrange
    exact
      sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine_mem_reducedVerticalCoeffMap_range_of_range_le
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ hrange
  · intro hpoint C hC
    rcases hC with ⟨p, rfl⟩
    exact hpoint p

set_option synthInstance.maxHeartbeats 500000 in
theorem sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine_range_le_reducedVerticalCoeffMap_iff_exists_linear_lift
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p) :
    LinearMap.range
        (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ) ≤
      LinearMap.range
        (sqdiagReducedRelationVerticalCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ↔
      ∃ V : SqdiagReducedRootProfile n b d →ₗ[F]
          sqdiagReducedRelationVertical n a b c d,
        (sqdiagReducedRelationVerticalCoeffMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).comp V =
          sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ := by
  exact
    linearMap_range_le_iff_exists_comp
      (sqdiagReducedRelationVerticalCoeffMap
        (n := n) (a := a) (b := b) (c := c) (d := d))
      (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ)

theorem sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_coeff_repr_of_KCAdjointRange
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hrootZeroRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      ∃ B : RootTarget n b c d,
        B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p)).2 := by
  intro p
  exact
    sqdiagRootZeroACoeffSpace_coeff_repr_of_KCAdjointMap_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L p)).2
      (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p).2
      (hrootZeroRange p)

theorem sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_coeff_repr_of_reducedVerticalCoeffMap_range
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hverticalCoeffRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      ∃ B : RootTarget n b c d,
        B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p)).2 := by
  intro p
  exact
    sqdiagRootZeroACoeffSpace_coeff_repr_of_reducedRelationVerticalCoeffMap_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ p)
      (hverticalCoeffRange p)

theorem sqdiagReducedRootProfileNormalizedSectionTraceKernelTwistWithLine_rootZeroACoeffSpace_coeff_repr_of_reducedVerticalCoeffMap_range
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (hverticalCoeffRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      ∃ B : RootTarget n b c d,
        B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionTraceKernelTwistWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L T p)).2 := by
  intro p
  exact
    sqdiagRootZeroACoeffSpace_coeff_repr_of_reducedRelationVerticalCoeffMap_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ p)
      (hverticalCoeffRange p)

theorem sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_coeff_repr_of_KCAdjointMap_range
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hrootZeroRange :
      ∀ (p : SqdiagReducedRootProfile n b d)
        (hC :
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p)).2 ∈
            LinearMap.range
              (sqdiagKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d))),
          (⟨(sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p)).2, hC⟩ :
            ↑(LinearMap.range
              (sqdiagKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d)))) ∈
            LinearMap.range
              (sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d))) :
    ∀ p : SqdiagReducedRootProfile n b d,
      ∃ B : RootTarget n b c d,
        B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p)).2 := by
  intro p
  have hC :
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L p)).2 ∈
        LinearMap.range
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    rcases ((sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L p).mp (hZ p)).2 with ⟨A, hA⟩
    exact ⟨A, by simpa [sqdiagKCAdjointMap_apply] using hA⟩
  exact
    sqdiagRootZeroACoeffSpace_coeff_repr_of_KCAdjointMap_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L p)).2
      hC (hrootZeroRange p hC)

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hcoeffRootZero :
      ∀ p : SqdiagReducedRootProfile n b d,
        ∃ B : RootTarget n b c d,
          B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) B =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).2)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_annihilates_root_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ hann hbij
    (sqdiagReducedRootProfileNormalizedSectionWithLine_rootCoeff_zero_of_rootZeroACoeffSpace_coeff_repr
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann hcoeffRootZero)
    x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootTarget_add_intersection_mem_annihilator_rootZeroACoeffSpace_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hroot :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileRootTarget
              (n := n) (b := b) (c := c) (d := d) p +
            (sqdiagReducedRootProfileIntersectionSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p).1.1 ∈
          sqdiagRootZeroACoeffAnnihilator n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootTarget_add_intersection_mem_annihilator_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hroot)))
    (hcoeffRootZero :
      ∀ p : SqdiagReducedRootProfile n b d,
        ∃ B : RootTarget n b c d,
          B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) B =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).2)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  have hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0 :=
    (sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_annihilates_root_forall_iff_rootTarget_add_intersection_mem_annihilator
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L).mpr hroot
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootTarget_add_intersection_mem_annihilator_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hroot hbij
      (sqdiagReducedRootProfileNormalizedSectionWithLine_rootCoeff_zero_of_rootZeroACoeffSpace_coeff_repr
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hann hcoeffRootZero)
      x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpaceKCAdjointMap_range_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hrootZeroRange :
      ∀ (p : SqdiagReducedRootProfile n b d)
        (hC :
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p)).2 ∈
            LinearMap.range
              (sqdiagKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d))),
          (⟨(sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p)).2, hC⟩ :
            ↑(LinearMap.range
              (sqdiagKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d)))) ∈
            LinearMap.range
              (sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ hann hbij
    (sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_coeff_repr_of_KCAdjointMap_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hrootZeroRange)
    x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpaceKCAdjointRange_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hrootZeroRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ hann hbij
    (sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_coeff_repr_of_KCAdjointRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hrootZeroRange)
    x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_reducedVerticalCoeffMap_range_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hverticalCoeffRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ hann hbij
    (sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_coeff_repr_of_reducedVerticalCoeffMap_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hverticalCoeffRange)
    x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hverticalCoeffRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let hann :=
    sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_annihilates_root_of_relation_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth
  let hcoeffRootZero :=
    sqdiagReducedRootProfileNormalizedSectionWithLine_rootZeroACoeffSpace_coeff_repr_of_reducedVerticalCoeffMap_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hverticalCoeffRange
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij
      (sqdiagReducedRootProfileNormalizedSectionWithLine_rootCoeff_zero_of_rootZeroACoeffSpace_coeff_repr
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L hZ hann hcoeffRootZero)
      x hx

set_option synthInstance.maxHeartbeats 500000 in
theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_le_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hrange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L hZ horth hbij
    (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine_mem_reducedVerticalCoeffMap_range_of_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hrange)
    x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionTraceKernelTwistWithLine_reducedVerticalCoeffMap_range_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth))
    (hverticalCoeffRange :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let hann :=
    sqdiagReducedRootProfileNormalizedSectionTraceKernelTwistWithLine_rootZeroACoeffSpace_annihilates_root_of_relation_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ horth
  let hcoeffRootZero :=
    sqdiagReducedRootProfileNormalizedSectionTraceKernelTwistWithLine_rootZeroACoeffSpace_coeff_repr_of_reducedVerticalCoeffMap_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ hverticalCoeffRange
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionTraceKernelTwistWithLine_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ horth hbij
      (sqdiagReducedRootProfileNormalizedSectionTraceKernelTwistWithLine_rootCoeff_zero_of_rootZeroACoeffSpace_coeff_repr
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb hc hd L T hZ hann hcoeffRootZero)
      x hx

set_option synthInstance.maxHeartbeats 500000 in
theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionTraceKernelTwistWithLine_reducedVerticalCoeffMap_range_le_bijective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (T :
      SqdiagReducedRootProfile n b d →ₗ[F]
        (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
          LinearMap.ker (SquareCompatTrace (n := n) (a := a))))
    (hZ :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T p)
    (horth :
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L T hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionTraceKernelTwistWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L T hZ horth))
    (hrange :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapTraceKernelTwistWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L T hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionTraceKernelTwistWithLine_reducedVerticalCoeffMap_range_bijective
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc hd L T hZ horth hbij
    (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeTraceKernelTwistWithLine_mem_reducedVerticalCoeffMap_range_of_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L T hZ hrange)
    x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_annihilates_root_bijective_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hzero :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).2 →
        sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L p)).1 = 0)
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpace_annihilates_root_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann hbij hzero x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpaceKCAdjointMap_range_bijective_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hrootZeroRange :
      ∀ (p : SqdiagReducedRootProfile n b d)
        (hC :
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hb hc hd L p)).2 ∈
            LinearMap.range
              (sqdiagKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d))),
          (⟨(sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                (n := n) (a := a) (b := b) (c := c) (d := d)
                hb hc hd L p)).2, hC⟩ :
            ↑(LinearMap.range
              (sqdiagKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d)))) ∈
            LinearMap.range
              (sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpaceKCAdjointMap_range_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann hbij hrootZeroRange x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpaceKCAdjointRange_bijective_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hrootZeroRange :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagBWAAdjointGraphRootZeroACoeffSpaceKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_rootZeroACoeffSpaceKCAdjointRange_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann hbij hrootZeroRange x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_reducedVerticalCoeffMap_range_bijective_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (hann :
      ∀ (p : SqdiagReducedRootProfile n b d) (A : RootTarget n b c d),
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply
              (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d)
                (sqdiagReducedRootProfileNormalizedPairProductSectionWithLine
                  (n := n) (a := a) (b := b) (c := c) (d := d)
                  hb hc hd L p)).1 = 0)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ
          (sqdiagReducedRootProfileNormalizedRelationSectionWithLine_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root_forall
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ hann)))
    (hverticalCoeffRange :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedPairSectionWithLine_reducedVerticalCoeffMap_range_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ hann hbij hverticalCoeffRange x hx

theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_bijective_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (horth :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hverticalCoeffRange :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hb hc hd L hZ p ∈
          LinearMap.range
            (sqdiagReducedRelationVerticalCoeffMap
              (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij hverticalCoeffRange x hx

set_option synthInstance.maxHeartbeats 500000 in
theorem
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_le_bijective_of_intersectionMaps_range_le
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (L : SqdiagReducedRootProfile n b d →ₗ[F] LineZeroSum n)
    (hroot :
      LinearMap.range
          (sqdiagReducedRootProfileIntersectionSectionRootCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagYWCoeffOfZMatrixSlices (n := n) (c := c)))
    (hcoeff :
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionCoeffWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L) ≤
        LinearMap.range
          (sqdiagKCAdjointRangeEmbed
            (n := n) (a := a) (b := b) (d := d)))
    (horth :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      ∀ p : SqdiagReducedRootProfile n b d,
        sqdiagReducedRootProfileNormalizedRelationSectionWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ p ∈
          sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (hbij :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      Function.Bijective
        (sqdiagReducedRootProfileNormalizedToDefectSectionWithLine
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hb hc hd L hZ horth))
    (hverticalCoeffRange :
      let hZ :=
        sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
      LinearMap.range
          (sqdiagReducedRootProfileNormalizedSectionKCAdjointRangeMapWithLine
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hZ) ≤
        LinearMap.range
          (sqdiagReducedRelationVerticalCoeffMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagReducedRelation n a b c d)
    (hx : x ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let hZ :=
    sqdiagReducedRootProfileNormalizedSectionTargetInZAdjointWithLine_forall_of_intersectionMaps_range_le
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd L hroot hcoeff
  exact
    sqdiagReducedRelationQ_eq_zero_of_verticalOrthogonal_of_normalizedSectionWithLine_reducedVerticalCoeffMap_range_le_bijective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc hd L hZ horth hbij hverticalCoeffRange x hx

set_option synthInstance.maxHeartbeats 800000 in
-- The profile is a nested product of two kernel submodules and a matrix submodule.
theorem finrank_SqdiagReducedRootProfile
    {n b d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagReducedRootProfile n b d) =
      Module.finrank F
          (LinearMap.ker (SquareRootTrace (n := n) (c := d))) +
        Module.finrank F
          (LinearMap.ker (SquareRootTrace (n := n) (c := b))) +
        Module.finrank F (MatrixZeroSum n) := by
  let Kd := LinearMap.ker (SquareRootTrace (n := n) (c := d))
  let Kb := LinearMap.ker (SquareRootTrace (n := n) (c := b))
  haveI : Module.Free F (Kd × Kb) := Module.Free.prod F Kd Kb
  change
    Module.finrank F ((Kd × Kb) × MatrixZeroSum n) =
      Module.finrank F Kd +
        Module.finrank F Kb +
        Module.finrank F (MatrixZeroSum n)
  rw [Module.finrank_prod, Module.finrank_prod]

set_option synthInstance.maxHeartbeats 800000 in
-- Rewriting the same nested product through the matrix-zero-sum dimension is expensive.
theorem finrank_SqdiagReducedRootProfile_with_matrix
    {n b d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagReducedRootProfile n b d) =
      Module.finrank F
          (LinearMap.ker (SquareRootTrace (n := n) (c := d))) +
        Module.finrank F
          (LinearMap.ker (SquareRootTrace (n := n) (c := b))) +
        (n - 1) ^ 2 := by
  rw [finrank_SqdiagReducedRootProfile, finrank_MatrixZeroSum]

set_option synthInstance.maxHeartbeats 800000 in
-- The balanced profile arithmetic reuses the two trace-kernel finrank formulas.
theorem finrank_SqdiagReducedRootProfile_add_profile_core
    {n b d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F (SqdiagReducedRootProfile n b d) +
        n * (n - 1) ^ 2 + (n - 1) ^ 3 =
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b := by
  have hprof :=
    finrank_SqdiagReducedRootProfile_with_matrix
      (n := n) (b := b) (d := d)
  have hdtrace :=
    finrank_ker_SquareRootTrace_add_core (n := n) (c := d) hd
  have hbtrace :=
    finrank_ker_SquareRootTrace_add_core (n := n) (c := b) hb
  have hn : n = (n - 1) + 1 := by
    have hpos : 1 ≤ n := one_le_of_neZero
    omega
  nlinarith

end

end SquareDiagonal
end Core4loop
