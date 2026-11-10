import Core3loop.ProfileEvenSurviving
import Core3loop.ProfileEvenKernel
import Mathlib.LinearAlgebra.BilinearForm.Hom

open scoped BigOperators

namespace Core3loop

set_option maxHeartbeats 1000000 in
-- Chosen-basis sum rearrangements elaborate slowly in the generic tail dimensions.
lemma sum_yz_basis_factor_left
    {a b c n : ℕ} [NeZero n]
    (d : UevenBasisIndexABC a n → UevenBasisIndexABC a n → F)
    (h : YCoord b n → ZCoord c n → UevenBasisIndexABC a n → UevenBasisIndexABC a n → F) :
    (∑ y : YCoord b n, ∑ z : ZCoord c n, ∑ i : UevenBasisIndexABC a n,
        ∑ j : UevenBasisIndexABC a n, d i j * h y z i j) =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
        d i j * (∑ y : YCoord b n, ∑ z : ZCoord c n, h y z i j) := by
  calc
    (∑ y : YCoord b n, ∑ z : ZCoord c n, ∑ i : UevenBasisIndexABC a n,
        ∑ j : UevenBasisIndexABC a n, d i j * h y z i j)
        =
      ∑ y : YCoord b n, ∑ i : UevenBasisIndexABC a n, ∑ z : ZCoord c n,
        ∑ j : UevenBasisIndexABC a n, d i j * h y z i j := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Finset.sum_comm]
    _ =
      ∑ i : UevenBasisIndexABC a n, ∑ y : YCoord b n, ∑ z : ZCoord c n,
        ∑ j : UevenBasisIndexABC a n, d i j * h y z i j := by
          rw [Finset.sum_comm]
    _ =
      ∑ i : UevenBasisIndexABC a n, ∑ y : YCoord b n, ∑ j : UevenBasisIndexABC a n,
        ∑ z : ZCoord c n, d i j * h y z i j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Finset.sum_comm]
    _ =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n, ∑ y : YCoord b n,
        ∑ z : ZCoord c n, d i j * h y z i j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.sum_comm]
    _ =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
        d i j * (∑ y : YCoord b n, ∑ z : ZCoord c n, h y z i j) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          calc
            (∑ y : YCoord b n, ∑ z : ZCoord c n, d i j * h y z i j)
                =
              ∑ y : YCoord b n, d i j * (∑ z : ZCoord c n, h y z i j) := by
                refine Finset.sum_congr rfl ?_
                intro y hy
                rw [Finset.mul_sum]
            _ = d i j * (∑ y : YCoord b n, ∑ z : ZCoord c n, h y z i j) := by
                rw [Finset.mul_sum]

set_option maxHeartbeats 1000000 in
-- This combines two basis-rearranged sums and needs the same elaboration budget.
lemma sum_yz_basis_factor_left_add
    {a b c n : ℕ} [NeZero n]
    (d : UevenBasisIndexABC a n → UevenBasisIndexABC a n → F)
    (h₁ h₂ : YCoord b n → ZCoord c n → UevenBasisIndexABC a n → UevenBasisIndexABC a n → F) :
    ((∑ y : YCoord b n, ∑ z : ZCoord c n, ∑ i : UevenBasisIndexABC a n,
        ∑ j : UevenBasisIndexABC a n, d i j * h₁ y z i j) +
      (∑ y : YCoord b n, ∑ z : ZCoord c n, ∑ i : UevenBasisIndexABC a n,
        ∑ j : UevenBasisIndexABC a n, d i j * h₂ y z i j)) =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
        d i j * ((∑ y : YCoord b n, ∑ z : ZCoord c n, h₁ y z i j) +
          (∑ y : YCoord b n, ∑ z : ZCoord c n, h₂ y z i j)) := by
  rw [sum_yz_basis_factor_left (d := d) (h := h₁),
    sum_yz_basis_factor_left (d := d) (h := h₂)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [mul_add]

set_option maxHeartbeats 1000000 in
-- The t/z variant of the basis rearrangement has the same generic-size cost.
lemma sum_tz_basis_factor_left
    {a c n : ℕ} [NeZero n]
    (d : UevenBasisIndexABC a n → UevenBasisIndexABC a n → F)
    (h : I n → ZCoord c n → UevenBasisIndexABC a n → UevenBasisIndexABC a n → F) :
    (∑ t : I n, ∑ z : ZCoord c n, ∑ i : UevenBasisIndexABC a n,
        ∑ j : UevenBasisIndexABC a n, d i j * h t z i j) =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
        d i j * (∑ t : I n, ∑ z : ZCoord c n, h t z i j) := by
  calc
    (∑ t : I n, ∑ z : ZCoord c n, ∑ i : UevenBasisIndexABC a n,
        ∑ j : UevenBasisIndexABC a n, d i j * h t z i j)
        =
      ∑ t : I n, ∑ i : UevenBasisIndexABC a n, ∑ z : ZCoord c n,
        ∑ j : UevenBasisIndexABC a n, d i j * h t z i j := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [Finset.sum_comm]
    _ =
      ∑ i : UevenBasisIndexABC a n, ∑ t : I n, ∑ z : ZCoord c n,
        ∑ j : UevenBasisIndexABC a n, d i j * h t z i j := by
          rw [Finset.sum_comm]
    _ =
      ∑ i : UevenBasisIndexABC a n, ∑ t : I n, ∑ j : UevenBasisIndexABC a n,
        ∑ z : ZCoord c n, d i j * h t z i j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [Finset.sum_comm]
    _ =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n, ∑ t : I n,
        ∑ z : ZCoord c n, d i j * h t z i j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.sum_comm]
    _ =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
        d i j * (∑ t : I n, ∑ z : ZCoord c n, h t z i j) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          calc
            (∑ t : I n, ∑ z : ZCoord c n, d i j * h t z i j)
                =
              ∑ t : I n, d i j * (∑ z : ZCoord c n, h t z i j) := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                rw [Finset.mul_sum]
            _ = d i j * (∑ t : I n, ∑ z : ZCoord c n, h t z i j) := by
                rw [Finset.mul_sum]

noncomputable def dotUevenForm {a n : ℕ} [NeZero n] :
    LinearMap.BilinForm F (Ueven (a := a) (n := n)) where
  toFun x :=
    { toFun := fun y => dotProfile (a := a) (n := n) x.1 y.1
      map_add' := by
        intro y z
        exact dot_add_right (a := a) (n := n) x.1 y.1 z.1
      map_smul' := by
        intro c y
        simpa [smul_eq_mul, mul_comm] using
          dot_smul_right (a := a) (n := n) x.1 y.1 c }
  map_add' := by
    intro x y
    ext z
    exact dot_add_left (a := a) (n := n) x.1 y.1 z.1
  map_smul' := by
    intro c x
    ext z
    simpa [smul_eq_mul] using
      dot_smul_left (a := a) (n := n) c x.1 z.1

set_option maxHeartbeats 1000000 in
-- Bilinear expansion through an arbitrary chosen basis is elaboration-heavy.
lemma dotProfile_uEven_eq_sum_basis {a n : ℕ} [NeZero n]
    (x y : Ueven (a := a) (n := n)) :
    dotProfile (a := a) (n := n) x.1 y.1 =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
        ((uevenBasisABC (a := a) (n := n)).equivFun x i) *
        ((uevenBasisABC (a := a) (n := n)).equivFun y j) *
          dotProfile (a := a) (n := n)
            (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
            (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) := by
  calc
    dotProfile (a := a) (n := n) x.1 y.1
      = dotUevenForm (a := a) (n := n) x y := by
          rfl
    _ = ((uevenBasisABC (a := a) (n := n)).repr x).sum
        (fun i xi =>
          ((uevenBasisABC (a := a) (n := n)).repr y).sum
            (fun j yj =>
              xi • yj •
                dotUevenForm (a := a) (n := n)
                  ((uevenBasisABC (a := a) (n := n)) i)
                  ((uevenBasisABC (a := a) (n := n)) j))) := by
        symm
        exact LinearMap.BilinForm.sum_repr_mul_repr_mul
            (b := uevenBasisABC (a := a) (n := n))
            (B := dotUevenForm (a := a) (n := n)) x y
    _ =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
        ((uevenBasisABC (a := a) (n := n)).equivFun x i) *
          ((uevenBasisABC (a := a) (n := n)).equivFun y j) *
          dotProfile (a := a) (n := n)
            (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
            (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) := by
        rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
        simp [dotUevenForm, smul_eq_mul, mul_assoc]

set_option maxHeartbeats 1000000 in
-- Expanding qProfile into basis coordinates nests four finite sums.
lemma qProfileABC_evenTailOfModel_eq_sum_qScalar_coords
    {a b c n : ℕ} [NeZero n]
    (XB : EvenTailBModelABC a c n) (YC : EvenTailCModelABC a b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n)
      (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB)
      (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC) =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
        dotProfile (a := a) (n := n)
          (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
          (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) *
          qScalar (b := b) (c := c) (n := n)
            (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i)
            (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j) := by
  unfold qProfileABC qLeftProfileABC qRightProfileABC
  calc
    (∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n)
          (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB (sumY y) z)
          (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y (sumZ z))) +
      (∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n)
          (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB (sumY y + 1) z)
          (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y (sumZ z + 1)))
      =
      (∑ y : YCoord b n, ∑ z : ZCoord c n,
        ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
          ((uevenBasisABC (a := a) (n := n)).equivFun (XB (sumY y) z) i) *
            ((uevenBasisABC (a := a) (n := n)).equivFun (YC y (sumZ z)) j) *
            dotProfile (a := a) (n := n)
              (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
              (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1)) +
      (∑ y : YCoord b n, ∑ z : ZCoord c n,
        ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
          ((uevenBasisABC (a := a) (n := n)).equivFun (XB (sumY y + 1) z) i) *
            ((uevenBasisABC (a := a) (n := n)).equivFun (YC y (sumZ z + 1)) j) *
            dotProfile (a := a) (n := n)
              (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
              (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1)) := by
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro z hz
          simpa using
            (dotProfile_uEven_eq_sum_basis (a := a) (n := n) (XB (sumY y) z) (YC y (sumZ z)))
        · refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro z hz
          simpa using
            (dotProfile_uEven_eq_sum_basis (a := a) (n := n) (XB (sumY y + 1) z) (YC y (sumZ z + 1)))
    _ =
        ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
          dotProfile (a := a) (n := n)
            (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
            (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) *
          ((∑ y : YCoord b n, ∑ z : ZCoord c n,
              (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i) (sumY y) z *
                (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j) y (sumZ z)) +
            (∑ y : YCoord b n, ∑ z : ZCoord c n,
              (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i) (sumY y + 1) z *
                (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j) y (sumZ z + 1))) := by
        have hmul1 :
            ∀ y : YCoord b n, ∀ z : ZCoord c n,
              ∀ i : UevenBasisIndexABC a n, ∀ j : UevenBasisIndexABC a n,
                ((uevenBasisABC (a := a) (n := n)).equivFun (XB (sumY y) z) i) *
                    ((uevenBasisABC (a := a) (n := n)).equivFun (YC y (sumZ z)) j) *
                      dotProfile (a := a) (n := n)
                        (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                        (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) =
                  dotProfile (a := a) (n := n)
                      (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                      (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) *
                    ((evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i) (sumY y) z *
                      (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j) y
                        (sumZ z)) := by
          intro y z i j
          change
            ((uevenBasisABC (a := a) (n := n)).equivFun (XB (sumY y) z) i) *
                ((uevenBasisABC (a := a) (n := n)).equivFun (YC y (sumZ z)) j) *
                  dotProfile (a := a) (n := n)
                    (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                    (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) =
              dotProfile (a := a) (n := n)
                  (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                  (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) *
                (((uevenBasisABC (a := a) (n := n)).equivFun (XB (sumY y) z) i) *
                  ((uevenBasisABC (a := a) (n := n)).equivFun (YC y (sumZ z)) j))
          ring
        have hmul2 :
            ∀ y : YCoord b n, ∀ z : ZCoord c n,
              ∀ i : UevenBasisIndexABC a n, ∀ j : UevenBasisIndexABC a n,
                ((uevenBasisABC (a := a) (n := n)).equivFun (XB (sumY y + 1) z) i) *
                    ((uevenBasisABC (a := a) (n := n)).equivFun (YC y (sumZ z + 1)) j) *
                      dotProfile (a := a) (n := n)
                        (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                        (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) =
                  dotProfile (a := a) (n := n)
                      (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                      (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) *
                    ((evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i) (sumY y + 1) z *
                      (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j) y
                        (sumZ z + 1)) := by
          intro y z i j
          change
            ((uevenBasisABC (a := a) (n := n)).equivFun (XB (sumY y + 1) z) i) *
                ((uevenBasisABC (a := a) (n := n)).equivFun (YC y (sumZ z + 1)) j) *
                  dotProfile (a := a) (n := n)
                    (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                    (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) =
              dotProfile (a := a) (n := n)
                  (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                  (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) *
                (((uevenBasisABC (a := a) (n := n)).equivFun (XB (sumY y + 1) z) i) *
                  ((uevenBasisABC (a := a) (n := n)).equivFun (YC y (sumZ z + 1)) j))
          ring
        let d : UevenBasisIndexABC a n → UevenBasisIndexABC a n → F := fun i j =>
          dotProfile (a := a) (n := n)
            (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
            (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1)
        let h₁ :
            YCoord b n → ZCoord c n → UevenBasisIndexABC a n → UevenBasisIndexABC a n → F :=
          fun y z i j =>
            (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i) (sumY y) z *
              (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j) y (sumZ z)
        let h₂ :
            YCoord b n → ZCoord c n → UevenBasisIndexABC a n → UevenBasisIndexABC a n → F :=
          fun y z i j =>
            (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i) (sumY y + 1) z *
              (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j) y (sumZ z + 1)
        calc
          ((∑ y : YCoord b n, ∑ z : ZCoord c n,
              ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
                ((uevenBasisABC (a := a) (n := n)).equivFun (XB (sumY y) z) i) *
                  ((uevenBasisABC (a := a) (n := n)).equivFun (YC y (sumZ z)) j) *
                  dotProfile (a := a) (n := n)
                    (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                    (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1)) +
            (∑ y : YCoord b n, ∑ z : ZCoord c n,
              ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
                ((uevenBasisABC (a := a) (n := n)).equivFun (XB (sumY y + 1) z) i) *
                  ((uevenBasisABC (a := a) (n := n)).equivFun (YC y (sumZ z + 1)) j) *
                  dotProfile (a := a) (n := n)
                    (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                    (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1)))
            =
              (∑ y : YCoord b n, ∑ z : ZCoord c n,
                ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
                  d i j * h₁ y z i j) +
              (∑ y : YCoord b n, ∑ z : ZCoord c n,
                ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
                  d i j * h₂ y z i j) := by
            simp_rw [d, h₁, h₂, hmul1, hmul2]
          _ =
              ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
                d i j * ((∑ y : YCoord b n, ∑ z : ZCoord c n, h₁ y z i j) +
                  (∑ y : YCoord b n, ∑ z : ZCoord c n, h₂ y z i j)) := by
            exact sum_yz_basis_factor_left_add (a := a) (b := b) (c := c) (n := n)
              (d := d) (h₁ := h₁) (h₂ := h₂)
          _ =
              ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
                dotProfile (a := a) (n := n)
                  (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
                  (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) *
                  ((∑ y : YCoord b n, ∑ z : ZCoord c n,
                      (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i) (sumY y) z *
                        (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j) y (sumZ z)) +
                    (∑ y : YCoord b n, ∑ z : ZCoord c n,
                      (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i) (sumY y + 1) z *
                        (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j) y (sumZ z + 1))) := by
            simp [d, h₁, h₂]
    _ =
        ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
          dotProfile (a := a) (n := n)
            (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
            (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) *
          qScalar (b := b) (c := c) (n := n)
            (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i)
            (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        refine Finset.sum_congr rfl ?_
        intro j hj
        congr 1
        rw [qScalar, qLeftScalar_eq_sum_yz (b := b) (c := c) (n := n)
              (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i)
              (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j),
            qRightScalar_eq_sum_yz (b := b) (c := c) (n := n)
              (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i)
              (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j)]

set_option maxHeartbeats 4000000 in
-- The pair model expansion repeats the arbitrary-basis bilinear calculation.
lemma evenTailPairModelABC_eq_sum_bPair_coords
    {a c n : ℕ} [NeZero n]
    (XB ZB : EvenTailBModelABC a c n) :
    evenTailPairModelABC (a := a) (c := c) (n := n) XB ZB =
      ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
        dotProfile (a := a) (n := n)
          (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
          (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1) *
          bPairScalar (c := c) (n := n)
            (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i)
            (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) ZB j) := by
  unfold evenTailPairModelABC bPairScalar
  let d : UevenBasisIndexABC a n → UevenBasisIndexABC a n → F := fun i j =>
    dotProfile (a := a) (n := n)
      (((uevenBasisABC (a := a) (n := n)) i : Ueven (a := a) (n := n)).1)
      (((uevenBasisABC (a := a) (n := n)) j : Ueven (a := a) (n := n)).1)
  let h :
      I n → ZCoord c n → UevenBasisIndexABC a n → UevenBasisIndexABC a n → F :=
    fun t z i j =>
      (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i) t z *
        (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) ZB j) t z
  calc
    ∑ t : I n, ∑ z : ZCoord c n,
      dotProfile (a := a) (n := n) (XB t z).1 (ZB t z).1
      =
        ∑ t : I n, ∑ z : ZCoord c n,
          ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
            d i j * h t z i j := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              refine Finset.sum_congr rfl ?_
              intro z hz
              have hsum := dotProfile_uEven_eq_sum_basis (a := a) (n := n) (XB t z) (ZB t z)
              calc
                dotProfile (a := a) (n := n) (XB t z).1 (ZB t z).1 =
                    ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
                      ((uevenBasisABC (a := a) (n := n)).equivFun (XB t z) i) *
                        ((uevenBasisABC (a := a) (n := n)).equivFun (ZB t z) j) *
                        dotProfile (a := a) (n := n)
                          (((uevenBasisABC (a := a) (n := n)) i :
                              Ueven (a := a) (n := n)).1)
                          (((uevenBasisABC (a := a) (n := n)) j :
                              Ueven (a := a) (n := n)).1) := by
                          exact hsum
                _ = ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
                      d i j * h t z i j := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      simp [d, h, evenTailBModelEquivCoordABC]
                      ring
    _ =
        ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
          d i j * (∑ t : I n, ∑ z : ZCoord c n, h t z i j) := by
              rw [sum_tz_basis_factor_left (a := a) (c := c) (n := n) (d := d) (h := h)]
    _ =
        ∑ i : UevenBasisIndexABC a n, ∑ j : UevenBasisIndexABC a n,
          d i j *
            bPairScalar (c := c) (n := n)
              (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i)
              (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) ZB j) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              rfl

lemma qProfileABC_evenTailOfModel_eq_evenTailPairModel_evenTailTModel
    {a b c n : ℕ} [NeZero n]
    (XB : EvenTailBModelABC a c n) (YC : EvenTailCModelABC a b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n)
      (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB)
      (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC) =
      evenTailPairModelABC (a := a) (c := c) (n := n) XB
        (evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC) := by
  rw [qProfileABC_evenTailOfModel_eq_sum_qScalar_coords (a := a) (b := b) (c := c) (n := n) XB YC]
  rw [evenTailPairModelABC_eq_sum_bPair_coords (a := a) (c := c) (n := n) XB
    (evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [qScalar_eq_bPair_TScalar (b := b) (c := c) (n := n)
    (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i)
    (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC j)]
  rw [evenTailTModelABC_coord_apply (a := a) (b := b) (c := c) (n := n) YC j]

lemma evenTailSignABC_eq_evenTailSignModelABC
    {a b c n : ℕ} [NeZero n]
    (XB : EvenTailBModelABC a c n) (YC : EvenTailCModelABC a b n) :
    evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC =
      evenTailSignModelABC (a := a) (b := b) (c := c) (n := n) XB YC := by
  unfold evenTailSignABC evenTailSignModelABC
  rw [qProfileABC_evenTailOfModel_eq_evenTailPairModel_evenTailTModel
    (a := a) (b := b) (c := c) (n := n) XB YC]

theorem sum_evenTailSignABC_eq_sum_evenTailSignModelABC
    {a b c n : ℕ} [NeZero n] :
    (∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
      evenTailSignABC (a := a) (b := b) (c := c) (n := n) XB YC) =
    (∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
      evenTailSignModelABC (a := a) (b := b) (c := c) (n := n) XB YC) := by
  refine Finset.sum_congr rfl ?_
  intro YC hYC
  refine Finset.sum_congr rfl ?_
  intro XB hXB
  exact evenTailSignABC_eq_evenTailSignModelABC (a := a) (b := b) (c := c) (n := n) XB YC

end Core3loop
