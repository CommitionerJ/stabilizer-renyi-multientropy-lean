import Core4loop.TriangleLeaf.E6Q1CoeffCore
import Core4loop.TriangleLeaf.BOnlyBDiagCore

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Neutral ambient coefficient pairing for the TriangleLeaf E6 route.

This module contains only the neutral B-diagonal restriction, the finite
coordinate pairing, and the resulting range/finrank bridge.  It makes no
numerical rank calculation.
-/

noncomputable def triangleLeafCFun4LinearEquiv (n a b d : ℕ) :
    CFun4 n a b d ≃ₗ[F]
      (PVec n a × YVec n b × I n × WVec n d → F) where
  toEquiv := cFun4Equiv n a b d
  map_add' C D := by
    funext u
    rcases u with ⟨p, y, sz, w⟩
    rfl
  map_smul' r C := by
    funext u
    rcases u with ⟨p, y, sz, w⟩
    rfl

private theorem exists_coeffApply_of_linearMap
    {ι : Type*} [Fintype ι]
    (M : (ι → F) →ₗ[F] F) :
    ∃ c : ι → F, ∀ f : ι → F, coeffApply c f = M f := by
  classical
  let e : ι → ι → F := fun i j => if j = i then 1 else 0
  refine ⟨fun i => M (e i), ?_⟩
  intro f
  have hdecomp : f = ∑ i : ι, f i • e i := by
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp [e]
    · intro i _ hij
      simp [e, hij.symm]
    · simp
  calc
    coeffApply (fun i => M (e i)) f
        = ∑ i : ι, f i * M (e i) := by
          unfold coeffApply
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ = M (∑ i : ι, f i • e i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [smul_eq_mul]
    _ = M f := by rw [← hdecomp]

private theorem coeffApply_comm
    {ι : Type*} [Fintype ι] (f g : ι → F) :
    coeffApply f g = coeffApply g f := by
  unfold coeffApply
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

private noncomputable def triangleLeafFunDotDual
    {ι : Type*} [Fintype ι] :
    (ι → F) →ₗ[F] Module.Dual F (ι → F) where
  toFun c :=
    { toFun := fun f => coeffApply c f
      map_add' := by
        intro f g
        unfold coeffApply
        simp only [Pi.add_apply]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro x f
        unfold coeffApply
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  map_add' c d := by
    apply LinearMap.ext
    intro f
    change (∑ i : ι, f i * (c i + d i)) =
      (∑ i : ι, f i * c i) + ∑ i : ι, f i * d i
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' x c := by
    apply LinearMap.ext
    intro f
    change (∑ i : ι, f i * (x * c i)) =
      x * ∑ i : ι, f i * c i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

noncomputable def triangleLeafCFunDotDual
    {n a b d : ℕ} [NeZero n] :
    CFun4 n a b d →ₗ[F] Module.Dual F (CFun4 n a b d) := by
  let E :=
    triangleLeafCFun4LinearEquiv n a b d
  exact E.toLinearMap.dualMap.comp
    ((triangleLeafFunDotDual
      (ι := PVec n a × YVec n b × I n × WVec n d)).comp
      E.toLinearMap)

@[simp]
theorem triangleLeafCFunDotDual_apply
    {n a b d : ℕ} [NeZero n]
    (C D : CFun4 n a b d) :
    triangleLeafCFunDotDual
        (n := n) (a := a) (b := b) (d := d) C D =
      coeffApply
        (cFun4Equiv n a b d C)
        (cFun4Equiv n a b d D) := by
  rfl

theorem triangleLeafCFunDotDual_surjective
    {n a b d : ℕ} [NeZero n] :
    Function.Surjective
      (triangleLeafCFunDotDual
        (n := n) (a := a) (b := b) (d := d)) := by
  intro L
  let E :=
    triangleLeafCFun4LinearEquiv n a b d
  let Lflat :
      Module.Dual F
        (PVec n a × YVec n b × I n × WVec n d → F) :=
    L.comp E.symm.toLinearMap
  rcases exists_coeffApply_of_linearMap Lflat with ⟨c, hc⟩
  refine ⟨E.symm c, ?_⟩
  apply LinearMap.ext
  intro D
  change coeffApply (E (E.symm c)) (E D) = L D
  rw [E.apply_symm_apply, hc]
  rfl

noncomputable def triangleLeafBDiagAlpha
    {n a b d : ℕ} [NeZero n] :
    CFun4 n a b d →ₗ[F] Module.Dual F (BDiagCoeff n a d) :=
  (BDiagEmbed
    (n := n) (a := a) (b := b) (d := d)).dualMap.comp
      (triangleLeafCFunDotDual
        (n := n) (a := a) (b := b) (d := d))

@[simp]
theorem triangleLeafBDiagAlpha_apply
    {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (U : BDiagCoeff n a d) :
    triangleLeafBDiagAlpha
        (n := n) (a := a) (b := b) (d := d) C U =
      coeffApply
        (cFun4Equiv n a b d
          (BDiagEmbed
            (n := n) (a := a) (b := b) (d := d) U))
        (cFun4Equiv n a b d C) := by
  change
    coeffApply
        (cFun4Equiv n a b d C)
        (cFun4Equiv n a b d
          (BDiagEmbed
            (n := n) (a := a) (b := b) (d := d) U)) =
      _
  exact coeffApply_comm _ _

noncomputable def triangleLeafBOnlyBDiagDualRestrict
    {n a b c d : ℕ} [NeZero n] :
    Module.Dual F (BDiagCoeff n a d) →ₗ[F]
      Module.Dual F (triangleLeafBOnly n a b c d) :=
  (triangleLeafBOnlyBDiagMap
    (n := n) (a := a) (b := b) (c := c) (d := d)).dualMap

theorem triangleLeafBDiagAlpha_surjective
    {n a b d : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Surjective
      (triangleLeafBDiagAlpha
        (n := n) (a := a) (b := b) (d := d)) := by
  intro ell
  rcases
      LinearMap.dualMap_surjective_of_injective
        (BDiagEmbed_injective
          (n := n) (a := a) (b := b) (d := d) hb) ell with
    ⟨phi, hphi⟩
  rcases
      triangleLeafCFunDotDual_surjective
        (n := n) (a := a) (b := b) (d := d) phi with
    ⟨C, hC⟩
  refine ⟨C, ?_⟩
  change
    (BDiagEmbed
      (n := n) (a := a) (b := b) (d := d)).dualMap
        (triangleLeafCFunDotDual
          (n := n) (a := a) (b := b) (d := d) C) = ell
  rw [hC, hphi]

theorem triangleLeafBDiagEmbed_BDiagOfB_apply
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d)
    (p : PVec n a) (y : YVec n b) (sz : I n) (w : WVec n d) :
    BDiagEmbed (n := n) (a := a) (b := b) (d := d)
        (BDiagOfB (n := n) (a := a) (c := c) (d := d) B) p y sz w =
      (∑ z : ZVec n c,
          if vecSum z = sz then B p (vecSum y) z w else 0) +
        ∑ z : ZVec n c,
          if vecSum z + 1 = sz then B p (vecSum y + 1) z w else 0 := by
  classical
  unfold BDiagEmbed BDiagOfB
  change
    ((∑ z : ZVec n c,
        if vecSum z = vecSum y + sz - vecSum y then
          B p (vecSum y) z w
        else 0) +
      ∑ z : ZVec n c,
        if vecSum z = vecSum y + sz - (vecSum y + 1) then
          B p (vecSum y + 1) z w
        else 0) =
      (∑ z : ZVec n c,
        if vecSum z = sz then B p (vecSum y) z w else 0) +
      ∑ z : ZVec n c,
        if vecSum z + 1 = sz then B p (vecSum y + 1) z w else 0
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro z _
    have hcoord : vecSum y + sz - vecSum y = sz := by abel
    rw [hcoord]
  · refine Finset.sum_congr rfl ?_
    intro z _
    have hiff :
        vecSum z = vecSum y + sz - (vecSum y + 1) ↔
          vecSum z + 1 = sz := by
      constructor
      · intro h
        rw [h]
        abel
      · intro h
        rw [← h]
        abel
    exact if_congr hiff rfl rfl

theorem triangleLeafBDiagAlpha_BDiagOfB_eq_Q1
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) :
    triangleLeafBDiagAlpha
        (n := n) (a := a) (b := b) (d := d) C
        (BDiagOfB (n := n) (a := a) (c := c) (d := d) B) =
      Q1 B C := by
  classical
  rw [triangleLeafBDiagAlpha_apply]
  unfold coeffApply Q1 betaB gammaB deltaC etaC cFun4Equiv
  simp only
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : I n, ∑ w : WVec n d,
        C p y x w *
          BDiagEmbed (n := n) (a := a) (b := b) (d := d)
            (BDiagOfB (n := n) (a := a) (c := c) (d := d) B) p y x w)
        =
        ∑ x : I n, ∑ w : WVec n d,
          C p y x w *
            ((∑ z : ZVec n c,
                if vecSum z = x then B p (vecSum y) z w else 0) +
              ∑ z : ZVec n c,
                if vecSum z + 1 = x then
                  B p (vecSum y + 1) z w
                else 0) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          refine Finset.sum_congr rfl ?_
          intro w _
          rw [triangleLeafBDiagEmbed_BDiagOfB_apply]
    _ =
        ∑ w : WVec n d, ∑ x : I n,
          C p y x w *
            ((∑ z : ZVec n c,
                if vecSum z = x then B p (vecSum y) z w else 0) +
              ∑ z : ZVec n c,
                if vecSum z + 1 = x then
                  B p (vecSum y + 1) z w
                else 0) := by
          exact Finset.sum_comm
    _ = ∑ w : WVec n d, ∑ z : ZVec n c,
        (B p (vecSum y) z w * C p y (vecSum z) w +
          B p (vecSum y + 1) z w * C p y (vecSum z + 1) w) := by
          refine Finset.sum_congr rfl ?_
          intro w _
          calc
            (∑ x : I n,
                C p y x w *
                  ((∑ z : ZVec n c,
                      if vecSum z = x then B p (vecSum y) z w else 0) +
                    ∑ z : ZVec n c,
                      if vecSum z + 1 = x then
                        B p (vecSum y + 1) z w
                      else 0))
                =
                (∑ x : I n,
                    C p y x w *
                      ∑ z : ZVec n c,
                        if vecSum z = x then B p (vecSum y) z w else 0) +
                  ∑ x : I n,
                    C p y x w *
                      ∑ z : ZVec n c,
                        if vecSum z + 1 = x then
                          B p (vecSum y + 1) z w
                        else 0 := by
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl ?_
                  intro x _
                  ring
            _ =
                (∑ z : ZVec n c,
                    C p y (vecSum z) w * B p (vecSum y) z w) +
                  ∑ z : ZVec n c,
                    C p y (vecSum z + 1) w * B p (vecSum y + 1) z w := by
                  congr 1
                  · calc
                      (∑ x : I n,
                          C p y x w *
                            ∑ z : ZVec n c,
                              if vecSum z = x then B p (vecSum y) z w else 0)
                          =
                          ∑ x : I n, ∑ z : ZVec n c,
                            C p y x w *
                              (if vecSum z = x then
                                B p (vecSum y) z w
                              else 0) := by
                            refine Finset.sum_congr rfl ?_
                            intro x _
                            rw [Finset.mul_sum]
                      _ = ∑ z : ZVec n c, ∑ x : I n,
                            C p y x w *
                              (if vecSum z = x then
                                B p (vecSum y) z w
                              else 0) := by
                            exact Finset.sum_comm
                      _ = ∑ z : ZVec n c,
                          C p y (vecSum z) w * B p (vecSum y) z w := by
                            refine Finset.sum_congr rfl ?_
                            intro z _
                            rw [Finset.sum_eq_single (vecSum z)]
                            · simp
                            · intro x _ hx
                              simp [hx.symm]
                            · simp
                  · calc
                      (∑ x : I n,
                          C p y x w *
                            ∑ z : ZVec n c,
                              if vecSum z + 1 = x then
                                B p (vecSum y + 1) z w
                              else 0)
                          =
                          ∑ x : I n, ∑ z : ZVec n c,
                            C p y x w *
                              (if vecSum z + 1 = x then
                                B p (vecSum y + 1) z w
                              else 0) := by
                            refine Finset.sum_congr rfl ?_
                            intro x _
                            rw [Finset.mul_sum]
                      _ = ∑ z : ZVec n c, ∑ x : I n,
                            C p y x w *
                              (if vecSum z + 1 = x then
                                B p (vecSum y + 1) z w
                              else 0) := by
                            exact Finset.sum_comm
                      _ = ∑ z : ZVec n c,
                          C p y (vecSum z + 1) w *
                            B p (vecSum y + 1) z w := by
                            refine Finset.sum_congr rfl ?_
                            intro z _
                            rw [Finset.sum_eq_single (vecSum z + 1)]
                            · simp
                            · intro x _ hx
                              simp [hx.symm]
                            · simp
            _ = ∑ z : ZVec n c,
                (B p (vecSum y) z w * C p y (vecSum z) w +
                  B p (vecSum y + 1) z w *
                    C p y (vecSum z + 1) w) := by
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl ?_
                  intro z _
                  ring
    _ = ∑ z : ZVec n c, ∑ w : WVec n d,
        (B p (vecSum y) z w * C p y (vecSum z) w +
          B p (vecSum y + 1) z w * C p y (vecSum z + 1) w) := by
          exact Finset.sum_comm

theorem triangleLeafBDiagAlpha_BOnly_eq_Q1
    {n a b c d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (Y : triangleLeafBOnly n a b c d) :
    triangleLeafBDiagAlpha
        (n := n) (a := a) (b := b) (d := d) C
        (triangleLeafBOnlyBDiagMap
          (n := n) (a := a) (b := b) (c := c) (d := d) Y) =
      Q1 Y.1.1.1 C := by
  rw [triangleLeafBOnlyBDiagMap_apply]
  exact triangleLeafBDiagAlpha_BDiagOfB_eq_Q1 Y.1.1.1 C

theorem triangleLeafQ1BOnlyCoeffAll_eq_dualRestrict_comp_alpha
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafQ1BOnlyCoeffAll
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (triangleLeafBOnlyBDiagDualRestrict
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (triangleLeafBDiagAlpha
          (n := n) (a := a) (b := b) (d := d)) := by
  apply LinearMap.ext
  intro C
  apply LinearMap.ext
  intro Y
  change
    Q1 Y.1.1.1 C =
      triangleLeafBDiagAlpha
        (n := n) (a := a) (b := b) (d := d) C
        (triangleLeafBOnlyBDiagMap
          (n := n) (a := a) (b := b) (c := c) (d := d) Y)
  rw [triangleLeafBDiagAlpha_BOnly_eq_Q1]

theorem range_triangleLeafQ1BOnlyCoeffAll_eq_dualRestrict
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    LinearMap.range
        (triangleLeafQ1BOnlyCoeffAll
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      LinearMap.range
        (triangleLeafBOnlyBDiagDualRestrict
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [triangleLeafQ1BOnlyCoeffAll_eq_dualRestrict_comp_alpha]
  exact
    LinearMap.range_comp_of_range_eq_top
      (triangleLeafBOnlyBDiagDualRestrict
        (n := n) (a := a) (b := b) (c := c) (d := d))
      (LinearMap.range_eq_top.mpr
        (triangleLeafBDiagAlpha_surjective
          (n := n) (a := a) (b := b) (d := d) hb))

set_option synthInstance.maxHeartbeats 1000000 in
-- Nested dual-map range subtypes require additional typeclass normalization.
theorem finrank_range_triangleLeafQ1BOnlyCoeffAll_eq_BDiagMap
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafQ1BOnlyCoeffAll
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.range
          (triangleLeafBOnlyBDiagMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  rw [range_triangleLeafQ1BOnlyCoeffAll_eq_dualRestrict hb]
  change
    Module.finrank F
        (LinearMap.range
          (triangleLeafBOnlyBDiagMap
            (n := n) (a := a) (b := b) (c := c) (d := d)).dualMap) =
      Module.finrank F
        (LinearMap.range
          (triangleLeafBOnlyBDiagMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
  exact
    LinearMap.finrank_range_dualMap_eq_finrank_range
      (triangleLeafBOnlyBDiagMap
        (n := n) (a := a) (b := b) (c := c) (d := d))

end

end TriangleLeaf
end Core4loop
