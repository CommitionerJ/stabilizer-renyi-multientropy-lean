import Core4loop.SquareDiagonal.SurvivorBWClassify

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable def sqdiagRootCoeffApply {n b c d : ℕ} [NeZero n]
    (A R : RootTarget n b c d) : F :=
  ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
    R y z w * A y z w

noncomputable def sqdiagRootCoeffLinearMap {n b c d : ℕ} [NeZero n]
    (R : RootTarget n b c d) : RootTarget n b c d →ₗ[F] F where
  toFun A := sqdiagRootCoeffApply A R
  map_add' A A' := by
    unfold sqdiagRootCoeffApply
    simp only [Pi.add_apply]
    calc
      (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
          R y z w * (A y z w + A' y z w))
        =
          ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            (R y z w * A y z w + R y z w * A' y z w) := by
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro z _
            refine Finset.sum_congr rfl ?_
            intro w _
            ring
      _ =
          ∑ y : YVec n b, ∑ z : ZVec n c,
            ((∑ w : WVec n d, R y z w * A y z w) +
              ∑ w : WVec n d, R y z w * A' y z w) := by
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro z _
            rw [Finset.sum_add_distrib]
      _ =
          ∑ y : YVec n b,
            ((∑ z : ZVec n c, ∑ w : WVec n d, R y z w * A y z w) +
              ∑ z : ZVec n c, ∑ w : WVec n d, R y z w * A' y z w) := by
            refine Finset.sum_congr rfl ?_
            intro y _
            rw [Finset.sum_add_distrib]
      _ =
          (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            R y z w * A y z w) +
          ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            R y z w * A' y z w := by
            rw [Finset.sum_add_distrib]
  map_smul' r A := by
    unfold sqdiagRootCoeffApply
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
          R y z w * (r * A y z w))
        =
          ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            (r * (R y z w * A y z w)) := by
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro z _
            refine Finset.sum_congr rfl ?_
            intro w _
            ring
      _ =
          r * (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            R y z w * A y z w) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro y _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro z _
            rw [Finset.mul_sum]

@[simp]
theorem sqdiagRootCoeffLinearMap_apply
    {n b c d : ℕ} [NeZero n]
    (R A : RootTarget n b c d) :
    sqdiagRootCoeffLinearMap (n := n) (b := b) (c := c) (d := d) R A =
      sqdiagRootCoeffApply A R := rfl

noncomputable def sqdiagKCAdjointCoeff {n a b c d : ℕ} [NeZero n]
    (A : RootTarget n b c d) : CFun4 n a b d :=
  fun _p y sz w =>
    (∑ z : ZVec n c, if vecSum z = sz then A y z w else 0)
      + ∑ z : ZVec n c, if vecSum z + 1 = sz then A y z w else 0

noncomputable def sqdiagKCAdjointMap {n a b c d : ℕ} [NeZero n] :
    RootTarget n b c d →ₗ[F] CFun4 n a b d where
  toFun A :=
    sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A
  map_add' A A' := by
    funext p y sz w
    unfold sqdiagKCAdjointCoeff
    have h1 :
        (∑ z : ZVec n c, if vecSum z = sz then (A + A') y z w else 0) =
          (∑ z : ZVec n c, if vecSum z = sz then A y z w else 0) +
            ∑ z : ZVec n c, if vecSum z = sz then A' y z w else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : vecSum z = sz <;> simp [hz]
    have h2 :
        (∑ z : ZVec n c, if vecSum z + 1 = sz then (A + A') y z w else 0) =
          (∑ z : ZVec n c, if 1 + vecSum z = sz then A y z w else 0) +
            ∑ z : ZVec n c, if 1 + vecSum z = sz then A' y z w else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : vecSum z + 1 = sz
      · have hz' : 1 + vecSum z = sz := by
          rwa [add_comm]
        simp [hz, hz']
      · have hz' : 1 + vecSum z ≠ sz := by
          intro h
          exact hz (by rwa [add_comm] at h)
        simp [hz, hz']
    rw [h1, h2]
    simp only [Pi.add_apply]
    abel_nf
  map_smul' r A := by
    funext p y sz w
    unfold sqdiagKCAdjointCoeff
    have h1 :
        (∑ z : ZVec n c, if vecSum z = sz then (r • A) y z w else 0) =
          r * ∑ z : ZVec n c, if vecSum z = sz then A y z w else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : vecSum z = sz <;> simp [hz, smul_eq_mul]
    have h2 :
        (∑ z : ZVec n c, if vecSum z + 1 = sz then (r • A) y z w else 0) =
          r * ∑ z : ZVec n c, if vecSum z + 1 = sz then A y z w else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : vecSum z + 1 = sz <;> simp [hz, smul_eq_mul]
    rw [h1, h2]
    simp [smul_eq_mul, mul_add]

@[simp]
theorem sqdiagKCAdjointMap_apply
    {n a b c d : ℕ} [NeZero n] (A : RootTarget n b c d) :
    sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d) A =
      sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A :=
  rfl

noncomputable instance instFintypeKerSqdiagKCAdjointMap
    {n a b c d : ℕ} [NeZero n] :
    Fintype
      (LinearMap.ker
        (sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  classical
  infer_instance

theorem sqdiag_coeffApply_KCAdjointCoeff_eq_rootCoeffApply_KCMap
    {n a b c d : ℕ} [NeZero n]
    (A : RootTarget n b c d) (C : CFun4 n a b d) :
    coeffApply
        (cFun4Equiv n a b d
          (sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A))
        (cFun4Equiv n a b d C)
      =
    sqdiagRootCoeffApply A
      (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) := by
  unfold coeffApply sqdiagRootCoeffApply sqdiagKCAdjointCoeff KCMap dzC deltaC etaC cFun4Equiv
  simp_rw [Fintype.sum_prod_type]
  calc
    (∑ p : PVec n a, ∑ y : YVec n b, ∑ x : I n, ∑ w : WVec n d,
        C p y x w *
          ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
            + ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0))
        =
      ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
        refine Finset.sum_congr rfl ?_
        intro p _
        refine Finset.sum_congr rfl ?_
        intro y _
        calc
          (∑ x : I n, ∑ w : WVec n d,
              C p y x w *
                ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
                  + ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0))
              =
            ∑ w : WVec n d, ∑ x : I n,
              C p y x w *
                ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
                  + ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0) := by
              exact Finset.sum_comm
          _ =
            ∑ w : WVec n d, ∑ z : ZVec n c,
              (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
              refine Finset.sum_congr rfl ?_
              intro w _
              calc
                (∑ x : I n,
                  C p y x w *
                    ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
                      + ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0))
                    =
                  (∑ x : I n,
                    C p y x w *
                      ∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
                    +
                  ∑ x : I n,
                    C p y x w *
                      ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0 := by
                    rw [← Finset.sum_add_distrib]
                    refine Finset.sum_congr rfl ?_
                    intro x _
                    ring
                _ =
                  (∑ z : ZVec n c, C p y (vecSum z) w * A y z w)
                    +
                  ∑ z : ZVec n c, C p y (vecSum z + 1) w * A y z w := by
                    congr 1
                    · calc
                        (∑ x : I n,
                          C p y x w *
                            ∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
                          =
                          ∑ x : I n, ∑ z : ZVec n c,
                            C p y x w * (if vecSum z = x then A y z w else 0) := by
                            refine Finset.sum_congr rfl ?_
                            intro x _
                            rw [Finset.mul_sum]
                        _ =
                          ∑ z : ZVec n c, ∑ x : I n,
                            C p y x w * (if vecSum z = x then A y z w else 0) := by
                            exact Finset.sum_comm
                        _ = ∑ z : ZVec n c, C p y (vecSum z) w * A y z w := by
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
                            ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0)
                          =
                          ∑ x : I n, ∑ z : ZVec n c,
                            C p y x w * (if vecSum z + 1 = x then A y z w else 0) := by
                            refine Finset.sum_congr rfl ?_
                            intro x _
                            rw [Finset.mul_sum]
                        _ =
                          ∑ z : ZVec n c, ∑ x : I n,
                            C p y x w * (if vecSum z + 1 = x then A y z w else 0) := by
                            exact Finset.sum_comm
                        _ = ∑ z : ZVec n c, C p y (vecSum z + 1) w * A y z w := by
                            refine Finset.sum_congr rfl ?_
                            intro z _
                            rw [Finset.sum_eq_single (vecSum z + 1)]
                            · simp
                            · intro x _ hx
                              simp [hx.symm]
                            · simp
                _ =
                  ∑ z : ZVec n c,
                    (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
                    rw [← Finset.sum_add_distrib]
                    refine Finset.sum_congr rfl ?_
                    intro z _
                    ring
          _ =
            ∑ z : ZVec n c, ∑ w : WVec n d,
              (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
              exact Finset.sum_comm
    _ =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d, ∑ p : PVec n a,
        (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro z _
        rw [Finset.sum_comm]
    _ =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        (∑ p : PVec n a, (C p y (vecSum z) w + C p y (vecSum z + 1) w)) *
          A y z w := by
        refine Finset.sum_congr rfl ?_
        intro y _
        refine Finset.sum_congr rfl ?_
        intro z _
        refine Finset.sum_congr rfl ?_
        intro w _
        rw [← Finset.sum_mul]

theorem sqdiagRootCoeffApply_eq_of_KCAdjointCoeff_eq_of_mem_ZDiff
    {n a b c d : ℕ} [NeZero n]
    (A A' R : RootTarget n b c d)
    (hcoeff :
      sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A =
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A')
    (hR : R ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d)) :
    sqdiagRootCoeffApply A R = sqdiagRootCoeffApply A' R := by
  rw [← range_KCMap_eq_ZDiffSpace
    (n := n) (a := a) (b := b) (c := c) (d := d)] at hR
  rcases hR with ⟨C, hC⟩
  rw [← hC]
  rw [← sqdiag_coeffApply_KCAdjointCoeff_eq_rootCoeffApply_KCMap
    (n := n) (a := a) (b := b) (c := c) (d := d) A C]
  rw [← sqdiag_coeffApply_KCAdjointCoeff_eq_rootCoeffApply_KCMap
    (n := n) (a := a) (b := b) (c := c) (d := d) A' C]
  rw [hcoeff]

theorem sqdiagRootCoeffLinearMap_comp_ker_KCAdjointMap_eq_zero_of_mem_ZDiff
    {n a b c d : ℕ} [NeZero n]
    (R : RootTarget n b c d)
    (hR : R ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d)) :
    (sqdiagRootCoeffLinearMap (n := n) (b := b) (c := c) (d := d) R).comp
        (LinearMap.ker
          (sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d))).subtype =
      0 := by
  apply LinearMap.ext
  intro A
  change sqdiagRootCoeffApply A.1 R = 0
  have hcoeff :
      sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A.1 =
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) 0 := by
    have hA := LinearMap.mem_ker.mp A.2
    calc
      sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A.1
        = 0 := by
          change
            sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d) A.1 = 0
          exact hA
      _ =
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) 0 := by
          ext p y sz w
          simp [sqdiagKCAdjointCoeff]
  have hroot :=
    sqdiagRootCoeffApply_eq_of_KCAdjointCoeff_eq_of_mem_ZDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) A.1 0 R hcoeff hR
  simpa [sqdiagRootCoeffApply] using hroot

theorem sqdiagCPhaseLinear_eq_rootCoeffApply_KCMap_of_coeff_eq_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (A : RootTarget n b c d) (C : CFun4 n a b d)
    (hcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W =
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W C =
      sqdiagRootCoeffApply A
        (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) := by
  unfold sqdiagCPhaseLinear
  change
    coeffApply
        (cFun4Equiv n a b d
          (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W))
        (cFun4Equiv n a b d C) =
      sqdiagRootCoeffApply A
        (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C)
  rw [hcoeff]
  exact sqdiag_coeffApply_KCAdjointCoeff_eq_rootCoeffApply_KCMap
    (n := n) (a := a) (b := b) (c := c) (d := d) A C

theorem sqdiagCPhaseLinear_eq_rootCoeffApply_fiberTarget_of_coeff_eq_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (A : RootTarget n b c d) (C0 : CFun4 n a b d)
    (hcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W =
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A)
    (hC0 :
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C0 =
        sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W) :
    sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W C0 =
      sqdiagRootCoeffApply A
        (sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W) := by
  rw [sqdiagCPhaseLinear_eq_rootCoeffApply_KCMap_of_coeff_eq_KCAdjointCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d) B W A C0 hcoeff]
  rw [hC0]

theorem sqdiagCPhaseKernelZero_iff_forall_KC_zero_Q3
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    Core4loop.SquareDiagonal.sqdiagCPhaseKernelZero
        (n := n) (a := a) (b := b) (c := c) (d := d) B W ↔
      ∀ C : CFun4 n a b d,
        KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C = 0 →
          Q3 B C W = 0 := by
  constructor
  · intro hzero C hKC
    let L : CFun4 n a b d →ₗ[F] RootTarget n b c d :=
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
    let M : CFun4 n a b d →ₗ[F] F :=
      sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W
    have happ :=
      congrArg
        (fun T : LinearMap.ker L →ₗ[F] F =>
          T ⟨C, by
            rw [LinearMap.mem_ker]
            simpa [L] using hKC⟩)
        hzero
    have hM : M C = 0 := by
      simpa [L, M] using happ
    simpa [M, sqdiagCPhaseLinear_apply
      (n := n) (a := a) (b := b) (c := c) (d := d) B C W] using hM
  · intro hforall
    unfold Core4loop.SquareDiagonal.sqdiagCPhaseKernelZero
    ext x
    have hx : KCMap (n := n) (a := a) (b := b) (c := c) (d := d) x.1 = 0 := by
      exact LinearMap.mem_ker.mp x.2
    have hQ := hforall x.1 hx
    simpa [sqdiagCPhaseLinear_apply
      (n := n) (a := a) (b := b) (c := c) (d := d) B x.1 W] using hQ

private theorem exists_linearMap_comp_of_ker_le_ker
    {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (L : V →ₗ[F] W) (M : V →ₗ[F] F)
    (hker : LinearMap.ker L ≤ LinearMap.ker M) :
    ∃ N : W →ₗ[F] F, M = N.comp L := by
  let Mquot : V ⧸ LinearMap.ker L →ₗ[F] F :=
    (LinearMap.ker L).liftQ M hker
  let Mrange : LinearMap.range L →ₗ[F] F :=
    Mquot.comp L.quotKerEquivRange.symm.toLinearMap
  obtain ⟨N, hN⟩ := LinearMap.exists_extend Mrange
  refine ⟨N, ?_⟩
  ext x
  have hNx :=
    congrArg
      (fun T : LinearMap.range L →ₗ[F] F => T ⟨L x, ⟨x, rfl⟩⟩)
      hN
  simpa [Mquot, Mrange] using hNx.symm

private theorem coeffApply_forall_eq_zero_iff_local
    {ι : Type*} [Fintype ι] (c : ι → F) :
    (∀ f : ι → F, coeffApply c f = 0) ↔ c = 0 := by
  classical
  constructor
  · intro h
    funext i
    have hi := h (fun j => if j = i then (1 : F) else 0)
    unfold coeffApply at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa using hi
    · intro j _ hji
      simp [hji]
    · simp
  · intro hc f
    simp [coeffApply, hc]

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

private noncomputable def sqdiagRootTargetLinearEquiv (n b c d : ℕ) :
    RootTarget n b c d ≃ₗ[F] (YVec n b × ZVec n c × WVec n d → F) where
  toEquiv := aFun4Equiv n b c d
  map_add' R S := by
    funext u
    rcases u with ⟨y, z, w⟩
    rfl
  map_smul' r R := by
    funext u
    rcases u with ⟨y, z, w⟩
    rfl

private theorem sqdiagRootCoeffApply_eq_coeffApply
    {n b c d : ℕ} [NeZero n]
    (A R : RootTarget n b c d) :
    sqdiagRootCoeffApply A R =
      coeffApply (aFun4Equiv n b c d A) (aFun4Equiv n b c d R) := by
  unfold sqdiagRootCoeffApply coeffApply
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro z _
  refine Finset.sum_congr rfl ?_
  intro w _
  simp [aFun4Equiv]

theorem sqdiagRootCoeffApply_forall_eq_zero_iff
    {n b c d : ℕ} [NeZero n]
    (R : RootTarget n b c d) :
    (∀ A : RootTarget n b c d, sqdiagRootCoeffApply A R = 0) ↔ R = 0 := by
  classical
  constructor
  · intro h
    apply (aFun4Equiv n b c d).injective
    apply (coeffApply_forall_eq_zero_iff_local (aFun4Equiv n b c d R)).mp
    intro f
    rcases (aFun4Equiv n b c d).surjective f with ⟨A, rfl⟩
    have hcomm :
        coeffApply (aFun4Equiv n b c d R) (aFun4Equiv n b c d A) =
          coeffApply (aFun4Equiv n b c d A) (aFun4Equiv n b c d R) := by
      unfold coeffApply
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [mul_comm]
    rw [hcomm, ← sqdiagRootCoeffApply_eq_coeffApply]
    exact h A
  · intro h A
    simp [h, sqdiagRootCoeffApply]

private theorem exists_sqdiagRootCoeffApply_of_linearMap
    {n b c d : ℕ} [NeZero n]
    (M : RootTarget n b c d →ₗ[F] F) :
    ∃ A : RootTarget n b c d,
      ∀ R : RootTarget n b c d, sqdiagRootCoeffApply A R = M R := by
  let e := sqdiagRootTargetLinearEquiv n b c d
  obtain ⟨c, hc⟩ :=
    exists_coeffApply_of_linearMap (M.comp e.symm.toLinearMap)
  refine ⟨e.symm c, ?_⟩
  intro R
  rw [sqdiagRootCoeffApply_eq_coeffApply]
  simpa [e] using hc (e R)

theorem sqdiag_exists_rootCoeffApply_of_linearMap
    {n b c d : ℕ} [NeZero n]
    (M : RootTarget n b c d →ₗ[F] F) :
    ∃ A : RootTarget n b c d,
      ∀ R : RootTarget n b c d, sqdiagRootCoeffApply A R = M R :=
  exists_sqdiagRootCoeffApply_of_linearMap
    (n := n) (b := b) (c := c) (d := d) M

theorem sqdiagCPhaseKernelZero_iff_exists_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    Core4loop.SquareDiagonal.sqdiagCPhaseKernelZero
        (n := n) (a := a) (b := b) (c := c) (d := d) B W ↔
      ∃ A : RootTarget n b c d,
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W =
          sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A := by
  constructor
  · intro hzero
    rw [sqdiagCPhaseKernelZero_iff_forall_KC_zero_Q3
      (n := n) (a := a) (b := b) (c := c) (d := d) B W] at hzero
    let L : CFun4 n a b d →ₗ[F] RootTarget n b c d :=
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
    let M : CFun4 n a b d →ₗ[F] F :=
      sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W
    have hker : LinearMap.ker L ≤ LinearMap.ker M := by
      intro C hC
      rw [LinearMap.mem_ker] at hC ⊢
      have hQ := hzero C hC
      simpa [M, sqdiagCPhaseLinear_apply
        (n := n) (a := a) (b := b) (c := c) (d := d) B C W] using hQ
    obtain ⟨N, hN⟩ := exists_linearMap_comp_of_ker_le_ker L M hker
    obtain ⟨A, hA⟩ := exists_sqdiagRootCoeffApply_of_linearMap N
    refine ⟨A, ?_⟩
    apply (cFun4Equiv n a b d).injective
    have hzero :
        cFun4Equiv n a b d
          (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W)
          + cFun4Equiv n a b d
            (sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) A) = 0 := by
      apply (coeffApply_forall_eq_zero_iff_local
        (cFun4Equiv n a b d
          (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W)
          + cFun4Equiv n a b d
            (sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) A))).mp
      intro f
      rcases (cFun4Equiv n a b d).surjective f with ⟨C, rfl⟩
      have hphase :
          coeffApply
            (cFun4Equiv n a b d
              (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W))
            (cFun4Equiv n a b d C) = M C := by
        rfl
      have hadj :
          coeffApply
            (cFun4Equiv n a b d
              (sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A))
            (cFun4Equiv n a b d C) = N (L C) := by
        rw [sqdiag_coeffApply_KCAdjointCoeff_eq_rootCoeffApply_KCMap]
        exact hA (L C)
      have hcomp : M C = N (L C) := by
        simpa [L, M] using congrArg (fun T : CFun4 n a b d →ₗ[F] F => T C) hN
      calc
        coeffApply
            (cFun4Equiv n a b d
              (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W)
              + cFun4Equiv n a b d
                (sqdiagKCAdjointCoeff
                  (n := n) (a := a) (b := b) (c := c) (d := d) A))
            (cFun4Equiv n a b d C)
          =
            coeffApply
              (cFun4Equiv n a b d
                (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W))
              (cFun4Equiv n a b d C)
            +
            coeffApply
              (cFun4Equiv n a b d
                (sqdiagKCAdjointCoeff
                  (n := n) (a := a) (b := b) (c := c) (d := d) A))
              (cFun4Equiv n a b d C) := by
              unfold coeffApply
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro x _
              simp only [Pi.add_apply]
              ring
        _ = M C + N (L C) := by rw [hphase, hadj]
        _ = N (L C) + N (L C) := by rw [hcomp]
        _ = 0 := F_add_self _
    funext x
    exact (add_eq_zero_iff_eq_of_F_module _ _).mp (congrFun hzero x)
  · intro h
    rcases h with ⟨A, hcoeff⟩
    rw [sqdiagCPhaseKernelZero_iff_forall_KC_zero_Q3
      (n := n) (a := a) (b := b) (c := c) (d := d) B W]
    intro C hKC
    rw [← sqdiagCPhaseLinear_apply
      (n := n) (a := a) (b := b) (c := c) (d := d) B C W]
    change
      coeffApply
          (cFun4Equiv n a b d
            (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W))
          (cFun4Equiv n a b d C) = 0
    rw [hcoeff]
    rw [sqdiag_coeffApply_KCAdjointCoeff_eq_rootCoeffApply_KCMap]
    simp [sqdiagRootCoeffApply, hKC]

theorem sqdiagCPhaseKernelZero_of_coeff_eq_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (A : RootTarget n b c d)
    (hcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W =
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    Core4loop.SquareDiagonal.sqdiagCPhaseKernelZero
        (n := n) (a := a) (b := b) (c := c) (d := d) B W := by
  rw [sqdiagCPhaseKernelZero_iff_forall_KC_zero_Q3
    (n := n) (a := a) (b := b) (c := c) (d := d) B W]
  intro C hKC
  rw [← sqdiagCPhaseLinear_apply
    (n := n) (a := a) (b := b) (c := c) (d := d) B C W]
  change
    coeffApply
        (cFun4Equiv n a b d
          (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W))
        (cFun4Equiv n a b d C) = 0
  rw [hcoeff]
  rw [sqdiag_coeffApply_KCAdjointCoeff_eq_rootCoeffApply_KCMap]
  simp [sqdiagRootCoeffApply, hKC]

theorem sqdiagCPhaseKernelZero_of_squareCompat_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (hcompat :
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0) :
    Core4loop.SquareDiagonal.sqdiagCPhaseKernelZero
        (n := n) (a := a) (b := b) (c := c) (d := d) B W := by
  refine sqdiagCPhaseKernelZero_of_coeff_eq_KCAdjointCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d) B W 0 ?_
  ext p y sz w
  simp [sqdiagCPhaseCoeff, sqdiagKCAdjointCoeff, hcompat]

theorem sqdiagCPhaseLinear_eq_zero_of_squareCompat_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (hcompat :
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0) :
    sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W = 0 := by
  apply LinearMap.ext
  intro C
  unfold sqdiagCPhaseLinear sqdiagCPhaseCoeff
  simp [hcompat, coeffApply, cFun4Equiv]

private theorem coeffApply_forall_eq_zero_iff
    {ι : Type*} [Fintype ι] (c : ι → F) :
    (∀ f : ι → F, coeffApply c f = 0) ↔ c = 0 := by
  classical
  constructor
  · intro h
    funext i
    have hi := h (fun j => if j = i then (1 : F) else 0)
    unfold coeffApply at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa using hi
    · intro j _ hji
      simp [hji]
    · simp
  · intro hc f
    simp [coeffApply, hc]

theorem sqdiagCPhaseLinear_eq_zero_iff_squareCompat_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W = 0 ↔
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0 := by
  constructor
  · intro hlin
    have hcoeffZero :
        cFun4Equiv n a b d
          (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W) = 0 := by
      apply (coeffApply_forall_eq_zero_iff
        (cFun4Equiv n a b d
          (sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W))).mp
      intro f
      rcases (cFun4Equiv n a b d).surjective f with ⟨C, rfl⟩
      have happ := congrArg (fun L : CFun4 n a b d →ₗ[F] F => L C) hlin
      simpa [sqdiagCPhaseLinear] using happ
    have hcoeffZero' :
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W = 0 :=
      (cFun4Equiv n a b d).injective (by
        simpa [cFun4Equiv] using hcoeffZero)
    simpa [sqdiagCPhaseCoeff] using hcoeffZero'
  · intro hcompat
    exact sqdiagCPhaseLinear_eq_zero_of_squareCompat_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) B W hcompat

theorem sqdiagCFiberValue_eq_kernelCard_of_ZDiff_of_squareCompat_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (hZ :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
          ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d))
    (hcompat :
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0) :
    sqdiagCFiberValue (n := n) (a := a) (b := b) (c := c) (d := d) B W =
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
  classical
  let C0 : CFun4 n a b d :=
    Classical.choose
      ((sqdiagCFiberTarget_exists_preimage_iff_ZDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) B W).mpr hZ)
  have hC0 :
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C0 =
        sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W := by
    dsimp [C0]
    exact
      Classical.choose_spec
        ((sqdiagCFiberTarget_exists_preimage_iff_ZDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) B W).mpr hZ)
  rw [sqdiagCFiberValue_eq_of_preimage
    (n := n) (a := a) (b := b) (c := c) (d := d) B W C0 hC0]
  have hKernel :
      Core4loop.SquareDiagonal.sqdiagCPhaseKernelZero
        (n := n) (a := a) (b := b) (c := c) (d := d) B W :=
    sqdiagCPhaseKernelZero_of_squareCompat_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) B W hcompat
  have hLinear :
      sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W = 0 :=
    sqdiagCPhaseLinear_eq_zero_of_squareCompat_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) B W hcompat
  have hC0Phase :
      sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W C0 = 0 := by
    simpa using congrArg (fun L : CFun4 n a b d →ₗ[F] F => L C0) hLinear
  unfold sqdiagCFiberPreimageBranchValue
  rw [if_pos hKernel]
  simp [hC0Phase, bitSign_zero]

end SquareDiagonal
end Core4loop
