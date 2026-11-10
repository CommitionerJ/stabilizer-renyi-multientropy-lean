import Core4loop.Square.Kernel
import Core4loop.SquareDiagonal.CPhaseAdjoint

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

private theorem neg_eq_self_of_F_module {M : Type*} [AddCommGroup M] [Module F M]
    (x : M) :
    -x = x := by
  exact (add_eq_zero_iff_eq_of_F_module (-x) x).mp (by simp)

def sqdiagBWZCompatSupportPred {n a b c d : ℕ} [NeZero n]
    (x : BFun4 n a c d × WFun4 n a b c) : Prop :=
  K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x
      ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
    squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x = 0

def sqdiagBWZAdjointSupportPred {n a b c d : ℕ} [NeZero n]
    (x : BFun4 n a c d × WFun4 n a b c) : Prop :=
  K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x
      ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
    sqdiagCPhaseKernelZero
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2

abbrev sqdiagBWZCompatSupport (n a b c d : ℕ) [NeZero n] :=
  {x : BFun4 n a c d × WFun4 n a b c //
    sqdiagBWZCompatSupportPred (n := n) (a := a) (b := b) (c := c) (d := d) x}

abbrev sqdiagBWZAdjointSupport (n a b c d : ℕ) [NeZero n] :=
  {x : BFun4 n a c d × WFun4 n a b c //
    sqdiagBWZAdjointSupportPred (n := n) (a := a) (b := b) (c := c) (d := d) x}

noncomputable def sqdiagZCompatTargetSubmodule
    {n a b c d : ℕ} [NeZero n] :
    Submodule F (RootTarget n b c d × CFun4 n a b d) :=
  (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).prod
    (⊥ : Submodule F (CFun4 n a b d))

noncomputable def sqdiagZAdjointTargetSubmodule
    {n a b c d : ℕ} [NeZero n] :
    Submodule F (RootTarget n b c d × CFun4 n a b d) :=
  (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).prod
    (LinearMap.range
      (sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d)))

noncomputable def sqdiagBWZCompatSubmodule
    {n a b c d : ℕ} [NeZero n] :
    Submodule F (BFun4 n a c d × WFun4 n a b c) :=
  (sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)).comap
    (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def sqdiagBWZAdjointSubmodule
    {n a b c d : ℕ} [NeZero n] :
    Submodule F (BFun4 n a c d × WFun4 n a b c) :=
  (sqdiagZAdjointTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)).comap
    (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable instance instFintypeSqdiagBWZCompatSupport
    {n a b c d : ℕ} [NeZero n] :
    Fintype (sqdiagBWZCompatSupport n a b c d) := by
  classical
  infer_instance

noncomputable instance instFintypeSqdiagBWZAdjointSupport
    {n a b c d : ℕ} [NeZero n] :
    Fintype (sqdiagBWZAdjointSupport n a b c d) := by
  classical
  infer_instance

noncomputable instance instFintypeSquareCombinedKernel
    {n a b c d : ℕ} [NeZero n] :
    Fintype (SquareCombinedKernel n a b c d) :=
  Fintype.ofInjective
    (fun x : SquareCombinedKernel n a b c d =>
      (x : BFun4 n a c d × WFun4 n a b c))
    (by
      intro x y hxy
      exact Subtype.ext hxy)

theorem K_yw_eq_KBMap_add_KWMap
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) =
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W := by
  funext y z w
  change
    (∑ p : PVec n a, (dyB B p y z w + dwW W p y z w)) =
      (∑ p : PVec n a, dyB B p y z w) +
        ∑ p : PVec n a, dwW W p y z w
  rw [Finset.sum_add_distrib]

theorem sqdiagBWZCompatSupportPred_iff
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    sqdiagBWZCompatSupportPred
        (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) ↔
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
          + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
            ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
        squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0 := by
  simp [sqdiagBWZCompatSupportPred, K_yw_eq_KBMap_add_KWMap]

theorem sqdiagZCompatTargetSubmodule_mem_iff
    {n a b c d : ℕ} [NeZero n]
    (x : RootTarget n b c d × CFun4 n a b d) :
    x ∈ sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) ↔
      x.1 ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧ x.2 = 0 := by
  simp [sqdiagZCompatTargetSubmodule]

theorem sqdiagZAdjointTargetSubmodule_mem_iff
    {n a b c d : ℕ} [NeZero n]
    (x : RootTarget n b c d × CFun4 n a b d) :
    x ∈ sqdiagZAdjointTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) ↔
      x.1 ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
        ∃ A : RootTarget n b c d,
          sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A =
            x.2 := by
  simp [sqdiagZAdjointTargetSubmodule]

theorem sqdiagBWZCompatSubmodule_mem_iff
    {n a b c d : ℕ} [NeZero n]
    (x : BFun4 n a c d × WFun4 n a b c) :
    x ∈ sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) ↔
      sqdiagBWZCompatSupportPred (n := n) (a := a) (b := b) (c := c) (d := d) x := by
  simp [sqdiagBWZCompatSubmodule, sqdiagZCompatTargetSubmodule,
    sqdiagBWZCompatSupportPred, SquareCombined]

theorem sqdiagBWZAdjointSubmodule_mem_iff
    {n a b c d : ℕ} [NeZero n]
    (x : BFun4 n a c d × WFun4 n a b c) :
    x ∈ sqdiagBWZAdjointSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) ↔
      sqdiagBWZAdjointSupportPred (n := n) (a := a) (b := b) (c := c) (d := d) x := by
  constructor
  · intro hx
    have htarget :=
      (sqdiagZAdjointTargetSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x)).mp hx
    constructor
    · simpa [SquareCombined] using htarget.1
    · rw [sqdiagCPhaseKernelZero_iff_exists_KCAdjointCoeff]
      rcases htarget.2 with ⟨A, hA⟩
      exact ⟨A, by simpa [SquareCombined, sqdiagCPhaseCoeff] using hA.symm⟩
  · intro hx
    apply (sqdiagZAdjointTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x)).mpr
    rcases hx with ⟨hZ, hK⟩
    constructor
    · simpa [SquareCombined] using hZ
    · have hExists :=
        (sqdiagCPhaseKernelZero_iff_exists_KCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2).mp hK
      rcases hExists with ⟨A, hA⟩
      exact ⟨A, by simpa [SquareCombined, sqdiagCPhaseCoeff] using hA.symm⟩

theorem sqdiagBWZCompatSubmodule_eq_K_yw_ZDiff_inf_squareCompat_ker
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) =
      (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).comap
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
        LinearMap.ker
          (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  ext x
  simp [sqdiagBWZCompatSubmodule_mem_iff, sqdiagBWZCompatSupportPred, LinearMap.mem_ker]

theorem SquareCombinedKernel_eq_K_yw_ker_inf_squareCompat_ker
    {n a b c d : ℕ} [NeZero n] :
    SquareCombinedKernel n a b c d =
      LinearMap.ker (K_yw (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
        LinearMap.ker
          (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  ext x
  simp [SquareCombinedKernel, SquareCombined, LinearMap.mem_ker]

theorem sqdiagBWZCompatSubmodule_le_sqdiagBWZAdjointSubmodule
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) ≤
      sqdiagBWZAdjointSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) := by
  intro x hx
  rw [sqdiagBWZAdjointSubmodule_mem_iff]
  rw [sqdiagBWZCompatSubmodule_mem_iff] at hx
  exact
    ⟨hx.1,
      sqdiagCPhaseKernelZero_of_squareCompat_eq_zero
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2 hx.2⟩

def sqdiagBWZCompatSupportEquivSubmodule
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZCompatSupport n a b c d ≃
      sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) where
  toFun x :=
    ⟨x.1,
      (sqdiagBWZCompatSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mpr x.2⟩
  invFun x :=
    ⟨x.1,
      (sqdiagBWZCompatSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

def sqdiagBWZAdjointSupportEquivSubmodule
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZAdjointSupport n a b c d ≃
      sqdiagBWZAdjointSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) where
  toFun x :=
    ⟨x.1,
      (sqdiagBWZAdjointSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mpr x.2⟩
  invFun x :=
    ⟨x.1,
      (sqdiagBWZAdjointSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

def sqdiagBWAAdjointGraphPred
    {n a b c d : ℕ} [NeZero n]
    (x : (BFun4 n a c d × WFun4 n a b c) × RootTarget n b c d) : Prop :=
  K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1
      ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) ∧
    sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 =
      sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.2

abbrev sqdiagBWAAdjointGraphSupport (n a b c d : ℕ) [NeZero n] :=
  {x : (BFun4 n a c d × WFun4 n a b c) × RootTarget n b c d //
    sqdiagBWAAdjointGraphPred (n := n) (a := a) (b := b) (c := c) (d := d) x}

noncomputable def sqdiagBWAAdjointGraphMap
    {n a b c d : ℕ} [NeZero n] :
    ((BFun4 n a c d × WFun4 n a b c) × RootTarget n b c d) →ₗ[F]
      (RootTarget n b c d × CFun4 n a b d) where
  toFun x :=
    (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1,
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 +
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.2)
  map_add' x y := by
    apply Prod.ext
    · exact (K_yw (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
    · change
        squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
          (x.1.1 + y.1.1, x.1.2 + y.1.2) +
            sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
              (((x.2 : RootTarget n b c d) + (y.2 : RootTarget n b c d)) :
                RootTarget n b c d) =
          (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1 +
              sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.2) +
            (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) y.1 +
              sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) y.2)
      have hsquare :
          squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
              (x.1.1 + y.1.1, x.1.2 + y.1.2) =
            squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1 +
              squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) y.1 := by
        have h :=
          (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
        exact h
      rw [hsquare]
      rw [← sqdiagKCAdjointMap_apply
        (n := n) (a := a) (b := b) (c := c) (d := d) (x.2 + y.2)]
      rw [(sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_add]
      simp only [sqdiagKCAdjointMap_apply]
      ext p yy sz w
      simp only [Pi.add_apply]
      abel
  map_smul' r x := by
    apply Prod.ext
    · exact (K_yw (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1
    · change
        squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
          (r • x.1.1, r • x.1.2) +
            sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
              (r • (x.2 : RootTarget n b c d)) =
          r •
            (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1 +
              sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.2)
      have hsquare :
          squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
              (r • x.1.1, r • x.1.2) =
            r • squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1 := by
        have h :=
          (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1
        exact h
      rw [hsquare]
      rw [← sqdiagKCAdjointMap_apply
        (n := n) (a := a) (b := b) (c := c) (d := d) (r • x.2)]
      rw [(sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul]
      simp only [sqdiagKCAdjointMap_apply]
      ext p yy sz w
      simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add]

noncomputable def sqdiagBWAAdjointGraphSubmodule
    {n a b c d : ℕ} [NeZero n] :
    Submodule F ((BFun4 n a c d × WFun4 n a b c) × RootTarget n b c d) :=
  (sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)).comap
    (sqdiagBWAAdjointGraphMap (n := n) (a := a) (b := b) (c := c) (d := d))

theorem sqdiagBWAAdjointGraphSubmodule_mem_iff
    {n a b c d : ℕ} [NeZero n]
    (x : (BFun4 n a c d × WFun4 n a b c) × RootTarget n b c d) :
    x ∈ sqdiagBWAAdjointGraphSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) ↔
      sqdiagBWAAdjointGraphPred (n := n) (a := a) (b := b) (c := c) (d := d) x := by
  constructor
  · intro hx
    have htarget :=
      (sqdiagZCompatTargetSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagBWAAdjointGraphMap (n := n) (a := a) (b := b) (c := c) (d := d) x)).mp hx
    constructor
    · exact htarget.1
    · exact (add_eq_zero_iff_eq_of_F_module _ _).mp htarget.2
  · intro hx
    apply (sqdiagZCompatTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagBWAAdjointGraphMap (n := n) (a := a) (b := b) (c := c) (d := d) x)).mpr
    constructor
    · exact hx.1
    · exact (add_eq_zero_iff_eq_of_F_module _ _).mpr hx.2

noncomputable instance instFintypeSqdiagBWAAdjointGraphSupport
    {n a b c d : ℕ} [NeZero n] :
    Fintype (sqdiagBWAAdjointGraphSupport n a b c d) := by
  classical
  infer_instance

def sqdiagBWAAdjointGraphSupportEquivSubmodule
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphSupport n a b c d ≃
      sqdiagBWAAdjointGraphSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) where
  toFun x :=
    ⟨x.1,
      (sqdiagBWAAdjointGraphSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mpr x.2⟩
  invFun x :=
    ⟨x.1,
      (sqdiagBWAAdjointGraphSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

set_option synthInstance.maxHeartbeats 200000 in
theorem natCard_sqdiagBWAAdjointGraphSupport
    {n a b c d : ℕ} [NeZero n] :
    Nat.card (sqdiagBWAAdjointGraphSupport n a b c d) =
      2 ^ Module.finrank F
        (sqdiagBWAAdjointGraphSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [Nat.card_congr
    (sqdiagBWAAdjointGraphSupportEquivSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d))]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

def sqdiagBWAAdjointGraphToBWZAdjointSupport
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWAAdjointGraphSupport n a b c d) :
    sqdiagBWZAdjointSupport n a b c d :=
  ⟨x.1.1,
    ⟨x.2.1,
      sqdiagCPhaseKernelZero_of_coeff_eq_KCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1.1 x.1.1.2 x.1.2 x.2.2⟩⟩

abbrev sqdiagBWZAdjointFiber
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZAdjointSupport n a b c d) :=
  {A : RootTarget n b c d //
    sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A =
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2}

noncomputable instance instFintypeSqdiagBWZAdjointFiber
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZAdjointSupport n a b c d) :
    Fintype (sqdiagBWZAdjointFiber (n := n) (a := a) (b := b) (c := c) (d := d) x) := by
  classical
  infer_instance

def sqdiagBWAAdjointGraphSupportEquivSigmaFiber
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphSupport n a b c d ≃
      Sigma
        (fun x : sqdiagBWZAdjointSupport n a b c d =>
          sqdiagBWZAdjointFiber (n := n) (a := a) (b := b) (c := c) (d := d) x) where
  toFun x :=
    ⟨sqdiagBWAAdjointGraphToBWZAdjointSupport
        (n := n) (a := a) (b := b) (c := c) (d := d) x,
      ⟨x.1.2, x.2.2.symm⟩⟩
  invFun x :=
    ⟨(x.1.1, x.2.1), ⟨x.1.2.1, x.2.2.symm⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    cases x with
    | mk x A =>
        simp [sqdiagBWAAdjointGraphToBWZAdjointSupport]

noncomputable def sqdiagBWAAdjointGraphRootSignSum
    {n a b c d : ℕ} [NeZero n] : ℤ :=
  ∑ x : sqdiagBWAAdjointGraphSupport n a b c d,
    bitSign
      (sqdiagRootCoeffApply x.1.2
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1))

noncomputable def sqdiagBWZAdjointWitness
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZAdjointSupport n a b c d) : RootTarget n b c d :=
  Classical.choose
    ((sqdiagCPhaseKernelZero_iff_exists_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2).mp x.2.2)

theorem sqdiagBWZAdjointWitness_spec
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZAdjointSupport n a b c d) :
    sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 =
      sqdiagKCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x) := by
  unfold sqdiagBWZAdjointWitness
  exact
    Classical.choose_spec
      ((sqdiagCPhaseKernelZero_iff_exists_KCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2).mp x.2.2)

theorem sqdiagBWZAdjointWitness_rootCoeffApply_eq_of_coeff_eq_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZAdjointSupport n a b c d)
    (A : RootTarget n b c d)
    (hcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 =
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    sqdiagRootCoeffApply
        (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x)
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1) =
      sqdiagRootCoeffApply A
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1) := by
  refine sqdiagRootCoeffApply_eq_of_KCAdjointCoeff_eq_of_mem_ZDiff
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x)
    A
    (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1) ?_ x.2.1
  calc
    sqdiagKCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x)
      =
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 := by
          exact (sqdiagBWZAdjointWitness_spec
            (n := n) (a := a) (b := b) (c := c) (d := d) x).symm
    _ =
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A := hcoeff

theorem sqdiagBWAAdjointGraph_witness_rootCoeffApply_eq
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWAAdjointGraphSupport n a b c d) :
    sqdiagRootCoeffApply
        (sqdiagBWZAdjointWitness
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagBWAAdjointGraphToBWZAdjointSupport
            (n := n) (a := a) (b := b) (c := c) (d := d) x))
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1) =
      sqdiagRootCoeffApply x.1.2
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1) := by
  exact
    sqdiagBWZAdjointWitness_rootCoeffApply_eq_of_coeff_eq_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagBWAAdjointGraphToBWZAdjointSupport
        (n := n) (a := a) (b := b) (c := c) (d := d) x)
      x.1.2 x.2.2

noncomputable def sqdiagAdjointWitnessFiberSignSum
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZAdjointSupport n a b c d) : ℤ := by
  classical
  exact
    ∑ A : RootTarget n b c d,
      if sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A =
          sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 then
        bitSign
          (sqdiagRootCoeffApply A
            (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1))
      else 0

theorem sqdiagAdjointWitnessFiberSignSum_eq_fiber_sum
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZAdjointSupport n a b c d) :
    sqdiagAdjointWitnessFiberSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x =
      ∑ A : sqdiagBWZAdjointFiber
          (n := n) (a := a) (b := b) (c := c) (d := d) x,
        bitSign
          (sqdiagRootCoeffApply A.1
            (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
  classical
  let p : RootTarget n b c d → Prop :=
    fun A =>
      sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A =
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2
  let f : RootTarget n b c d → ℤ :=
    fun A =>
      bitSign
        (sqdiagRootCoeffApply A
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1))
  change (∑ A : RootTarget n b c d, if p A then f A else 0) =
      ∑ A : {A : RootTarget n b c d // p A}, f A.1
  rw [← Finset.sum_subtype
    (s := Finset.univ.filter p)
    (h := by intro A; simp [p])
    (f := f)]
  rw [Finset.sum_filter]

noncomputable def sqdiagKCAdjointKernelCardZ
    {n a b c d : ℕ} [NeZero n] : ℤ :=
  (Fintype.card
    (LinearMap.ker
      (sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ)

theorem sqdiagKCAdjointKernelCardZ_ne_zero
    {n a b c d : ℕ} [NeZero n] :
    sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) ≠ 0 := by
  unfold sqdiagKCAdjointKernelCardZ
  have hnonempty :
      Nonempty
        (LinearMap.ker
          (sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d))) :=
    ⟨0⟩
  exact_mod_cast
    (Fintype.card_ne_zero
      (α :=
        LinearMap.ker
          (sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d))))

noncomputable def sqdiagBWZAdjointRootCoeffSignSum
    {n a b c d : ℕ} [NeZero n] : ℤ :=
  ∑ x : sqdiagBWZAdjointSupport n a b c d,
    bitSign
      (sqdiagRootCoeffApply
        (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x)
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1))

noncomputable def sqdiagBWZAdjointWitnessFiberTotalSignSum
    {n a b c d : ℕ} [NeZero n] : ℤ :=
  ∑ x : sqdiagBWZAdjointSupport n a b c d,
    sqdiagAdjointWitnessFiberSignSum
      (n := n) (a := a) (b := b) (c := c) (d := d) x

theorem sqdiagBWAAdjointGraphRootSignSum_eq_BWZAdjointWitnessFiberTotalSignSum
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      sqdiagBWZAdjointWitnessFiberTotalSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  classical
  unfold sqdiagBWAAdjointGraphRootSignSum
  unfold sqdiagBWZAdjointWitnessFiberTotalSignSum
  calc
    (∑ x : sqdiagBWAAdjointGraphSupport n a b c d,
      bitSign
        (sqdiagRootCoeffApply x.1.2
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1)))
        =
      ∑ x : Sigma
          (fun y : sqdiagBWZAdjointSupport n a b c d =>
            sqdiagBWZAdjointFiber (n := n) (a := a) (b := b) (c := c) (d := d) y),
        bitSign
          (sqdiagRootCoeffApply x.2.1
            (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1)) := by
          exact
            Fintype.sum_equiv
              (sqdiagBWAAdjointGraphSupportEquivSigmaFiber
                (n := n) (a := a) (b := b) (c := c) (d := d))
              (fun x : sqdiagBWAAdjointGraphSupport n a b c d =>
                bitSign
                  (sqdiagRootCoeffApply x.1.2
                    (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1)))
              (fun x : Sigma
                  (fun y : sqdiagBWZAdjointSupport n a b c d =>
                    sqdiagBWZAdjointFiber
                      (n := n) (a := a) (b := b) (c := c) (d := d) y) =>
                bitSign
                  (sqdiagRootCoeffApply x.2.1
                    (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1)))
              (by
                intro x
                simp [sqdiagBWAAdjointGraphSupportEquivSigmaFiber,
                  sqdiagBWAAdjointGraphToBWZAdjointSupport])
    _ =
      ∑ x : sqdiagBWZAdjointSupport n a b c d,
        ∑ A : sqdiagBWZAdjointFiber
            (n := n) (a := a) (b := b) (c := c) (d := d) x,
          bitSign
            (sqdiagRootCoeffApply A.1
              (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
        rw [Fintype.sum_sigma]
    _ =
      ∑ x : sqdiagBWZAdjointSupport n a b c d,
        sqdiagAdjointWitnessFiberSignSum
          (n := n) (a := a) (b := b) (c := c) (d := d) x := by
        refine Finset.sum_congr rfl ?_
        intro x _
        exact
          (sqdiagAdjointWitnessFiberSignSum_eq_fiber_sum
            (n := n) (a := a) (b := b) (c := c) (d := d) x).symm

theorem sqdiagAdjointWitnessFiberSignSum_eq_kernelCard_mul_witness_rootSign
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZAdjointSupport n a b c d) :
    sqdiagAdjointWitnessFiberSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x =
    (Fintype.card
      (LinearMap.ker
        (sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ) *
      bitSign
        (sqdiagRootCoeffApply
          (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x)
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
  classical
  let target : CFun4 n a b d :=
    sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2
  let L : RootTarget n b c d →ₗ[F] CFun4 n a b d :=
    sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d)
  let R : RootTarget n b c d :=
    K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1
  let M : RootTarget n b c d →ₗ[F] F :=
    sqdiagRootCoeffLinearMap (n := n) (b := b) (c := c) (d := d) R
  have hpre :
      L
        (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x) =
        target := by
    change
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x)
        =
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2
    exact (sqdiagBWZAdjointWitness_spec
      (n := n) (a := a) (b := b) (c := c) (d := d) x).symm
  have hMzero :
      (M.comp (LinearMap.ker L).subtype) = 0 := by
    dsimp [M, L]
    exact sqdiagRootCoeffLinearMap_comp_ker_KCAdjointMap_eq_zero_of_mem_ZDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) R x.2.1
  have hsum :=
    sum_if_linearMap_eq_const_bitSign_linearMap_add_const_of_preimage
      (V := RootTarget n b c d) (W := CFun4 n a b d)
      L M 0 target
      (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x)
      hpre
  rw [hMzero] at hsum
  simpa [sqdiagAdjointWitnessFiberSignSum, target, L, M, R] using hsum

theorem sqdiagBWZAdjointWitnessFiberTotalSignSum_eq_KCAdjointKernelCard_mul_rootCoeffSignSum
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZAdjointWitnessFiberTotalSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        sqdiagBWZAdjointRootCoeffSignSum
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
  unfold sqdiagBWZAdjointWitnessFiberTotalSignSum
  unfold sqdiagBWZAdjointRootCoeffSignSum
  unfold sqdiagKCAdjointKernelCardZ
  calc
    (∑ x : sqdiagBWZAdjointSupport n a b c d,
      sqdiagAdjointWitnessFiberSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x)
        =
      ∑ x : sqdiagBWZAdjointSupport n a b c d,
        (Fintype.card
          (LinearMap.ker
            (sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ) *
          bitSign
            (sqdiagRootCoeffApply
              (sqdiagBWZAdjointWitness
                (n := n) (a := a) (b := b) (c := c) (d := d) x)
              (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact
            sqdiagAdjointWitnessFiberSignSum_eq_kernelCard_mul_witness_rootSign
              (n := n) (a := a) (b := b) (c := c) (d := d) x
    _ =
      (Fintype.card
        (LinearMap.ker
          (sqdiagKCAdjointMap (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ) *
        ∑ x : sqdiagBWZAdjointSupport n a b c d,
          bitSign
            (sqdiagRootCoeffApply
              (sqdiagBWZAdjointWitness
                (n := n) (a := a) (b := b) (c := c) (d := d) x)
              (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
        rw [Finset.mul_sum]

theorem sqdiagCFiberValue_eq_kernelCard_of_BWZCompatSupport
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZCompatSupport n a b c d) :
    sqdiagCFiberValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 =
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
  have hZ :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1
          + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2
            ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
    exact
      ((sqdiagBWZCompatSupportPred_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2).mp x.2).1
  exact sqdiagCFiberValue_eq_kernelCard_of_ZDiff_of_squareCompat_eq_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 hZ x.2.2

theorem sqdiagCFiberClassifiedValue_eq_kernelCard_of_BWZCompatSupport
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZCompatSupport n a b c d) :
    sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 =
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [← sqdiagCFiberValue_eq_classifiedValue
    (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2]
  exact sqdiagCFiberValue_eq_kernelCard_of_BWZCompatSupport
    (n := n) (a := a) (b := b) (c := c) (d := d) x

theorem sqdiagCFiberClassifiedValue_eq_kernelCard_mul_bitSign_rootCoeffApply
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZAdjointSupport n a b c d) :
    sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 =
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        bitSign
          (sqdiagRootCoeffApply
            (sqdiagBWZAdjointWitness
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
            (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
  classical
  let B : BFun4 n a c d := x.1.1
  let W : WFun4 n a b c := x.1.2
  have hZsum :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
          ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
    rw [← K_yw_eq_KBMap_add_KWMap
      (n := n) (a := a) (b := b) (c := c) (d := d) B W]
    exact x.2.1
  let C0 : CFun4 n a b d :=
    Classical.choose
      ((sqdiagCFiberTarget_exists_preimage_iff_ZDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) B W).mpr hZsum)
  have hC0 :
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C0 =
        sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W := by
    dsimp [C0]
    exact
      Classical.choose_spec
        ((sqdiagCFiberTarget_exists_preimage_iff_ZDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) B W).mpr hZsum)
  have hcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x) := by
    simpa [B, W] using
      sqdiagBWZAdjointWitness_spec
        (n := n) (a := a) (b := b) (c := c) (d := d) x
  rw [← sqdiagCFiberValue_eq_classifiedValue
    (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2]
  rw [sqdiagCFiberValue_eq_of_preimage
    (n := n) (a := a) (b := b) (c := c) (d := d) B W C0 hC0]
  unfold sqdiagCFiberPreimageBranchValue
  rw [if_pos (by simpa [B, W] using x.2.2)]
  have hphaseTarget :
      sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W C0 =
        sqdiagRootCoeffApply
          (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x)
          (sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W) :=
    sqdiagCPhaseLinear_eq_rootCoeffApply_fiberTarget_of_coeff_eq_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) B W
      (sqdiagBWZAdjointWitness (n := n) (a := a) (b := b) (c := c) (d := d) x)
      C0 hcoeff hC0
  have htarget :
      sqdiagCFiberTarget (n := n) (a := a) (b := b) (c := c) (d := d) B W =
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1 := by
    unfold sqdiagCFiberTarget
    rw [K_yw_eq_KBMap_add_KWMap
      (n := n) (a := a) (b := b) (c := c) (d := d) B W]
    exact neg_eq_self_of_F_module _
  simp [B, W, hphaseTarget, htarget]

theorem sqdiagCFiberClassifiedValue_eq_kernelCard_mul_bitSign_rootCoeffApply_of_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZAdjointSupport n a b c d)
    (A : RootTarget n b c d)
    (hcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 =
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 =
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        bitSign
          (sqdiagRootCoeffApply A
            (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
  rw [sqdiagCFiberClassifiedValue_eq_kernelCard_mul_bitSign_rootCoeffApply
    (n := n) (a := a) (b := b) (c := c) (d := d) x]
  rw [sqdiagBWZAdjointWitness_rootCoeffApply_eq_of_coeff_eq_KCAdjointCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d) x A hcoeff]

theorem sqdiagCFiberClassifiedValue_eq_zero_of_not_BWZAdjointSupportPred
    {n a b c d : ℕ} [NeZero n]
    (x : BFun4 n a c d × WFun4 n a b c)
    (hx :
      ¬ sqdiagBWZAdjointSupportPred
        (n := n) (a := a) (b := b) (c := c) (d := d) x) :
    sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2 = 0 := by
  classical
  unfold sqdiagCFiberClassifiedValue
  by_cases hZ :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) x.1
        + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) x.2
          ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d)
  · rw [dif_pos hZ]
    by_cases hK :
        sqdiagCPhaseKernelZero
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2
    · exfalso
      have hKYW :
          K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x
            ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
        rw [K_yw_eq_KBMap_add_KWMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2]
        exact hZ
      exact hx ⟨hKYW, hK⟩
    · rw [if_neg hK]
  · rw [dif_neg hZ]

theorem sqdiagBWZCompatSupportPred_of_SquareCombined_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (h :
      SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0) :
    sqdiagBWZCompatSupportPred
      (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) := by
  have hK :
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0 :=
    congrArg Prod.fst h
  have hCompat :
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0 :=
    congrArg Prod.snd h
  exact ⟨by simp [hK], hCompat⟩

def sqdiagBWZCompatSupportOfSquareCombinedKernel
    {n a b c d : ℕ} [NeZero n]
    (x : SquareCombinedKernel n a b c d) :
    sqdiagBWZCompatSupport n a b c d :=
  ⟨x.1,
    sqdiagBWZCompatSupportPred_of_SquareCombined_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2
      (LinearMap.mem_ker.mp x.2)⟩

theorem SquareCombinedKernel_le_sqdiagBWZCompatSubmodule
    {n a b c d : ℕ} [NeZero n] :
    SquareCombinedKernel n a b c d ≤
      sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) := by
  intro x hx
  rw [sqdiagBWZCompatSubmodule_mem_iff]
  exact sqdiagBWZCompatSupportPred_of_SquareCombined_eq_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2
    (LinearMap.mem_ker.mp hx)

theorem sqdiagBWZCompatSupportOfSquareCombinedKernel_injective
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
      (sqdiagBWZCompatSupportOfSquareCombinedKernel
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun t : sqdiagBWZCompatSupport n a b c d => t.1) hxy

set_option synthInstance.maxHeartbeats 200000 in
-- The cardinality formula asks Lean to synthesize module structure for a high-dimensional
-- comap submodule; this matches the budget used for the existing square kernel count.
theorem natCard_sqdiagBWZCompatSupport
    {n a b c d : ℕ} [NeZero n] :
    Nat.card (sqdiagBWZCompatSupport n a b c d) =
      2 ^ Module.finrank F
        (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [Nat.card_congr
    (sqdiagBWZCompatSupportEquivSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d))]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

set_option synthInstance.maxHeartbeats 200000 in
-- This is the same high-dimensional subtype/submodule cardinality package as the compat support.
theorem natCard_sqdiagBWZAdjointSupport
    {n a b c d : ℕ} [NeZero n] :
    Nat.card (sqdiagBWZAdjointSupport n a b c d) =
      2 ^ Module.finrank F
        (sqdiagBWZAdjointSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [Nat.card_congr
    (sqdiagBWZAdjointSupportEquivSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d))]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

set_option maxHeartbeats 800000 in
-- The subtype restriction rewrites a high-dimensional product sum through a dependent support.
theorem sqdiag_sum_over_all_BW_classifiedValue_eq_sum_over_BWZAdjointSupport
    {n a b c d : ℕ} [NeZero n] :
    (∑ B : BFun4 n a c d,
      ∑ W : WFun4 n a b c,
        sqdiagCFiberClassifiedValue
          (n := n) (a := a) (b := b) (c := c) (d := d) B W)
      =
    (∑ x : sqdiagBWZAdjointSupport n a b c d,
      sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2) := by
  classical
  let p : BFun4 n a c d × WFun4 n a b c → Prop :=
    fun x =>
      sqdiagBWZAdjointSupportPred
        (n := n) (a := a) (b := b) (c := c) (d := d) x
  let f : BFun4 n a c d × WFun4 n a b c → ℤ :=
    fun x =>
      sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 x.2
  have hrestrict :
      (∑ x : BFun4 n a c d × WFun4 n a b c, f x) =
        ∑ x : BFun4 n a c d × WFun4 n a b c,
          if p x then (1 : ℤ) * f x else 0 := by
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases hx : p x
    · simp [hx]
    · have hzero :
        f x = 0 := by
          exact
            sqdiagCFiberClassifiedValue_eq_zero_of_not_BWZAdjointSupportPred
              (n := n) (a := a) (b := b) (c := c) (d := d) x
              (by simpa [p] using hx)
      simp [hx, hzero]
  calc
    (∑ B : BFun4 n a c d,
      ∑ W : WFun4 n a b c,
        sqdiagCFiberClassifiedValue
          (n := n) (a := a) (b := b) (c := c) (d := d) B W)
        =
      ∑ x : BFun4 n a c d × WFun4 n a b c, f x := by
        rw [Fintype.sum_prod_type]
    _ =
      ∑ x : BFun4 n a c d × WFun4 n a b c,
        if p x then (1 : ℤ) * f x else 0 := hrestrict
    _ =
      (1 : ℤ) * ∑ x : {x : BFun4 n a c d × WFun4 n a b c // p x}, f x.1 := by
        exact sum_if_mul_eq_mul_subtype p (1 : ℤ) f
    _ =
      ∑ x : sqdiagBWZAdjointSupport n a b c d,
        sqdiagCFiberClassifiedValue
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 := by
        change
          (1 : ℤ) *
              (∑ x : sqdiagBWZAdjointSupport n a b c d,
                sqdiagCFiberClassifiedValue
                  (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
            =
          ∑ x : sqdiagBWZAdjointSupport n a b c d,
            sqdiagCFiberClassifiedValue
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2
        simp

theorem sqdiag_survivor_sum_as_BWZAdjointSupport_classifiedValue
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    (∑ x : sqdiagBWZAdjointSupport n a b c d,
      sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2) := by
  rw [sqdiag_survivor_sum_as_BW_ZDiff_kernel_classified_value]
  exact sqdiag_sum_over_all_BW_classifiedValue_eq_sum_over_BWZAdjointSupport
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiag_sum_over_BWZAdjointSupport_classifiedValue_eq_kernelCard_mul_rootCoeffSign
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : sqdiagBWZAdjointSupport n a b c d,
      sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
      =
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      ∑ x : sqdiagBWZAdjointSupport n a b c d,
        bitSign
          (sqdiagRootCoeffApply
            (sqdiagBWZAdjointWitness
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
            (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
  calc
    (∑ x : sqdiagBWZAdjointSupport n a b c d,
      sqdiagCFiberClassifiedValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
        =
      ∑ x : sqdiagBWZAdjointSupport n a b c d,
        sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
          bitSign
            (sqdiagRootCoeffApply
              (sqdiagBWZAdjointWitness
                (n := n) (a := a) (b := b) (c := c) (d := d) x)
              (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact sqdiagCFiberClassifiedValue_eq_kernelCard_mul_bitSign_rootCoeffApply
            (n := n) (a := a) (b := b) (c := c) (d := d) x
    _ =
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
        ∑ x : sqdiagBWZAdjointSupport n a b c d,
          bitSign
            (sqdiagRootCoeffApply
              (sqdiagBWZAdjointWitness
                (n := n) (a := a) (b := b) (c := c) (d := d) x)
              (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
        rw [Finset.mul_sum]

theorem sqdiag_survivor_sum_eq_kernelCard_mul_BWZAdjointSupport_rootCoeffSign
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      ∑ x : sqdiagBWZAdjointSupport n a b c d,
        bitSign
          (sqdiagRootCoeffApply
            (sqdiagBWZAdjointWitness
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
            (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1)) := by
  rw [sqdiag_survivor_sum_as_BWZAdjointSupport_classifiedValue]
  exact sqdiag_sum_over_BWZAdjointSupport_classifiedValue_eq_kernelCard_mul_rootCoeffSign
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiag_survivor_sum_eq_CKernelCard_mul_BWZAdjointRootCoeffSignSum
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      sqdiagBWZAdjointRootCoeffSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  unfold sqdiagBWZAdjointRootCoeffSignSum
  exact sqdiag_survivor_sum_eq_kernelCard_mul_BWZAdjointSupport_rootCoeffSign
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiagKCAdjointKernelCard_mul_survivor_sum_eq_CKernelCard_mul_BWZAdjointWitnessFiberTotalSignSum
    {n a b c d : ℕ} [NeZero n] :
    sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      (∑ x : Surviving_yzw n a b c d,
        bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      sqdiagBWZAdjointWitnessFiberTotalSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [sqdiag_survivor_sum_eq_CKernelCard_mul_BWZAdjointRootCoeffSignSum
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  rw [sqdiagBWZAdjointWitnessFiberTotalSignSum_eq_KCAdjointKernelCard_mul_rootCoeffSignSum
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  ring

theorem sqdiagKCAdjointKernelCard_mul_survivor_sum_eq_CKernelCard_mul_BWAAdjointGraphRootSignSum
    {n a b c d : ℕ} [NeZero n] :
    sqdiagKCAdjointKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      (∑ x : Surviving_yzw n a b c d,
        bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) *
      sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [sqdiagKCAdjointKernelCard_mul_survivor_sum_eq_CKernelCard_mul_BWZAdjointWitnessFiberTotalSignSum
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  rw [← sqdiagBWAAdjointGraphRootSignSum_eq_BWZAdjointWitnessFiberTotalSignSum
    (n := n) (a := a) (b := b) (c := c) (d := d)]

theorem sqdiagCFiberValue_eq_kernelCard_of_mem_SquareCombinedKernel
    {n a b c d : ℕ} [NeZero n]
    (x : SquareCombinedKernel n a b c d) :
    sqdiagCFiberValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 =
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) :=
  sqdiagCFiberValue_eq_kernelCard_of_BWZCompatSupport
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagBWZCompatSupportOfSquareCombinedKernel
      (n := n) (a := a) (b := b) (c := c) (d := d) x)

theorem sqdiag_sum_over_BWZCompatSupport_fiberValue
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : sqdiagBWZCompatSupport n a b c d,
      sqdiagCFiberValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
      =
    (Nat.card (sqdiagBWZCompatSupport n a b c d) : ℤ) *
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
  classical
  calc
    (∑ x : sqdiagBWZCompatSupport n a b c d,
      sqdiagCFiberValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
        =
      ∑ _x : sqdiagBWZCompatSupport n a b c d,
        sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact sqdiagCFiberValue_eq_kernelCard_of_BWZCompatSupport
            (n := n) (a := a) (b := b) (c := c) (d := d) x
    _ =
      (Nat.card (sqdiagBWZCompatSupport n a b c d) : ℤ) *
        sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [Nat.card_eq_fintype_card]

theorem sqdiag_sum_over_SquareCombinedKernel_fiberValue
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : SquareCombinedKernel n a b c d,
      sqdiagCFiberValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
      =
    (Nat.card (SquareCombinedKernel n a b c d) : ℤ) *
      sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
  classical
  calc
    (∑ x : SquareCombinedKernel n a b c d,
      sqdiagCFiberValue
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
        =
      ∑ _x : SquareCombinedKernel n a b c d,
        sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact sqdiagCFiberValue_eq_kernelCard_of_mem_SquareCombinedKernel
            (n := n) (a := a) (b := b) (c := c) (d := d) x
    _ =
      (Nat.card (SquareCombinedKernel n a b c d) : ℤ) *
        sqdiagCKernelCardZ (n := n) (a := a) (b := b) (c := c) (d := d) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [Nat.card_eq_fintype_card]

end SquareDiagonal
end Core4loop
