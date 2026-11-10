import Core4loop.TriangleLeaf.E5CompatibleQuadratic
import Core4loop.TriangleLeaf.CompatibleSourceCore
import Core4loop.LinearSignSum

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private noncomputable def q1LeftLinear
    {n a b c d : ℕ} [NeZero n] (C : CFun4 n a b d) :
    BFun4 n a c d →ₗ[F] F where
  toFun B := Q1 B C
  map_add' B B' := by
    unfold Q1 betaB gammaB deltaC etaC
    simp only [Pi.add_apply]
    simp_rw [add_mul, Finset.sum_add_distrib]
    abel
  map_smul' r B := by
    unfold Q1 betaB gammaB deltaC etaC
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    simp only [mul_assoc, mul_add, Finset.mul_sum]

private noncomputable def q1RightLinear
    {n a b c d : ℕ} [NeZero n] (B : BFun4 n a c d) :
    CFun4 n a b d →ₗ[F] F where
  toFun C := Q1 B C
  map_add' C C' := by
    unfold Q1 betaB gammaB deltaC etaC
    simp only [Pi.add_apply]
    simp_rw [mul_add, Finset.sum_add_distrib]
    abel
  map_smul' r C := by
    unfold Q1 betaB gammaB deltaC etaC
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    simp only [mul_left_comm, mul_add, Finset.mul_sum]

private noncomputable def q1Bilinear
    {n a b c d : ℕ} [NeZero n] :
    BFun4 n a c d →ₗ[F] CFun4 n a b d →ₗ[F] F :=
  LinearMap.mk₂ F Q1
    (fun B B' C => (q1LeftLinear C).map_add B B')
    (fun r B C => (q1LeftLinear C).map_smul r B)
    (fun B C C' => (q1RightLinear B).map_add C C')
    (fun r B C => (q1RightLinear B).map_smul r C)

noncomputable def triangleLeafCompatiblePolar
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafCompatibleSubmodule n a b c d →ₗ[F]
      triangleLeafCompatibleSubmodule n a b c d →ₗ[F] F := by
  let bProj :
      triangleLeafCompatibleSubmodule n a b c d →ₗ[F] BFun4 n a c d :=
    (LinearMap.fst F (BFun4 n a c d) (CFun4 n a b d)).comp
      (triangleLeafCompatibleSubmodule n a b c d).subtype
  let cProj :
      triangleLeafCompatibleSubmodule n a b c d →ₗ[F] CFun4 n a b d :=
    (LinearMap.snd F (BFun4 n a c d) (CFun4 n a b d)).comp
      (triangleLeafCompatibleSubmodule n a b c d).subtype
  let direct :=
    (q1Bilinear (n := n) (a := a) (b := b) (c := c) (d := d)).compl₁₂
      bProj cProj
  exact direct + direct.flip

@[simp] theorem triangleLeafCompatiblePolar_apply
    {n a b c d : ℕ} [NeZero n]
    (X Y : triangleLeafCompatibleSubmodule n a b c d) :
    triangleLeafCompatiblePolar X Y =
      Q1 X.1.1 Y.1.2 + Q1 Y.1.1 X.1.2 := rfl

set_option maxHeartbeats 1000000 in
theorem triangleLeafCompatibleQ_add
    {n a b c d : ℕ} [NeZero n]
    (X Y : triangleLeafCompatibleSubmodule n a b c d) :
    triangleLeafCompatibleQ (X + Y) =
      triangleLeafCompatibleQ X + triangleLeafCompatibleQ Y +
        triangleLeafCompatiblePolar X Y := by
  change
    Q1 (X.1.1 + Y.1.1) (X.1.2 + Y.1.2) =
      Q1 X.1.1 X.1.2 + Q1 Y.1.1 Y.1.2 +
        (Q1 X.1.1 Y.1.2 + Q1 Y.1.1 X.1.2)
  have hleft :
      Q1 (X.1.1 + Y.1.1) (X.1.2 + Y.1.2) =
        Q1 X.1.1 (X.1.2 + Y.1.2) +
          Q1 Y.1.1 (X.1.2 + Y.1.2) :=
    (q1LeftLinear (X.1.2 + Y.1.2)).map_add X.1.1 Y.1.1
  have hrightX :
      Q1 X.1.1 (X.1.2 + Y.1.2) =
        Q1 X.1.1 X.1.2 + Q1 X.1.1 Y.1.2 :=
    (q1RightLinear X.1.1).map_add X.1.2 Y.1.2
  have hrightY :
      Q1 Y.1.1 (X.1.2 + Y.1.2) =
        Q1 Y.1.1 X.1.2 + Q1 Y.1.1 Y.1.2 :=
    (q1RightLinear Y.1.1).map_add X.1.2 Y.1.2
  rw [hleft, hrightX, hrightY]
  ring

noncomputable def triangleLeafBOnlyPolarMap
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafCompatibleSubmodule n a b c d →ₗ[F]
      triangleLeafBOnly n a b c d →ₗ[F] F where
  toFun X :=
    (triangleLeafCompatiblePolar X).comp
      (triangleLeafBOnly n a b c d).subtype
  map_add' X Y := by ext Z; simp
  map_smul' r X := by ext Z; simp

abbrev triangleLeafE5LB (n a b c d : ℕ) [NeZero n] :=
  LinearMap.ker
    (triangleLeafBOnlyPolarMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def scalarYEquiv
    {n : ℕ} [NeZero n] : I n ≃ YVec n 1 where
  toFun t := vecSingle (by omega) t
  invFun y := y 0
  left_inv t := by simp [vecSingle]
  right_inv y := by
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp [vecSingle]

@[simp] theorem vecSum_scalarYEquiv
    {n : ℕ} [NeZero n] (t : I n) :
    vecSum (scalarYEquiv t) = t :=
  vecSum_vecSingle (by omega) t

abbrev triangleLeafE5YOf
    {n : ℕ} [NeZero n] (t : I n) : YVec n 1 :=
  scalarYEquiv t

private theorem sum_y_eq_sum_triangleLeafE5YOf
    {n : ℕ} [NeZero n]
    {M : Type*} [AddCommMonoid M]
    (f : YVec n 1 → M) :
    (∑ y : YVec n 1, f y) =
      ∑ t : I n, f (triangleLeafE5YOf t) := by
  simpa [triangleLeafE5YOf] using
    (Equiv.sum_comp scalarYEquiv f).symm

noncomputable def triangleLeafE5BCoeff
    {n a c d : ℕ} [NeZero n]
    (C : CFun4 n a 1 d)
    (p : PVec n a) (t : I n) (z : ZVec n c) (w : WVec n d) : F :=
  C p (triangleLeafE5YOf t) (vecSum z) w +
    C p (triangleLeafE5YOf (t - 1)) (vecSum z + 1) w

private theorem sum_t_shift_for_triangleLeafE5BCoeff
    {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a 1 d)
    (p : PVec n a) (z : ZVec n c) (w : WVec n d) :
    (∑ t : I n,
        B p (t + 1) z w *
          C p (triangleLeafE5YOf t) (vecSum z + 1) w)
      =
    ∑ t : I n,
      B p t z w *
        C p (triangleLeafE5YOf (t - 1)) (vecSum z + 1) w := by
  let g : I n → F :=
    fun t =>
      B p t z w *
        C p (triangleLeafE5YOf (t - 1)) (vecSum z + 1) w
  have h := Equiv.sum_comp (Equiv.addRight (1 : I n)) g
  simpa [g, sub_eq_add_neg, add_assoc] using h

private theorem Q1_p_eq_sum_B_mul_triangleLeafE5BCoeff
    {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a 1 d)
    (p : PVec n a) :
    (∑ y : YVec n 1, ∑ z : ZVec n c, ∑ w : WVec n d,
        (betaB B p y z w * deltaC C p y z w +
          gammaB B p y z w * etaC C p y z w))
      =
    ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
      B p t z w * triangleLeafE5BCoeff C p t z w := by
  rw [sum_y_eq_sum_triangleLeafE5YOf]
  simp only [betaB, gammaB, deltaC, etaC, vecSum_scalarYEquiv]
  calc
    (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        (B p t z w * C p (triangleLeafE5YOf t) (vecSum z) w +
          B p (t + 1) z w *
            C p (triangleLeafE5YOf t) (vecSum z + 1) w))
        =
      (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        B p t z w * C p (triangleLeafE5YOf t) (vecSum z) w) +
      (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        B p (t + 1) z w *
          C p (triangleLeafE5YOf t) (vecSum z + 1) w) := by
          simp_rw [Finset.sum_add_distrib]
    _ =
      (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        B p t z w * C p (triangleLeafE5YOf t) (vecSum z) w) +
      (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        B p t z w *
          C p (triangleLeafE5YOf (t - 1)) (vecSum z + 1) w) := by
          congr 1
          calc
            (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
                B p (t + 1) z w *
                  C p (triangleLeafE5YOf t) (vecSum z + 1) w)
                =
              ∑ z : ZVec n c, ∑ w : WVec n d, ∑ t : I n,
                B p (t + 1) z w *
                  C p (triangleLeafE5YOf t) (vecSum z + 1) w := by
                  rw [Finset.sum_comm]
                  congr 1
                  funext z
                  rw [Finset.sum_comm]
            _ =
              ∑ z : ZVec n c, ∑ w : WVec n d, ∑ t : I n,
                B p t z w *
                  C p (triangleLeafE5YOf (t - 1)) (vecSum z + 1) w := by
                  refine Finset.sum_congr rfl ?_
                  intro z _
                  refine Finset.sum_congr rfl ?_
                  intro w _
                  exact sum_t_shift_for_triangleLeafE5BCoeff B C p z w
            _ =
              ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
                B p t z w *
                  C p (triangleLeafE5YOf (t - 1)) (vecSum z + 1) w := by
                  calc
                    (∑ z : ZVec n c, ∑ w : WVec n d, ∑ t : I n,
                        B p t z w *
                          C p (triangleLeafE5YOf (t - 1))
                            (vecSum z + 1) w)
                        =
                      ∑ z : ZVec n c, ∑ t : I n, ∑ w : WVec n d,
                        B p t z w *
                          C p (triangleLeafE5YOf (t - 1))
                            (vecSum z + 1) w := by
                          refine Finset.sum_congr rfl ?_
                          intro z _
                          rw [Finset.sum_comm]
                    _ = _ := by rw [Finset.sum_comm]
    _ =
      ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        (B p t z w * C p (triangleLeafE5YOf t) (vecSum z) w +
          B p t z w *
            C p (triangleLeafE5YOf (t - 1)) (vecSum z + 1) w) := by
            simp_rw [Finset.sum_add_distrib]
    _ =
      ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        B p t z w * triangleLeafE5BCoeff C p t z w := by
            refine Finset.sum_congr rfl ?_
            intro t _
            refine Finset.sum_congr rfl ?_
            intro z _
            refine Finset.sum_congr rfl ?_
            intro w _
            simp [triangleLeafE5BCoeff]
            ring

theorem Q1_eq_sum_B_mul_triangleLeafE5BCoeff
    {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a 1 d) :
    Q1 B C =
      ∑ p : PVec n a, ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        B p t z w * triangleLeafE5BCoeff C p t z w := by
  unfold Q1
  refine Finset.sum_congr rfl ?_
  intro p _
  exact Q1_p_eq_sum_B_mul_triangleLeafE5BCoeff B C p

private noncomputable def triangleLeafE5BPoint
    {n a c d : ℕ} [NeZero n]
    (p₀ : PVec n a) (t₀ : I n) (z₀ : ZVec n c) (w₀ : WVec n d) :
    BFun4 n a c d :=
  fun p t z w =>
    if p = p₀ ∧ t = t₀ ∧ z = z₀ ∧ w = w₀ then 1 else 0

noncomputable def triangleLeafE5BPulse
    {n a c d : ℕ} [NeZero n]
    (p₀ : PVec n a) (t₀ : I n) (z₀ : ZVec n c) (w₀ : WVec n d) :
    BFun4 n a c d :=
  triangleLeafE5BPoint p₀ t₀ z₀ w₀ +
    triangleLeafE5BPoint zeroVec t₀ z₀ w₀

private theorem sum_p_triangleLeafE5BPoint
    {n a c d : ℕ} [NeZero n]
    (p₀ : PVec n a) (t₀ t : I n) (z₀ z : ZVec n c)
    (w₀ w : WVec n d) :
    (∑ p : PVec n a, triangleLeafE5BPoint p₀ t₀ z₀ w₀ p t z w)
      =
    if t = t₀ ∧ z = z₀ ∧ w = w₀ then 1 else 0 := by
  classical
  by_cases hrest : t = t₀ ∧ z = z₀ ∧ w = w₀
  · rcases hrest with ⟨rfl, rfl, rfl⟩
    simp [triangleLeafE5BPoint]
  · simp only [triangleLeafE5BPoint]
    have hp :
        ∀ p : PVec n a,
          ¬(p = p₀ ∧ t = t₀ ∧ z = z₀ ∧ w = w₀) := by
      intro p h
      exact hrest ⟨h.2.1, h.2.2.1, h.2.2.2⟩
    simp [hrest]

private theorem sum_p_triangleLeafE5BPulse_eq_zero
    {n a c d : ℕ} [NeZero n]
    (p₀ : PVec n a) (t₀ t : I n) (z₀ z : ZVec n c)
    (w₀ w : WVec n d) :
    (∑ p : PVec n a, triangleLeafE5BPulse p₀ t₀ z₀ w₀ p t z w) = 0 := by
  rw [show triangleLeafE5BPulse p₀ t₀ z₀ w₀ =
      triangleLeafE5BPoint p₀ t₀ z₀ w₀ +
        triangleLeafE5BPoint zeroVec t₀ z₀ w₀ by rfl]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [sum_p_triangleLeafE5BPoint, sum_p_triangleLeafE5BPoint]
  by_cases hrest : t = t₀ ∧ z = z₀ ∧ w = w₀
  · simp [hrest, F_add_self]
  · simp [hrest]

theorem KBMap_triangleLeafE5BPulse_eq_zero
    {n a c d : ℕ} [NeZero n]
    (p₀ : PVec n a) (t₀ : I n) (z₀ : ZVec n c) (w₀ : WVec n d) :
    KBMap (n := n) (a := a) (b := 1) (c := c) (d := d)
      (triangleLeafE5BPulse p₀ t₀ z₀ w₀) = 0 := by
  funext y z w
  unfold KBMap dyB betaB gammaB
  change
    (∑ p : PVec n a,
      (triangleLeafE5BPulse p₀ t₀ z₀ w₀ p (vecSum y) z w +
        triangleLeafE5BPulse p₀ t₀ z₀ w₀ p (vecSum y + 1) z w)) = 0
  rw [Finset.sum_add_distrib]
  rw [sum_p_triangleLeafE5BPulse_eq_zero,
    sum_p_triangleLeafE5BPulse_eq_zero]
  simp

private theorem sum_triangleLeafE5BPoint_mul
    {n a c d : ℕ} [NeZero n]
    (p₀ : PVec n a) (t₀ : I n) (z₀ : ZVec n c) (w₀ : WVec n d)
    (f : PVec n a → I n → ZVec n c → WVec n d → F) :
    (∑ p : PVec n a, ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
      triangleLeafE5BPoint p₀ t₀ z₀ w₀ p t z w * f p t z w)
      =
    f p₀ t₀ z₀ w₀ := by
  classical
  rw [Finset.sum_eq_single p₀]
  · rw [Finset.sum_eq_single t₀]
    · rw [Finset.sum_eq_single z₀]
      · rw [Finset.sum_eq_single w₀]
        · simp [triangleLeafE5BPoint]
        · intro w _ hw
          simp [triangleLeafE5BPoint, hw]
        · simp
      · intro z _ hz
        simp [triangleLeafE5BPoint, hz]
      · simp
    · intro t _ ht
      simp [triangleLeafE5BPoint, ht]
    · simp
  · intro p _ hp
    simp [triangleLeafE5BPoint, hp]
  · simp

private theorem Q1_triangleLeafE5BPulse
    {n a c d : ℕ} [NeZero n]
    (C : CFun4 n a 1 d)
    (p₀ : PVec n a) (t₀ : I n) (z₀ : ZVec n c) (w₀ : WVec n d) :
    Q1 (triangleLeafE5BPulse p₀ t₀ z₀ w₀) C =
      triangleLeafE5BCoeff C p₀ t₀ z₀ w₀ +
        triangleLeafE5BCoeff C zeroVec t₀ z₀ w₀ := by
  rw [Q1_eq_sum_B_mul_triangleLeafE5BCoeff]
  change
    (∑ p : PVec n a, ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
      (triangleLeafE5BPoint p₀ t₀ z₀ w₀ p t z w +
        triangleLeafE5BPoint zeroVec t₀ z₀ w₀ p t z w) *
          triangleLeafE5BCoeff C p t z w)
      =
    triangleLeafE5BCoeff C p₀ t₀ z₀ w₀ +
      triangleLeafE5BCoeff C zeroVec t₀ z₀ w₀
  calc
    (∑ p : PVec n a, ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
      (triangleLeafE5BPoint p₀ t₀ z₀ w₀ p t z w +
        triangleLeafE5BPoint zeroVec t₀ z₀ w₀ p t z w) *
          triangleLeafE5BCoeff C p t z w)
        =
      (∑ p : PVec n a, ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        triangleLeafE5BPoint p₀ t₀ z₀ w₀ p t z w *
          triangleLeafE5BCoeff C p t z w) +
      (∑ p : PVec n a, ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        triangleLeafE5BPoint zeroVec t₀ z₀ w₀ p t z w *
          triangleLeafE5BCoeff C p t z w) := by
          simp_rw [add_mul, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_triangleLeafE5BPoint_mul, sum_triangleLeafE5BPoint_mul]

theorem triangleLeafE5BCoeff_eq_zeroVec
    {n a c d : ℕ} [NeZero n]
    (X : triangleLeafE5LB n a 1 c d)
    (p : PVec n a) (t : I n) (z : ZVec n c) (w : WVec n d) :
    triangleLeafE5BCoeff X.1.1.2 p t z w =
      triangleLeafE5BCoeff X.1.1.2 zeroVec t z w := by
  let pulseV : triangleLeafCompatibleSubmodule n a 1 c d :=
    ⟨(triangleLeafE5BPulse p t z w, 0), by
      apply (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := 1) (c := c) (d := d)
        (triangleLeafE5BPulse p t z w, 0)).mpr
      rw [KBMap_triangleLeafE5BPulse_eq_zero,
        LinearMap.map_zero, zero_add]
      exact (WDiffSpace
        (n := n) (b := 1) (c := c) (d := d)).zero_mem⟩
  let pulseBOnly : triangleLeafBOnly n a 1 c d :=
    ⟨pulseV, by rfl⟩
  have hmap :
      triangleLeafBOnlyPolarMap
        (n := n) (a := a) (b := 1) (c := c) (d := d) X.1 = 0 :=
    LinearMap.mem_ker.mp X.2
  have hpoint :=
    DFunLike.congr_fun hmap pulseBOnly
  change
    Q1 X.1.1.1 (0 : CFun4 n a 1 d) +
        Q1 (triangleLeafE5BPulse p t z w) X.1.1.2 = 0 at hpoint
  have hz : Q1 X.1.1.1 (0 : CFun4 n a 1 d) = 0 :=
    (q1RightLinear X.1.1.1).map_zero
  have hQzero :
      Q1 (triangleLeafE5BPulse p t z w) X.1.1.2 = 0 := by
    rw [hz, zero_add] at hpoint
    exact hpoint
  rw [Q1_triangleLeafE5BPulse] at hQzero
  exact (add_eq_zero_iff_eq_of_F_module _ _).mp hQzero

noncomputable def triangleLeafE5Cbar
    {n a d : ℕ} [NeZero n]
    (C : CFun4 n a 1 d) (t r : I n) (w : WVec n d) : F :=
  ∑ p : PVec n a, C p (triangleLeafE5YOf t) r w

theorem triangleLeafE5Cbar_diagonal
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c)
    (X : triangleLeafE5LB n a 1 c d)
    (t r : I n) (w : WVec n d) :
    triangleLeafE5Cbar X.1.1.2 t r w =
      triangleLeafE5Cbar X.1.1.2 (t - 1) (r + 1) w := by
  let z : ZVec n c := vecSingle hc r
  have hz : vecSum z = r := vecSum_vecSingle hc r
  have hsum :
      (∑ p : PVec n a,
          triangleLeafE5BCoeff X.1.1.2 p t z w) =
        ∑ _p : PVec n a,
          triangleLeafE5BCoeff X.1.1.2 zeroVec t z w := by
    refine Finset.sum_congr rfl ?_
    intro p _
    exact triangleLeafE5BCoeff_eq_zeroVec X p t z w
  have hcard :
      (Fintype.card (PVec n a) : F) = 0 := by
    exact natCast_card_vec_eq_zero_of_even_pos hn (by omega)
  have hrhs :
      (∑ _p : PVec n a,
          triangleLeafE5BCoeff X.1.1.2 zeroVec t z w) = 0 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    change
      (Fintype.card (PVec n a) : F) *
          triangleLeafE5BCoeff X.1.1.2 zeroVec t z w = 0
    rw [hcard, zero_mul]
  rw [hrhs] at hsum
  change
    (∑ p : PVec n a,
        (X.1.1.2 p (triangleLeafE5YOf t) (vecSum z) w +
          X.1.1.2 p (triangleLeafE5YOf (t - 1))
            (vecSum z + 1) w)) = 0 at hsum
  rw [Finset.sum_add_distrib] at hsum
  change
    triangleLeafE5Cbar X.1.1.2 t (vecSum z) w +
      triangleLeafE5Cbar X.1.1.2 (t - 1) (vecSum z + 1) w = 0 at hsum
  rw [hz] at hsum
  exact (add_eq_zero_iff_eq_of_F_module _ _).mp hsum

noncomputable def triangleLeafE5BCLift
    {n a c d : ℕ} [NeZero n]
    (C : CFun4 n a 1 d) :
    BFun4 n a c d :=
  fun p t z w =>
    if p = (zeroVec : PVec n a)
    then triangleLeafE5Cbar C t (vecSum z) w
    else 0

theorem KBMap_triangleLeafE5BCLift_eq_KCMap
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c)
    (X : triangleLeafE5LB n a 1 c d) :
    KBMap (n := n) (a := a) (b := 1) (c := c) (d := d)
        (triangleLeafE5BCLift (c := c) X.1.1.2)
      =
    KCMap (n := n) (a := a) (b := 1) (c := c) (d := d)
        X.1.1.2 := by
  classical
  have hsum (t : I n) (z : ZVec n c) (w : WVec n d) :
      (∑ p : PVec n a,
          triangleLeafE5BCLift (c := c) X.1.1.2 p t z w) =
        triangleLeafE5Cbar X.1.1.2 t (vecSum z) w := by
    rw [Finset.sum_eq_single (zeroVec : PVec n a)]
    · simp [triangleLeafE5BCLift]
    · intro p _ hp
      simp [triangleLeafE5BCLift, hp]
    · simp
  funext y z w
  let t : I n := vecSum y
  let r : I n := vecSum z
  have hy : triangleLeafE5YOf t = y := by
    have h := (scalarYEquiv (n := n)).apply_symm_apply y
    change triangleLeafE5YOf (y 0) = y at h
    have hsum : vecSum y = y 0 := by simp [vecSum]
    dsimp [t]
    rw [hsum]
    exact h
  have hstep :
      triangleLeafE5Cbar X.1.1.2 (t + 1) r w =
        triangleLeafE5Cbar X.1.1.2 t (r + 1) w := by
    have h :=
      triangleLeafE5Cbar_diagonal hn ha2 hc X (t + 1) r w
    simpa [sub_eq_add_neg, add_assoc] using h
  change
    (∑ p : PVec n a,
      (triangleLeafE5BCLift (c := c) X.1.1.2 p t z w +
        triangleLeafE5BCLift (c := c) X.1.1.2 p (t + 1) z w))
      =
    ∑ p : PVec n a,
      (X.1.1.2 p y r w + X.1.1.2 p y (r + 1) w)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsum, hsum]
  change
    triangleLeafE5Cbar X.1.1.2 t r w +
        triangleLeafE5Cbar X.1.1.2 (t + 1) r w =
      (∑ p : PVec n a, X.1.1.2 p y r w) +
        ∑ p : PVec n a, X.1.1.2 p y (r + 1) w
  rw [hstep]
  simp only [triangleLeafE5Cbar, hy]

private theorem triangleLeafE5_sum_tzw_shift
    {n c d : ℕ} [NeZero n] (hc : 0 < c)
    {M : Type*} [AddCommMonoid M]
    (f : I n → ZVec n c → WVec n d → M) :
    (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        f (t - 1) (shiftVec z (⟨0, hc⟩ : Fin c) 1) w)
      =
    ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d, f t z w := by
  let e :
      (I n × (ZVec n c × WVec n d)) ≃
        (I n × (ZVec n c × WVec n d)) :=
    Equiv.prodCongr
      (Equiv.addRight (-(1 : I n)))
      (Equiv.prodCongr
        (shiftVecEquiv (⟨0, hc⟩ : Fin c) (1 : I n))
        (Equiv.refl (WVec n d)))
  let g : I n × (ZVec n c × WVec n d) → M :=
    fun x => f x.1 x.2.1 x.2.2
  have h := Equiv.sum_comp e g
  simpa [g, e, sub_eq_add_neg, Fintype.sum_prod_type] using h

theorem Q1_triangleLeafE5BCLift_eq_zero
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c)
    (X : triangleLeafE5LB n a 1 c d) :
    Q1 (triangleLeafE5BCLift (c := c) X.1.1.2) X.1.1.2 = 0 := by
  rw [Q1_eq_sum_B_mul_triangleLeafE5BCoeff]
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · simp only [triangleLeafE5BCLift, if_pos, triangleLeafE5BCoeff]
    let f : I n → ZVec n c → WVec n d → F :=
      fun t z w =>
        triangleLeafE5Cbar X.1.1.2 t (vecSum z) w *
          X.1.1.2 zeroVec (triangleLeafE5YOf t) (vecSum z) w
    have hsecond :
        (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
          triangleLeafE5Cbar X.1.1.2 t (vecSum z) w *
            X.1.1.2 zeroVec (triangleLeafE5YOf (t - 1))
              (vecSum z + 1) w)
          =
        ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
          triangleLeafE5Cbar X.1.1.2 t (vecSum z) w *
            X.1.1.2 zeroVec (triangleLeafE5YOf t)
              (vecSum z) w := by
      calc
        (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
          triangleLeafE5Cbar X.1.1.2 t (vecSum z) w *
            X.1.1.2 zeroVec (triangleLeafE5YOf (t - 1))
              (vecSum z + 1) w)
            =
          ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
            f (t - 1) (shiftVec z (⟨0, hc⟩ : Fin c) 1) w := by
              refine Finset.sum_congr rfl ?_
              intro t _
              refine Finset.sum_congr rfl ?_
              intro z _
              refine Finset.sum_congr rfl ?_
              intro w _
              simp only [f, vecSum_shiftVec]
              rw [← triangleLeafE5Cbar_diagonal
                hn ha2 hc X t (vecSum z) w]
        _ = ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
              f t z w :=
          triangleLeafE5_sum_tzw_shift hc f
        _ = _ := rfl
    calc
      (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        triangleLeafE5Cbar X.1.1.2 t (vecSum z) w *
          (X.1.1.2 zeroVec (triangleLeafE5YOf t) (vecSum z) w +
            X.1.1.2 zeroVec (triangleLeafE5YOf (t - 1))
              (vecSum z + 1) w))
          =
        (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
          triangleLeafE5Cbar X.1.1.2 t (vecSum z) w *
            X.1.1.2 zeroVec (triangleLeafE5YOf t) (vecSum z) w) +
        (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
          triangleLeafE5Cbar X.1.1.2 t (vecSum z) w *
            X.1.1.2 zeroVec (triangleLeafE5YOf (t - 1))
              (vecSum z + 1) w) := by
              simp_rw [mul_add, Finset.sum_add_distrib]
      _ =
        (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
          triangleLeafE5Cbar X.1.1.2 t (vecSum z) w *
            X.1.1.2 zeroVec (triangleLeafE5YOf t) (vecSum z) w) +
        (∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
          triangleLeafE5Cbar X.1.1.2 t (vecSum z) w *
            X.1.1.2 zeroVec (triangleLeafE5YOf t)
              (vecSum z) w) := by rw [hsecond]
      _ = 0 := F_add_self _
  · intro p _ hp
    simp [triangleLeafE5BCLift, hp]
  · simp

theorem triangleLeafE5LB_q_zero_b_eq_one
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c) (_hd2 : 2 ≤ d)
    (X : triangleLeafE5LB n a 1 c d) :
    triangleLeafCompatibleQ X.1 = 0 := by
  let YV : triangleLeafCompatibleSubmodule n a 1 c d :=
    ⟨(X.1.1.1 +
        triangleLeafE5BCLift (c := c) X.1.1.2,
      0), by
        apply (triangleLeafCompatibleSubmodule_carrier_iff
          (n := n) (a := a) (b := 1) (c := c) (d := d)
          (X.1.1.1 +
              triangleLeafE5BCLift (c := c) X.1.1.2,
            0)).mpr
        rw [LinearMap.map_add,
          KBMap_triangleLeafE5BCLift_eq_KCMap hn ha2 hc X,
          LinearMap.map_zero, add_zero]
        exact
          (triangleLeafCompatibleSubmodule_carrier_iff
            (n := n) (a := a) (b := 1) (c := c) (d := d)
            X.1.1).mp X.1.2⟩
  let Y : triangleLeafBOnly n a 1 c d :=
    ⟨YV, by rfl⟩
  have hmap :
      triangleLeafBOnlyPolarMap
        (n := n) (a := a) (b := 1) (c := c) (d := d) X.1 = 0 :=
    LinearMap.mem_ker.mp X.2
  have hpoint := DFunLike.congr_fun hmap Y
  change
    Q1 X.1.1.1 (0 : CFun4 n a 1 d) +
      Q1
        (X.1.1.1 + triangleLeafE5BCLift (c := c) X.1.1.2)
        X.1.1.2 = 0 at hpoint
  have hzero : Q1 X.1.1.1 (0 : CFun4 n a 1 d) = 0 :=
    (q1RightLinear X.1.1.1).map_zero
  rw [hzero, zero_add] at hpoint
  have hadd :
      Q1
          (X.1.1.1 + triangleLeafE5BCLift (c := c) X.1.1.2)
          X.1.1.2 =
        Q1 X.1.1.1 X.1.1.2 +
          Q1 (triangleLeafE5BCLift (c := c) X.1.1.2) X.1.1.2 :=
    (q1LeftLinear X.1.1.2).map_add
      X.1.1.1 (triangleLeafE5BCLift (c := c) X.1.1.2)
  rw [hadd, Q1_triangleLeafE5BCLift_eq_zero hn ha2 hc X,
    add_zero] at hpoint
  exact hpoint

theorem triangleLeafE5LB_selfDual_b_eq_one
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c) (hd2 : 2 ≤ d) :
    ∀ x : triangleLeafCompatibleSubmodule n a 1 c d,
      ((triangleLeafCompatiblePolar x).comp
          (triangleLeafE5LB n a 1 c d).subtype = 0 ↔
        x ∈ triangleLeafE5LB n a 1 c d) := by
  have hBOnly_le_LB :
      triangleLeafBOnly n a 1 c d ≤ triangleLeafE5LB n a 1 c d := by
    intro y hy
    apply LinearMap.mem_ker.mpr
    ext z
    have hyC := LinearMap.mem_ker.mp hy
    have hzC := LinearMap.mem_ker.mp z.2
    change y.1.2 = 0 at hyC
    change z.1.1.2 = 0 at hzC
    change Q1 y.1.1 z.1.1.2 + Q1 z.1.1.1 y.1.2 = 0
    rw [hyC, hzC]
    have h₁ : Q1 y.1.1 (0 : CFun4 n a 1 d) = 0 :=
      (q1RightLinear y.1.1).map_zero
    have h₂ : Q1 z.1.1.1 (0 : CFun4 n a 1 d) = 0 :=
      (q1RightLinear z.1.1.1).map_zero
    rw [h₁, h₂, add_zero]
  intro x
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    ext y
    let yL : triangleLeafE5LB n a 1 c d :=
      ⟨y.1, hBOnly_le_LB y.2⟩
    have hpoint := DFunLike.congr_fun hx yL
    change triangleLeafCompatiblePolar x y.1 = 0 at hpoint
    exact hpoint
  · intro hx
    ext y
    let xL : triangleLeafE5LB n a 1 c d := ⟨x, hx⟩
    have hqX := triangleLeafE5LB_q_zero_b_eq_one hn ha2 hc hd2 xL
    have hqY := triangleLeafE5LB_q_zero_b_eq_one hn ha2 hc hd2 y
    have hqXY :=
      triangleLeafE5LB_q_zero_b_eq_one hn ha2 hc hd2 (xL + y)
    have hadd := triangleLeafCompatibleQ_add xL.1 y.1
    have hqXY' :
        triangleLeafCompatibleQ (xL.1 + y.1) = 0 := by
      simpa using hqXY
    rw [hqXY', hqX, hqY] at hadd
    have hp : triangleLeafCompatiblePolar xL.1 y.1 = 0 := by
      simpa using hadd.symm
    change triangleLeafCompatiblePolar x y.1 = 0
    exact hp

/-! Step 16: literal admissible-C annihilator and pointed-`p` coordinates. -/

noncomputable def triangleLeafE5CadmMap
    {n a c d : ℕ} [NeZero n] :
    CFun4 n a 1 d →ₗ[F] triangleLeafBOnly n a 1 c d →ₗ[F] F where
  toFun C :=
    { toFun := fun Y => Q1 Y.1.1.1 C
      map_add' := fun Y Z => (q1LeftLinear C).map_add Y.1.1.1 Z.1.1.1
      map_smul' := fun x Y => (q1LeftLinear C).map_smul x Y.1.1.1 }
  map_add' C D := by
    ext Y
    exact (q1RightLinear Y.1.1.1).map_add C D
  map_smul' x C := by
    ext Y
    exact (q1RightLinear Y.1.1.1).map_smul x C

abbrev TriangleLeafE5Cadm
    (n a c d : ℕ) [NeZero n] :=
  LinearMap.ker
    (triangleLeafE5CadmMap
      (n := n) (a := a) (c := c) (d := d))

abbrev TriangleLeafE5NonzeroPVec
    (n a : ℕ) :=
  {p : PVec n a // p ≠ zeroVec}

abbrev TriangleLeafE5PointedPart
    (n a d : ℕ) :=
  TriangleLeafE5NonzeroPVec n a → I n → WVec n d → F

abbrev TriangleLeafE5BaseC (n d : ℕ) :=
  I n → I n → WVec n d → F

theorem triangleLeafE5Cadm_BCoeff_eq_zeroVec
    {n a c d : ℕ} [NeZero n]
    (C : TriangleLeafE5Cadm n a c d)
    (p : PVec n a) (t : I n) (z : ZVec n c) (w : WVec n d) :
    triangleLeafE5BCoeff C.1 p t z w =
      triangleLeafE5BCoeff C.1 zeroVec t z w := by
  let pulseV : triangleLeafCompatibleSubmodule n a 1 c d :=
    ⟨(triangleLeafE5BPulse p t z w, 0), by
      apply (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := 1) (c := c) (d := d)
        (triangleLeafE5BPulse p t z w, 0)).mpr
      rw [KBMap_triangleLeafE5BPulse_eq_zero,
        LinearMap.map_zero, zero_add]
      exact (WDiffSpace
        (n := n) (b := 1) (c := c) (d := d)).zero_mem⟩
  let pulseBOnly : triangleLeafBOnly n a 1 c d :=
    ⟨pulseV, by rfl⟩
  have hmap :
      triangleLeafE5CadmMap C.1 = 0 :=
    LinearMap.mem_ker.mp C.2
  have hpoint := DFunLike.congr_fun hmap pulseBOnly
  change Q1 (triangleLeafE5BPulse p t z w) C.1 = 0 at hpoint
  rw [Q1_triangleLeafE5BPulse] at hpoint
  exact (add_eq_zero_iff_eq_of_F_module _ _).mp hpoint


end

end TriangleLeaf
end Core4loop
