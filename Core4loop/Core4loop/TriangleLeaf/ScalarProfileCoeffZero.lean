import Core4loop.TriangleLeaf.LeafProfileKernelDimensions
import Core4loop.TriangleLeaf.FiniteSelectors

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafScalarCoeffApply {n a : ℕ} [NeZero n]
    (C : PVec n a → F) (X : LeafScalarProfileKernel n a) : F :=
  ∑ p : PVec n a, X.1 p * C p

def leafScalarCoeffCondition {n a : ℕ} [NeZero n]
    (C : PVec n a → F) : Prop :=
  ∀ p : PVec n a, C p = C (zeroVec : PVec n a)

private lemma two_point_kernel_fun_mem
    {n a : ℕ} [NeZero n] (p : PVec n a)
    (hp : p ≠ (zeroVec : PVec n a)) :
    (fun q : PVec n a =>
        if q = p then (1 : F)
        else if q = (zeroVec : PVec n a) then (1 : F) else 0)
      ∈ LeafScalarProfileKernel n a := by
  rw [LinearMap.mem_ker]
  change
    (∑ q : PVec n a,
        if q = p then (1 : F)
        else if q = (zeroVec : PVec n a) then (1 : F) else 0) = 0
  calc
    (∑ q : PVec n a,
        if q = p then (1 : F)
        else if q = (zeroVec : PVec n a) then (1 : F) else 0)
        =
        (∑ q : PVec n a, if q = p then (1 : F) else 0)
          +
        (∑ q : PVec n a, if q = (zeroVec : PVec n a) then (1 : F) else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro q _
          by_cases hq : q = p
          · simp [hq, hp]
          · simp [hq]
    _ = (1 : F) + 1 := by
          rw [Finset.sum_eq_single p, Finset.sum_eq_single (zeroVec : PVec n a)]
          · simp
          · intro q _ hq
            simp [hq]
          · simp
          · intro q _ hq
            simp [hq]
          · simp
    _ = 0 := by rw [F_add_self]

private lemma leafScalarCoeffApply_two_point
    {n a : ℕ} [NeZero n] (C : PVec n a → F) (p : PVec n a)
    (hp : p ≠ (zeroVec : PVec n a)) :
    leafScalarCoeffApply (n := n) (a := a) C
        ⟨fun q : PVec n a =>
            if q = p then (1 : F)
            else if q = (zeroVec : PVec n a) then (1 : F) else 0,
          two_point_kernel_fun_mem (n := n) (a := a) p hp⟩
      =
      C p + C (zeroVec : PVec n a) := by
  unfold leafScalarCoeffApply
  calc
    (∑ q : PVec n a,
        (if q = p then (1 : F)
          else if q = (zeroVec : PVec n a) then (1 : F) else 0) * C q)
        =
        (∑ q : PVec n a, (if q = p then (1 : F) else 0) * C q)
          +
        (∑ q : PVec n a,
          (if q = (zeroVec : PVec n a) then (1 : F) else 0) * C q) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro q _
          by_cases hq : q = p
          · simp [hq, hp]
          · simp [hq]
    _ = C p + C (zeroVec : PVec n a) := by
          rw [sum_ite_eq_mul (fun q : PVec n a => C q) p (1 : F)]
          rw [sum_ite_eq_mul
            (fun q : PVec n a => C q) (zeroVec : PVec n a) (1 : F)]
          simp

theorem leafScalarCoeffApply_forall_eq_zero_iff_condition
    {n a : ℕ} [NeZero n] (C : PVec n a → F) :
    (∀ X : LeafScalarProfileKernel n a,
        leafScalarCoeffApply (n := n) (a := a) C X = 0)
      ↔
      leafScalarCoeffCondition (n := n) (a := a) C := by
  constructor
  · intro h p
    by_cases hp : p = (zeroVec : PVec n a)
    · simp [hp]
    · have hX := h
        ⟨fun q : PVec n a =>
            if q = p then (1 : F)
            else if q = (zeroVec : PVec n a) then (1 : F) else 0,
          two_point_kernel_fun_mem (n := n) (a := a) p hp⟩
      rw [leafScalarCoeffApply_two_point (n := n) (a := a) C p hp] at hX
      calc
        C p = C p + 0 := by simp
        _ = C p + (C p + C (zeroVec : PVec n a)) := by rw [hX]
        _ = C (zeroVec : PVec n a) := by
          calc
            C p + (C p + C (zeroVec : PVec n a))
                = (C p + C p) + C (zeroVec : PVec n a) := by ac_rfl
            _ = C (zeroVec : PVec n a) := by rw [F_add_self, zero_add]
  · intro hC X
    unfold leafScalarCoeffApply
    calc
      (∑ p : PVec n a, X.1 p * C p)
          =
          ∑ p : PVec n a, X.1 p * C (zeroVec : PVec n a) := by
            refine Finset.sum_congr rfl ?_
            intro p _
            rw [hC p]
      _ = (∑ p : PVec n a, X.1 p) * C (zeroVec : PVec n a) := by
            rw [Finset.sum_mul]
      _ = 0 := by
            have hsum := LinearMap.mem_ker.mp X.2
            change (∑ p : PVec n a, X.1 p) = 0 at hsum
            rw [hsum, zero_mul]

def leafScalarFamilyCoeffApply
    {ι : Type*} [Fintype ι] {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → F) (X : ι → LeafScalarProfileKernel n a) : F :=
  ∑ i : ι, leafScalarCoeffApply (n := n) (a := a) (C i) (X i)

def leafScalarFamilyCoeffCondition
    {ι : Type*} {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → F) : Prop :=
  ∀ i : ι, leafScalarCoeffCondition (n := n) (a := a) (C i)

def leafScalarFamilyCoeffRead
    {ι : Type*} {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → F) :
    ι × {p : PVec n a // p ≠ (zeroVec : PVec n a)} → F :=
  fun ip => C ip.1 ip.2.1 + C ip.1 (zeroVec : PVec n a)

theorem leafScalarFamilyCoeffRead_add
    {ι : Type*} {n a : ℕ} [NeZero n]
    (C D : ι → PVec n a → F) :
    leafScalarFamilyCoeffRead (n := n) (a := a) (C + D)
      =
      leafScalarFamilyCoeffRead (n := n) (a := a) C
        +
      leafScalarFamilyCoeffRead (n := n) (a := a) D := by
  funext ip
  rcases ip with ⟨i, p⟩
  simp [leafScalarFamilyCoeffRead, Pi.add_apply]
  abel

theorem leafScalarFamilyCoeffRead_smul
    {ι : Type*} {n a : ℕ} [NeZero n]
    (r : F) (C : ι → PVec n a → F) :
    leafScalarFamilyCoeffRead (n := n) (a := a) (r • C)
      =
      r • leafScalarFamilyCoeffRead (n := n) (a := a) C := by
  funext ip
  rcases ip with ⟨i, p⟩
  simp [leafScalarFamilyCoeffRead, Pi.smul_apply]
  ring

theorem leafScalarFamilyCoeffRead_eq_zero_iff_condition
    {ι : Type*} {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → F) :
    leafScalarFamilyCoeffRead (n := n) (a := a) C = 0
      ↔
      leafScalarFamilyCoeffCondition (n := n) (a := a) C := by
  constructor
  · intro h i p
    by_cases hp : p = (zeroVec : PVec n a)
    · simp [hp]
    · have hread := congrFun h (i, ⟨p, hp⟩)
      dsimp [leafScalarFamilyCoeffRead] at hread
      calc
        C i p = C i p + 0 := by simp
        _ = C i p + (C i p + C i (zeroVec : PVec n a)) := by rw [hread]
        _ = C i (zeroVec : PVec n a) := by
          calc
            C i p + (C i p + C i (zeroVec : PVec n a))
                = (C i p + C i p) + C i (zeroVec : PVec n a) := by ac_rfl
            _ = C i (zeroVec : PVec n a) := by rw [F_add_self, zero_add]
  · intro hC
    funext ip
    dsimp [leafScalarFamilyCoeffRead]
    rw [hC ip.1 ip.2.1, F_add_self]

theorem leafScalarFamilyCoeffApply_forall_eq_zero_iff_condition
    {ι : Type*} [Fintype ι] {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → F) :
    (∀ X : ι → LeafScalarProfileKernel n a,
        leafScalarFamilyCoeffApply (n := n) (a := a) C X = 0)
      ↔
      leafScalarFamilyCoeffCondition (n := n) (a := a) C := by
  classical
  constructor
  · intro h i
    rw [← leafScalarCoeffApply_forall_eq_zero_iff_condition
      (n := n) (a := a) (C i)]
    intro K
    let X : ι → LeafScalarProfileKernel n a :=
      fun j => if j = i then K else 0
    have hX := h X
    unfold leafScalarFamilyCoeffApply at hX
    rw [Finset.sum_eq_single i] at hX
    · simpa [X] using hX
    · intro j _ hj
      rw [show X j = 0 by simp [X, hj]]
      unfold leafScalarCoeffApply
      simp
    · simp [X]
  · intro hC X
    unfold leafScalarFamilyCoeffApply
    refine Finset.sum_eq_zero ?_
    intro i _
    exact
      (leafScalarCoeffApply_forall_eq_zero_iff_condition
        (n := n) (a := a) (C i)).2 (hC i) (X i)

theorem linearMap_eq_zero_iff_of_apply_eq_leafScalarFamilyCoeffApply
    {ι : Type*} [Fintype ι] {n a : ℕ} [NeZero n]
    (L : (ι → LeafScalarProfileKernel n a) →ₗ[F] F)
    (C : ι → PVec n a → F)
    (hL : ∀ X : ι → LeafScalarProfileKernel n a,
      L X = leafScalarFamilyCoeffApply (n := n) (a := a) C X) :
    L = 0 ↔ leafScalarFamilyCoeffCondition (n := n) (a := a) C := by
  have hzero := leafScalarFamilyCoeffApply_forall_eq_zero_iff_condition
    (n := n) (a := a) C
  constructor
  · intro h
    rw [← hzero]
    intro X
    rw [← hL X, h]
    rfl
  · intro hread
    apply LinearMap.ext
    intro X
    rw [hL X]
    exact hzero.2 hread X

end

end TriangleLeaf
end Core4loop
