import TreeGraph.AssignmentBridge

namespace TreeGraph

namespace RawPrimitive

open RawLinearAlgebra

noncomputable def branchConstraintMap {n : Nat} [NeZero n]
    (P M : Type) [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (π : P →ₗ[F2] (ZMod n → M)) :
    P →ₗ[F2] (ZMod n → M) :=
  (cyclicDiff n M).comp π

def BranchMessageCompatible {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M]
    (g : ZMod n → M) : Prop :=
  totalSumLinear n M g = 0

def branchConstraintExponent (n N Y : Nat) : Nat :=
  N - (n - 1) * Y

theorem branchConstraintMap_range_eq_totalSum_ker
    {n : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π) :
    LinearMap.range (branchConstraintMap P M π) =
      LinearMap.ker (totalSumLinear n M) := by
  simpa [branchConstraintMap] using
    cyclicDiff_comp_surjective_range_eq_totalSum_ker M π hπ

theorem branchConstraintMap_mem_range_iff_compatible
    {n : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π) (g : ZMod n → M) :
    g ∈ LinearMap.range (branchConstraintMap P M π) ↔
      BranchMessageCompatible M g := by
  rw [branchConstraintMap_range_eq_totalSum_ker π hπ]
  rfl

theorem branchConstraintFiber_nonempty_iff_compatible
    {n : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π) (g : ZMod n → M) :
    Nonempty { p : P // branchConstraintMap P M π p = g } ↔
      BranchMessageCompatible M g := by
  constructor
  · rintro ⟨⟨p, hp⟩⟩
    exact (branchConstraintMap_mem_range_iff_compatible π hπ g).1
      ⟨p, hp⟩
  · intro hg
    rcases (branchConstraintMap_mem_range_iff_compatible π hπ g).2 hg with
      ⟨p, hp⟩
    exact ⟨⟨p, hp⟩⟩

theorem finrank_range_branchConstraintMap
    {n : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π) :
    Module.finrank F2 (LinearMap.range (branchConstraintMap P M π)) =
      (n - 1) * Module.finrank F2 M := by
  simpa [branchConstraintMap] using
    finrank_range_cyclicDiff_comp_surjective M π hπ

theorem finrank_range_branchConstraintMap_eq
    {n Y : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (hM : Module.finrank F2 M = Y) :
    Module.finrank F2 (LinearMap.range (branchConstraintMap P M π)) =
      (n - 1) * Y := by
  rw [finrank_range_branchConstraintMap π hπ, hM]

theorem finrank_ker_branchConstraintMap_of_surjective
    {n : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π) :
    Module.finrank F2 (LinearMap.ker (branchConstraintMap P M π)) =
      Module.finrank F2 P - (n - 1) * Module.finrank F2 M := by
  classical
  let L := branchConstraintMap P M π
  let D := Module.finrank F2 P
  let R := (n - 1) * Module.finrank F2 M
  let K := Module.finrank F2 (LinearMap.ker L)
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hrange : Module.finrank F2 (LinearMap.range L) = R := by
    simpa [L, R] using finrank_range_branchConstraintMap π hπ
  rw [hrange] at hsum
  have hsum' : R + K = D := by
    simpa [D, K, R] using hsum
  have hK : K = D - R := by
    omega
  simpa [L, D, R, K] using hK

theorem finrank_ker_branchConstraintMap_eq_branchConstraintExponent
    {n N Y : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (hP : Module.finrank F2 P = N)
    (hM : Module.finrank F2 M = Y) :
    Module.finrank F2 (LinearMap.ker (branchConstraintMap P M π)) =
      branchConstraintExponent n N Y := by
  rw [finrank_ker_branchConstraintMap_of_surjective π hπ, hP, hM,
    branchConstraintExponent]

theorem branchConstraintExponent_cast_pow
    {n A Y : Nat} [NeZero n]
    (hle : (n - 1) * Y ≤ n ^ A) :
    ((branchConstraintExponent n (n ^ A) Y : Nat) : ℤ) =
      (nZ n) ^ A - (tZ n) * (Y : ℤ) := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  rw [branchConstraintExponent, Nat.cast_sub hle, Nat.cast_pow,
    Nat.cast_mul, Nat.cast_sub hn]
  ring

theorem branchConstraintExponent_cast
    {n N Y : Nat} [NeZero n]
    (hle : (n - 1) * Y ≤ N) :
    ((branchConstraintExponent n N Y : Nat) : ℤ) =
      (N : ℤ) - (tZ n) * (Y : ℤ) := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  rw [branchConstraintExponent, Nat.cast_sub hle, Nat.cast_mul,
    Nat.cast_sub hn]
  ring

theorem branchConstraintExponent_toNat_pow
    {n A Y : Nat} [NeZero n]
    (hle : (n - 1) * Y ≤ n ^ A) :
    Int.toNat ((nZ n) ^ A - (tZ n) * (Y : ℤ)) =
      branchConstraintExponent n (n ^ A) Y := by
  rw [← branchConstraintExponent_cast_pow (n := n) (A := A) (Y := Y) hle]
  simp

theorem branchConstraintExponent_toNat
    {n N Y : Nat} [NeZero n]
    (hle : (n - 1) * Y ≤ N) :
    Int.toNat ((N : ℤ) - (tZ n) * (Y : ℤ)) =
      branchConstraintExponent n N Y := by
  rw [← branchConstraintExponent_cast (n := n) (N := N) (Y := Y) hle]
  simp

theorem finrank_ker_branchConstraintMap_int
    {n A Y : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (hP : Module.finrank F2 P = n ^ A)
    (hM : Module.finrank F2 M = Y)
    (hle : (n - 1) * Y ≤ n ^ A) :
    ((Module.finrank F2
        (LinearMap.ker (branchConstraintMap P M π)) : Nat) : ℤ) =
      (nZ n) ^ A - (tZ n) * (Y : ℤ) := by
  rw [finrank_ker_branchConstraintMap_eq_branchConstraintExponent
    π hπ hP hM]
  exact branchConstraintExponent_cast_pow (n := n) (A := A) (Y := Y) hle

theorem card_ker_branchConstraintMap_of_surjective
    {n : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π) :
    Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) =
      2 ^ (Module.finrank F2 P -
        (n - 1) * Module.finrank F2 M) := by
  classical
  calc
    Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.ker (branchConstraintMap P M π)) :=
      Module.natCard_eq_pow_finrank
        (K := F2) (V := LinearMap.ker (branchConstraintMap P M π))
    _ = 2 ^ (Module.finrank F2 P -
        (n - 1) * Module.finrank F2 M) := by
      rw [finrank_ker_branchConstraintMap_of_surjective π hπ]
      simp [F2]

theorem card_ker_branchConstraintMap_eq_branchConstraintExponent
    {n N Y : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (hP : Module.finrank F2 P = N)
    (hM : Module.finrank F2 M = Y) :
    Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) =
      2 ^ branchConstraintExponent n N Y := by
  rw [card_ker_branchConstraintMap_of_surjective π hπ, hP, hM,
    branchConstraintExponent]

theorem card_ker_branchConstraintMap_eq_two_pow_int
    {n A Y : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (hP : Module.finrank F2 P = n ^ A)
    (hM : Module.finrank F2 M = Y)
    (hle : (n - 1) * Y ≤ n ^ A) :
    Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) =
      2 ^ Int.toNat ((nZ n) ^ A - (tZ n) * (Y : ℤ)) := by
  calc
    Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) =
      2 ^ branchConstraintExponent n (n ^ A) Y := by
        exact card_ker_branchConstraintMap_eq_branchConstraintExponent
          π hπ hP hM
    _ = 2 ^ Int.toNat ((nZ n) ^ A - (tZ n) * (Y : ℤ)) := by
        rw [← branchConstraintExponent_toNat_pow
          (n := n) (A := A) (Y := Y) hle]

theorem card_ker_branchConstraintMap_eq_two_pow_int_of_dims
    {n N Y : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (hP : Module.finrank F2 P = N)
    (hM : Module.finrank F2 M = Y)
    (hle : (n - 1) * Y ≤ N) :
    Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) =
      2 ^ Int.toNat ((N : ℤ) - (tZ n) * (Y : ℤ)) := by
  calc
    Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) =
      2 ^ branchConstraintExponent n N Y := by
        exact card_ker_branchConstraintMap_eq_branchConstraintExponent
          π hπ hP hM
    _ = 2 ^ Int.toNat ((N : ℤ) - (tZ n) * (Y : ℤ)) := by
        rw [← branchConstraintExponent_toNat
          (n := n) (N := N) (Y := Y) hle]

theorem card_branchConstraintFiber_of_solution
    {n : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (g : ZMod n → M) (p0 : P)
    (hp0 : branchConstraintMap P M π p0 = g) :
    Nat.card { p : P // branchConstraintMap P M π p = g } =
      2 ^ (Module.finrank F2 P -
        (n - 1) * Module.finrank F2 M) := by
  calc
    Nat.card { p : P // branchConstraintMap P M π p = g } =
        Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) :=
      card_linearMap_fiber_eq_card_ker_of_solution
        (branchConstraintMap P M π) g p0 hp0
    _ = 2 ^ (Module.finrank F2 P -
        (n - 1) * Module.finrank F2 M) :=
      card_ker_branchConstraintMap_of_surjective π hπ

theorem card_branchConstraintFiber_of_compatible
    {n : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (g : ZMod n → M) (hg : BranchMessageCompatible M g) :
    Nat.card { p : P // branchConstraintMap P M π p = g } =
      2 ^ (Module.finrank F2 P -
        (n - 1) * Module.finrank F2 M) := by
  rcases (branchConstraintMap_mem_range_iff_compatible π hπ g).2 hg with
    ⟨p0, hp0⟩
  exact card_branchConstraintFiber_of_solution π hπ g p0 hp0

theorem card_branchConstraintFiber_eq_branchConstraintExponent
    {n N Y : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (g : ZMod n → M) (hg : BranchMessageCompatible M g)
    (hP : Module.finrank F2 P = N)
    (hM : Module.finrank F2 M = Y) :
    Nat.card { p : P // branchConstraintMap P M π p = g } =
      2 ^ branchConstraintExponent n N Y := by
  rw [card_branchConstraintFiber_of_compatible π hπ g hg, hP, hM,
    branchConstraintExponent]

theorem card_branchConstraintFiber_eq_two_pow_int
    {n A Y : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (g : ZMod n → M) (hg : BranchMessageCompatible M g)
    (hP : Module.finrank F2 P = n ^ A)
    (hM : Module.finrank F2 M = Y)
    (hle : (n - 1) * Y ≤ n ^ A) :
    Nat.card { p : P // branchConstraintMap P M π p = g } =
      2 ^ Int.toNat ((nZ n) ^ A - (tZ n) * (Y : ℤ)) := by
  calc
    Nat.card { p : P // branchConstraintMap P M π p = g } =
      2 ^ branchConstraintExponent n (n ^ A) Y := by
        exact card_branchConstraintFiber_eq_branchConstraintExponent
          π hπ g hg hP hM
    _ = 2 ^ Int.toNat ((nZ n) ^ A - (tZ n) * (Y : ℤ)) := by
        rw [← branchConstraintExponent_toNat_pow
          (n := n) (A := A) (Y := Y) hle]

theorem card_branchConstraintFiber_eq_two_pow_int_of_dims
    {n N Y : Nat} [NeZero n] {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (g : ZMod n → M) (hg : BranchMessageCompatible M g)
    (hP : Module.finrank F2 P = N)
    (hM : Module.finrank F2 M = Y)
    (hle : (n - 1) * Y ≤ N) :
    Nat.card { p : P // branchConstraintMap P M π p = g } =
      2 ^ Int.toNat ((N : ℤ) - (tZ n) * (Y : ℤ)) := by
  calc
    Nat.card { p : P // branchConstraintMap P M π p = g } =
      2 ^ branchConstraintExponent n N Y := by
        exact card_branchConstraintFiber_eq_branchConstraintExponent
          π hπ g hg hP hM
    _ = 2 ^ Int.toNat ((N : ℤ) - (tZ n) * (Y : ℤ)) := by
        rw [← branchConstraintExponent_toNat
          (n := n) (N := N) (Y := Y) hle]

end RawPrimitive

end TreeGraph
