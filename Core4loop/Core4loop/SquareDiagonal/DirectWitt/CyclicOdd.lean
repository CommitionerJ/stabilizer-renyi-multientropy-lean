import Core4loop.ZeroSumSpaces.ExplicitCyclicPrefix

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

noncomputable section

/-- Adding the total sum as a constant normalizes a profile when `n` is odd. -/
private theorem sigma_add_constant_self_of_odd
    {n : Nat} [NeZero n] (hn : Odd n) (p : Profile n) :
    sigmaMap (n := n)
        (p + constantFunctionLinear n F (sigmaMap (n := n) p)) = 0 := by
  have hncast : ((n : Nat) : F) = 1 :=
    natCast_odd_eq_one_F hn
  change (∑ s : I n, (p s + ∑ t : I n, p t)) = 0
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
  rw [show Fintype.card (I n) = n by simp [I, ZMod.card]]
  rw [nsmul_eq_mul, hncast, one_mul, F_add_self]

/-- The repository-oriented cyclic difference restricted to zero-sum profiles. -/
noncomputable def oddCyclicDiffRestrict
    {n : Nat} [NeZero n] :
    ZeroSumProfile n →ₗ[F] ZeroSumProfile n :=
  (LinearMap.codRestrict (ZeroSumProfile n) (cycDiff (n := n) F)
    (cycDiff_mem_ZeroSumProfile (n := n))).comp
      (ZeroSumProfile n).subtype

/--
For odd cycle length, prefix integration followed by addition of its total
sum is the normalized zero-sum primitive.
-/
noncomputable def oddCyclicInverse
    {n : Nat} [NeZero n] (hn : Odd n) :
    ZeroSumProfile n →ₗ[F] ZeroSumProfile n :=
  LinearMap.codRestrict (ZeroSumProfile n)
    (explicitCyclicPrimitive n +
      (constantFunctionLinear n F).comp
        ((sigmaMap (n := n)).comp (explicitCyclicPrimitive n)))
    (by
      intro u
      apply LinearMap.mem_ker.mpr
      exact sigma_add_constant_self_of_odd hn
        (explicitCyclicPrimitive n u))

@[simp] theorem oddCyclicDiffRestrict_oddCyclicInverse
    {n : Nat} [NeZero n] (hn : Odd n) (u : ZeroSumProfile n) :
    oddCyclicDiffRestrict (n := n) (oddCyclicInverse hn u) = u := by
  apply Subtype.ext
  change cycDiff (n := n) F
      (explicitCyclicPrimitive n u +
        constantFunctionLinear n F
          (sigmaMap (n := n) (explicitCyclicPrimitive n u))) = u.1
  rw [map_add, cycDiff_explicitCyclicPrimitive, cycDiff_constant, add_zero]

@[simp] theorem oddCyclicInverse_oddCyclicDiffRestrict
    {n : Nat} [NeZero n] (hn : Odd n) (u : ZeroSumProfile n) :
    oddCyclicInverse hn (oddCyclicDiffRestrict (n := n) u) = u := by
  apply Subtype.ext
  have hprefix :
      explicitCyclicPrimitive n (oddCyclicDiffRestrict (n := n) u) =
        fun s => u.1 0 + u.1 s := by
    exact explicitCyclicPrefix_cycDiff u.1
  have huzero : (∑ s : I n, u.1 s) = 0 :=
    LinearMap.mem_ker.mp u.2
  have hncast : ((n : Nat) : F) = 1 :=
    natCast_odd_eq_one_F hn
  have hsigma :
      sigmaMap (n := n)
          (explicitCyclicPrimitive n (oddCyclicDiffRestrict (n := n) u)) =
        u.1 0 := by
    rw [hprefix]
    change (∑ s : I n, (u.1 0 + u.1 s)) = u.1 0
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    rw [show Fintype.card (I n) = n by simp [I, ZMod.card]]
    rw [nsmul_eq_mul, hncast, one_mul, huzero, add_zero]
  funext s
  change
    explicitCyclicPrimitive n (oddCyclicDiffRestrict (n := n) u) s +
        sigmaMap (n := n)
          (explicitCyclicPrimitive n (oddCyclicDiffRestrict (n := n) u)) =
      u.1 s
  rw [hsigma, hprefix]
  change (u.1 0 + u.1 s) + u.1 0 = u.1 s
  calc
    (u.1 0 + u.1 s) + u.1 0 = (u.1 0 + u.1 0) + u.1 s := by
      abel
    _ = u.1 s := by rw [F_add_self, zero_add]

/-- Cyclic difference is explicitly invertible on zero-sum profiles for odd `n`. -/
noncomputable def oddCyclicDiffRestrictEquiv
    {n : Nat} [NeZero n] (hn : Odd n) :
    ZeroSumProfile n ≃ₗ[F] ZeroSumProfile n where
  toLinearMap := oddCyclicDiffRestrict
  invFun := oddCyclicInverse hn
  left_inv := oddCyclicInverse_oddCyclicDiffRestrict hn
  right_inv := oddCyclicDiffRestrict_oddCyclicInverse hn

/--
The normalized inverse `S` of cyclic difference satisfies
`⟪S u, v⟫ + ⟪u, S v⟫ = ⟪u, v⟫`.
-/
theorem oddCyclicInverse_pairing_add_pairing
    {n : Nat} [NeZero n] (hn : Odd n)
    (u v : ZeroSumProfile n) :
    (∑ s : I n, (oddCyclicInverse hn u).1 s * v.1 s) +
        (∑ s : I n, u.1 s * (oddCyclicInverse hn v).1 s) =
      ∑ s : I n, u.1 s * v.1 s := by
  let a := oddCyclicInverse hn u
  let b := oddCyclicInverse hn v
  have hu : oddCyclicDiffRestrict (n := n) a = u := by
    exact oddCyclicDiffRestrict_oddCyclicInverse hn u
  have hv : oddCyclicDiffRestrict (n := n) b = v := by
    exact oddCyclicDiffRestrict_oddCyclicInverse hn v
  rw [← hu, ← hv]
  simp only [oddCyclicInverse_oddCyclicDiffRestrict]
  change
    (∑ s : I n, a.1 s * (b.1 s + b.1 (s + 1))) +
        (∑ s : I n, (a.1 s + a.1 (s + 1)) * b.1 s) =
      ∑ s : I n,
        (a.1 s + a.1 (s + 1)) * (b.1 s + b.1 (s + 1))
  simp_rw [mul_add, add_mul]
  repeat' rw [Finset.sum_add_distrib]
  have hshift :
      (∑ s : I n, a.1 (s + 1) * b.1 (s + 1)) =
        ∑ s : I n, a.1 s * b.1 s := by
    simpa using
      sum_shift (n := n) (1 : I n) (fun s => a.1 s * b.1 s)
  rw [hshift]
  ring

end

end Core4loop.SquareDiagonal.DirectWitt
