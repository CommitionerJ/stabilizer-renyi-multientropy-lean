import TreeGraph.RawNormalForm
import TreeGraph.AlgebraLemmas

namespace TreeGraph

namespace RawLinearAlgebra

noncomputable def cyclicDiff (n : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    (ZMod n → M) →ₗ[F2] (ZMod n → M) where
  toFun f := fun t => f t + f (t + 1)
  map_add' f g := by
    ext t
    simp [Pi.add_apply, add_assoc, add_left_comm, add_comm]
  map_smul' c f := by
    ext t
    simp [Pi.smul_apply, smul_add]

@[simp] theorem cyclicDiff_apply {n : Nat} [NeZero n] {M : Type}
    [AddCommGroup M] [Module F2 M] (f : ZMod n → M) (t : ZMod n) :
    cyclicDiff n M f t = f t + f (t + 1) := rfl

private theorem add_self_eq_zero_of_module_F2 {M : Type}
    [AddCommGroup M] [Module F2 M] (x : M) :
    x + x = 0 := by
  have htwo : (1 : F2) + (1 : F2) = 0 := by decide
  calc
    x + x = (1 : F2) • x + (1 : F2) • x := by simp
    _ = ((1 : F2) + (1 : F2)) • x := by rw [add_smul]
    _ = 0 := by simp [htwo]

private theorem neg_eq_self_of_module_F2 {M : Type}
    [AddCommGroup M] [Module F2 M] (x : M) :
    -x = x := by
  have hxx : x + x = 0 := add_self_eq_zero_of_module_F2 x
  calc
    -x = -x + 0 := by simp
    _ = -x + (x + x) := by rw [hxx]
    _ = x := by abel

theorem nsmul_eq_zero_of_even_module_F2 {M : Type}
    [AddCommGroup M] [Module F2 M] {k : Nat} (hk : Even k) (x : M) :
    k • x = 0 := by
  rcases hk with ⟨m, hm⟩
  rw [hm, add_nsmul]
  exact add_self_eq_zero_of_module_F2 (m • x)

theorem nsmul_eq_self_of_odd_module_F2 {M : Type}
    [AddCommGroup M] [Module F2 M] {k : Nat} (hk : Odd k) (x : M) :
    k • x = x := by
  rcases hk with ⟨m, hm⟩
  have hpos : 0 < k := by omega
  have hevenPred : Even (k - 1) := by
    refine ⟨m, ?_⟩
    omega
  calc
    k • x = ((k - 1) + 1) • x := by
      have hkdecomp : k = (k - 1) + 1 := by omega
      rw [← hkdecomp]
    _ = (k - 1) • x + x := by simp [add_nsmul]
    _ = x := by
      rw [nsmul_eq_zero_of_even_module_F2 hevenPred]
      simp

noncomputable def constantFunctionLinear (n : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    M →ₗ[F2] (ZMod n → M) where
  toFun m := fun _ => m
  map_add' x y := by
    ext t
    simp
  map_smul' c x := by
    ext t
    simp

theorem cyclicDiff_constant {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] (m : M) :
    cyclicDiff n M (constantFunctionLinear n M m) = 0 := by
  ext t
  have htwo : (1 : F2) + (1 : F2) = 0 := by decide
  calc
    (cyclicDiff n M (constantFunctionLinear n M m)) t = m + m := by
      rfl
    _ = (1 : F2) • m + (1 : F2) • m := by simp
    _ = ((1 : F2) + (1 : F2)) • m := by rw [add_smul]
    _ = 0 := by simp [htwo]

theorem cyclicDiff_sum_zero {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] (f : ZMod n → M) :
    (∑ t : ZMod n, cyclicDiff n M f t) = 0 := by
  classical
  have hshift :
      (∑ t : ZMod n, f (t + 1)) = ∑ t : ZMod n, f t := by
    simpa using
      (Equiv.sum_comp (Equiv.addRight (1 : ZMod n))
        (fun t : ZMod n => f t))
  calc
    (∑ t : ZMod n, cyclicDiff n M f t)
        = ∑ t : ZMod n, (f t + f (t + 1)) := by rfl
    _ = (∑ t : ZMod n, f t) + ∑ t : ZMod n, f (t + 1) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ t : ZMod n, f t) + ∑ t : ZMod n, f t := by
      rw [hshift]
    _ = 0 := add_self_eq_zero_of_module_F2 _

theorem cyclicDiff_eq_zero_iff_exists_constant {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] (f : ZMod n → M) :
    cyclicDiff n M f = 0 ↔ ∃ m : M, f = constantFunctionLinear n M m := by
  constructor
  · intro hzero
    have hstep : ∀ t : ZMod n, f (t + 1) = f t := by
      intro t
      have ht : f t + f (t + 1) = 0 := by
        simpa using congrArg (fun g : ZMod n → M => g t) hzero
      calc
        f (t + 1) = 0 + f (t + 1) := by simp
        _ = (-f t + f t) + f (t + 1) := by simp
        _ = -f t + (f t + f (t + 1)) := by abel
        _ = -f t := by rw [ht]; simp
        _ = f t := neg_eq_self_of_module_F2 (f t)
    refine ⟨f 0, ?_⟩
    ext t
    have hnat : ∀ k : Nat, f ((k : Nat) : ZMod n) = f 0 := by
      intro k
      induction k with
      | zero =>
          simp
      | succ k ih =>
          calc
            f ((Nat.succ k : Nat) : ZMod n)
                = f ((k : ZMod n) + 1) := by simp [Nat.cast_succ]
            _ = f (k : ZMod n) := hstep (k : ZMod n)
            _ = f 0 := ih
    rw [← ZMod.natCast_zmod_val t]
    exact hnat t.val
  · rintro ⟨m, rfl⟩
    exact cyclicDiff_constant M m

theorem cyclicDiff_eq_zero_iff_constant_apply {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] (f : ZMod n → M) :
    cyclicDiff n M f = 0 ↔ ∀ t : ZMod n, f t = f 0 := by
  constructor
  · intro hzero t
    rcases (cyclicDiff_eq_zero_iff_exists_constant M f).1 hzero with ⟨m, hm⟩
    rw [hm]
    rfl
  · intro hconst
    apply (cyclicDiff_eq_zero_iff_exists_constant M f).2
    refine ⟨f 0, ?_⟩
    ext t
    exact hconst t

theorem cyclicDiff_eq_iff_exists_constant {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M]
    (f g : ZMod n → M) :
    cyclicDiff n M f = cyclicDiff n M g ↔
      ∃ m : M, f = g + constantFunctionLinear n M m := by
  constructor
  · intro hfg
    have hker : cyclicDiff n M (f - g) = 0 := by
      rw [map_sub, hfg]
      simp
    rcases (cyclicDiff_eq_zero_iff_exists_constant M (f - g)).1 hker with
      ⟨m, hm⟩
    refine ⟨m, ?_⟩
    ext t
    have ht := congrArg (fun h : ZMod n → M => h t) hm
    change f t - g t = m at ht
    calc
      f t = (f t - g t) + g t := by abel
      _ = m + g t := by rw [ht]
      _ = g t + m := by abel
  · rintro ⟨m, rfl⟩
    simp [map_add, cyclicDiff_constant]

noncomputable def cyclicDiffKerEquiv {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    LinearMap.ker (cyclicDiff n M) ≃ₗ[F2] M where
  toFun u := u.1 0
  invFun m :=
    ⟨constantFunctionLinear n M m,
      LinearMap.mem_ker.mpr (cyclicDiff_constant M m)⟩
  map_add' u v := rfl
  map_smul' c u := rfl
  left_inv u := by
    apply Subtype.ext
    funext t
    have hzero : cyclicDiff n M u.1 = 0 := LinearMap.mem_ker.mp u.2
    exact ((cyclicDiff_eq_zero_iff_constant_apply M u.1).1 hzero t).symm
  right_inv m := rfl

theorem finrank_ker_cyclicDiff {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    Module.finrank F2 (LinearMap.ker (cyclicDiff n M)) =
      Module.finrank F2 M :=
  LinearEquiv.finrank_eq (cyclicDiffKerEquiv M)

theorem card_ker_cyclicDiff {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Nat.card (↥(LinearMap.ker (cyclicDiff n M))) =
      2 ^ Module.finrank F2 M := by
  classical
  calc
    Nat.card (↥(LinearMap.ker (cyclicDiff n M))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.ker (cyclicDiff n M)) :=
      Module.natCard_eq_pow_finrank
        (K := F2) (V := LinearMap.ker (cyclicDiff n M))
    _ = 2 ^ Module.finrank F2 M := by
      rw [finrank_ker_cyclicDiff M]
      simp [F2]

noncomputable def cyclicDiffFiberEquivKer {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M]
    (g f0 : ZMod n → M) (hf0 : cyclicDiff n M f0 = g) :
    { f : ZMod n → M // cyclicDiff n M f = g } ≃
      LinearMap.ker (cyclicDiff n M) where
  toFun f :=
    ⟨f.1 - f0, LinearMap.mem_ker.mpr (by
      rw [LinearMap.map_sub, f.2, hf0]
      simp)⟩
  invFun u :=
    ⟨u.1 + f0, by
      rw [LinearMap.map_add, LinearMap.mem_ker.mp u.2, hf0]
      simp⟩
  left_inv f := by
    apply Subtype.ext
    ext t
    simp
  right_inv u := by
    apply Subtype.ext
    ext t
    simp

theorem card_cyclicDiff_fiber_of_solution {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (g f0 : ZMod n → M) (hf0 : cyclicDiff n M f0 = g) :
    Nat.card { f : ZMod n → M // cyclicDiff n M f = g } =
      2 ^ Module.finrank F2 M := by
  calc
    Nat.card { f : ZMod n → M // cyclicDiff n M f = g } =
        Nat.card (↥(LinearMap.ker (cyclicDiff n M))) :=
      Nat.card_congr (cyclicDiffFiberEquivKer M g f0 hf0)
    _ = 2 ^ Module.finrank F2 M := card_ker_cyclicDiff M

theorem card_cyclicDiff_fiber_of_mem_range {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (g : ZMod n → M) (hg : g ∈ LinearMap.range (cyclicDiff n M)) :
    Nat.card { f : ZMod n → M // cyclicDiff n M f = g } =
      2 ^ Module.finrank F2 M := by
  rcases hg with ⟨f0, hf0⟩
  exact card_cyclicDiff_fiber_of_solution M g f0 hf0

noncomputable def linearMapFiberEquivKer
    {P Q : Type} [AddCommGroup P] [Module F2 P]
    [AddCommGroup Q] [Module F2 Q]
    (L : P →ₗ[F2] Q) (q : Q) (p0 : P) (hp0 : L p0 = q) :
    { p : P // L p = q } ≃ LinearMap.ker L where
  toFun p :=
    ⟨p.1 - p0, LinearMap.mem_ker.mpr (by
      rw [LinearMap.map_sub, p.2, hp0]
      simp)⟩
  invFun u :=
    ⟨u.1 + p0, by
      rw [LinearMap.map_add, LinearMap.mem_ker.mp u.2, hp0]
      simp⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv u := by
    apply Subtype.ext
    simp

theorem card_linearMap_fiber_eq_card_ker_of_solution
    {P Q : Type} [AddCommGroup P] [Module F2 P]
    [AddCommGroup Q] [Module F2 Q]
    (L : P →ₗ[F2] Q) (q : Q) (p0 : P) (hp0 : L p0 = q) :
    Nat.card { p : P // L p = q } =
      Nat.card (↥(LinearMap.ker L)) :=
  Nat.card_congr (linearMapFiberEquivKer L q p0 hp0)

noncomputable def totalSumLinear (n : Nat) [NeZero n] (M : Type)
    [AddCommMonoid M] [Module F2 M] :
    (ZMod n → M) →ₗ[F2] M where
  toFun f := ∑ t : ZMod n, f t
  map_add' f g := by
    simp [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c f := by
    rw [Finset.smul_sum]
    rfl

@[simp] theorem totalSumLinear_apply {n : Nat} [NeZero n] {M : Type}
    [AddCommMonoid M] [Module F2 M] (f : ZMod n → M) :
    totalSumLinear n M f = ∑ t : ZMod n, f t := rfl

theorem totalSumLinear_surjective {n : Nat} [NeZero n] (M : Type)
    [AddCommMonoid M] [Module F2 M] :
    Function.Surjective (totalSumLinear n M) := by
  classical
  intro m
  refine ⟨fun t : ZMod n => if t = 0 then m else 0, ?_⟩
  rw [totalSumLinear_apply]
  rw [Fintype.sum_eq_single (0 : ZMod n)]
  · simp
  · intro t ht
    simp [ht]

theorem finrank_totalSum_ker {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.ker (totalSumLinear n M)) =
      (n - 1) * Module.finrank F2 M := by
  classical
  let d := Module.finrank F2 M
  have hsum :=
    LinearMap.finrank_range_add_finrank_ker (totalSumLinear n M)
  have hrange :
      Module.finrank F2 (LinearMap.range (totalSumLinear n M)) = d := by
    rw [LinearMap.range_eq_top.2 (totalSumLinear_surjective M), finrank_top]
  have hdomain :
      Module.finrank F2 (ZMod n → M) = n * d := by
    calc
      Module.finrank F2 (ZMod n → M)
          = ∑ _ : ZMod n, d := by
              simpa [d] using
                (Module.finrank_pi_fintype
                  (R := F2) (M := fun _ : ZMod n => M))
      _ = n * d := by
              simp [ZMod.card, Finset.card_univ]
  rw [hrange, hdomain] at hsum
  have hnpos : 0 < n := NeZero.pos n
  have hn : n = (n - 1) + 1 := by
    omega
  have hmul : n * d = (n - 1) * d + d := by
    calc
      n * d = ((n - 1) + 1) * d := by
        exact congrArg (fun k => k * d) hn
      _ = (n - 1) * d + d := by rw [Nat.add_mul, one_mul]
  rw [hmul] at hsum
  have hcancel :
      Module.finrank F2 (LinearMap.ker (totalSumLinear n M)) =
        (n - 1) * d := by
    apply Nat.add_left_cancel (n := d)
    simpa [Nat.add_comm] using hsum
  simpa [d] using hcancel

theorem card_totalSum_ker {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Nat.card (↥(LinearMap.ker (totalSumLinear n M))) =
      2 ^ ((n - 1) * Module.finrank F2 M) := by
  classical
  calc
    Nat.card (↥(LinearMap.ker (totalSumLinear n M))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.ker (totalSumLinear n M)) :=
      Module.natCard_eq_pow_finrank
        (K := F2) (V := LinearMap.ker (totalSumLinear n M))
    _ = 2 ^ ((n - 1) * Module.finrank F2 M) := by
      rw [finrank_totalSum_ker M]
      simp [F2]

noncomputable def cyclicAntiderivative (n : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] (g : ZMod n → M) :
    ZMod n → M :=
  fun t => ∑ k ∈ Finset.range t.val, g (k : ZMod n)

private theorem zmod_sum_eq_sum_range {n : Nat} [NeZero n] {M : Type}
    [AddCommMonoid M] (g : ZMod n → M) :
    (∑ t : ZMod n, g t) =
      ∑ k ∈ Finset.range n, g (k : ZMod n) := by
  classical
  cases n with
  | zero =>
      cases NeZero.ne 0 rfl
  | succ n =>
      have hcomp :
          (∑ i : Fin (n + 1),
              g ((ZMod.finEquiv (n + 1)) i)) =
            ∑ t : ZMod (n + 1), g t := by
        exact Equiv.sum_comp (ZMod.finEquiv (n + 1)).toEquiv g
      rw [← hcomp]
      calc
        (∑ i : Fin (n + 1), g ((ZMod.finEquiv (n + 1)) i))
            = ∑ i : Fin (n + 1), g ((i : Nat) : ZMod (n + 1)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              congr 1
              apply ZMod.val_injective (n + 1)
              rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
              change (i : Nat) = (i : Nat)
              rfl
        _ = ∑ k ∈ Finset.range (n + 1), g (k : ZMod (n + 1)) := by
              exact
                Fin.sum_univ_eq_sum_range
                  (fun k : Nat => g (k : ZMod (n + 1))) (n + 1)

theorem cyclicDiff_cyclicAntiderivative_of_sum_zero {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] (g : ZMod n → M)
    (hsum : (∑ t : ZMod n, g t) = 0) :
    cyclicDiff n M (cyclicAntiderivative n M g) = g := by
  classical
  ext t
  have ht_cast : t + 1 = ((t.val + 1 : Nat) : ZMod n) := by
    rw [← ZMod.natCast_zmod_val t]
    simp [Nat.cast_succ]
  by_cases hlt : t.val + 1 < n
  · have hval : (t + 1).val = t.val + 1 := by
      rw [ht_cast]
      exact ZMod.val_natCast_of_lt hlt
    let S : M := ∑ k ∈ Finset.range t.val, g (k : ZMod n)
    have hlast : g ((t.val : Nat) : ZMod n) = g t := by
      rw [ZMod.natCast_zmod_val]
    calc
      cyclicDiff n M (cyclicAntiderivative n M g) t
          = S + (∑ k ∈ Finset.range (t.val + 1), g (k : ZMod n)) := by
            simp [cyclicAntiderivative, S, hval]
      _ = S + (S + g ((t.val : Nat) : ZMod n)) := by
            rw [Finset.sum_range_succ]
      _ = (S + S) + g ((t.val : Nat) : ZMod n) := by abel
      _ = g t := by
            rw [add_self_eq_zero_of_module_F2 S]
            rw [hlast]
            simp
  · have hsucc : t.val + 1 = n := by
      have hle : n ≤ t.val + 1 := Nat.le_of_not_gt hlt
      have htn : t.val < n := ZMod.val_lt t
      omega
    have hnext : t + 1 = 0 := by
      rw [ht_cast, hsucc]
      simp
    let S : M := ∑ k ∈ Finset.range t.val, g (k : ZMod n)
    have hsum_range :
        (∑ k ∈ Finset.range n, g (k : ZMod n)) = 0 := by
      rw [← zmod_sum_eq_sum_range g]
      exact hsum
    have hSg : S + g t = 0 := by
      have htmp :
          (∑ k ∈ Finset.range (t.val + 1), g (k : ZMod n)) = 0 := by
        rw [hsucc]
        exact hsum_range
      rw [Finset.sum_range_succ] at htmp
      simpa [S] using htmp
    calc
      cyclicDiff n M (cyclicAntiderivative n M g) t
          = S := by
            simp [cyclicAntiderivative, S, hnext]
      _ = S + 0 := by simp
      _ = S + (g t + g t) := by
            rw [add_self_eq_zero_of_module_F2 (g t)]
      _ = (S + g t) + g t := by abel
      _ = g t := by
            rw [hSg]
            simp

theorem cyclicDiff_range_iff_sum_zero {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] (g : ZMod n → M) :
    (∃ f : ZMod n → M, cyclicDiff n M f = g) ↔
      (∑ t : ZMod n, g t) = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact cyclicDiff_sum_zero M f
  · intro hsum
    exact ⟨cyclicAntiderivative n M g,
      cyclicDiff_cyclicAntiderivative_of_sum_zero M g hsum⟩

theorem cyclicDiff_fiber_nonempty_iff_sum_zero {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] (g : ZMod n → M) :
    Nonempty { f : ZMod n → M // cyclicDiff n M f = g } ↔
      (∑ t : ZMod n, g t) = 0 := by
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    rw [← hf]
    exact cyclicDiff_sum_zero M f
  · intro hsum
    exact ⟨⟨cyclicAntiderivative n M g,
      cyclicDiff_cyclicAntiderivative_of_sum_zero M g hsum⟩⟩

theorem card_cyclicDiff_fiber_of_sum_zero {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (g : ZMod n → M) (hsum : (∑ t : ZMod n, g t) = 0) :
    Nat.card { f : ZMod n → M // cyclicDiff n M f = g } =
      2 ^ Module.finrank F2 M :=
  card_cyclicDiff_fiber_of_solution M g (cyclicAntiderivative n M g)
    (cyclicDiff_cyclicAntiderivative_of_sum_zero M g hsum)

theorem cyclicDiff_range_eq_totalSum_ker {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] :
    LinearMap.range (cyclicDiff n M) = LinearMap.ker (totalSumLinear n M) := by
  classical
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    change (∑ t : ZMod n, cyclicDiff n M f t) = 0
    exact cyclicDiff_sum_zero M f
  · intro hg
    have hsum : (∑ t : ZMod n, g t) = 0 := by
      change totalSumLinear n M g = 0 at hg
      simpa using hg
    exact (cyclicDiff_range_iff_sum_zero M g).2 hsum

theorem cyclicDiff_mem_range_iff_totalSum_eq_zero {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] (g : ZMod n → M) :
    g ∈ LinearMap.range (cyclicDiff n M) ↔ totalSumLinear n M g = 0 := by
  rw [cyclicDiff_range_eq_totalSum_ker M]
  rfl

theorem cyclicDiff_fiber_nonempty_iff_totalSum_eq_zero {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] (g : ZMod n → M) :
    Nonempty { f : ZMod n → M // cyclicDiff n M f = g } ↔
      totalSumLinear n M g = 0 := by
  simpa using cyclicDiff_fiber_nonempty_iff_sum_zero M g

theorem card_cyclicDiff_fiber_of_totalSum_eq_zero {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (g : ZMod n → M) (hg : totalSumLinear n M g = 0) :
    Nat.card { f : ZMod n → M // cyclicDiff n M f = g } =
      2 ^ Module.finrank F2 M := by
  apply card_cyclicDiff_fiber_of_sum_zero M g
  simpa using hg

theorem range_comp_eq_range_of_surjective
    {P Q R : Type} [AddCommGroup P] [Module F2 P]
    [AddCommGroup Q] [Module F2 Q] [AddCommGroup R] [Module F2 R]
    (L : Q →ₗ[F2] R) (π : P →ₗ[F2] Q)
    (hπ : Function.Surjective π) :
    LinearMap.range (L.comp π) = LinearMap.range L := by
  ext r
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨π p, rfl⟩
  · rintro ⟨q, rfl⟩
    rcases hπ q with ⟨p, hp⟩
    exact ⟨p, by simp [LinearMap.comp_apply, hp]⟩

theorem cyclicDiff_comp_surjective_range_eq_totalSum_ker
    {n : Nat} [NeZero n] {P : Type}
    [AddCommGroup P] [Module F2 P]
    (M : Type) [AddCommGroup M] [Module F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π) :
    LinearMap.range ((cyclicDiff n M).comp π) =
      LinearMap.ker (totalSumLinear n M) := by
  rw [range_comp_eq_range_of_surjective (cyclicDiff n M) π hπ,
    cyclicDiff_range_eq_totalSum_ker M]

theorem finrank_range_cyclicDiff {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.range (cyclicDiff n M)) =
      (n - 1) * Module.finrank F2 M := by
  rw [cyclicDiff_range_eq_totalSum_ker M, finrank_totalSum_ker M]

theorem card_range_cyclicDiff {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Nat.card (↥(LinearMap.range (cyclicDiff n M))) =
      2 ^ ((n - 1) * Module.finrank F2 M) := by
  classical
  calc
    Nat.card (↥(LinearMap.range (cyclicDiff n M))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.range (cyclicDiff n M)) :=
      Module.natCard_eq_pow_finrank
        (K := F2) (V := LinearMap.range (cyclicDiff n M))
    _ = 2 ^ ((n - 1) * Module.finrank F2 M) := by
      rw [finrank_range_cyclicDiff M]
      simp [F2]

theorem finrank_range_cyclicDiff_comp_surjective
    {n : Nat} [NeZero n] {P : Type}
    [AddCommGroup P] [Module F2 P]
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π) :
    Module.finrank F2 (LinearMap.range ((cyclicDiff n M).comp π)) =
      (n - 1) * Module.finrank F2 M := by
  rw [cyclicDiff_comp_surjective_range_eq_totalSum_ker M π hπ,
    finrank_totalSum_ker M]

theorem card_range_cyclicDiff_comp_surjective
    {n : Nat} [NeZero n] {P : Type}
    [AddCommGroup P] [Module F2 P]
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π) :
    Nat.card (↥(LinearMap.range ((cyclicDiff n M).comp π))) =
      2 ^ ((n - 1) * Module.finrank F2 M) := by
  classical
  calc
    Nat.card (↥(LinearMap.range ((cyclicDiff n M).comp π))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.range ((cyclicDiff n M).comp π)) :=
      Module.natCard_eq_pow_finrank
        (K := F2) (V := LinearMap.range ((cyclicDiff n M).comp π))
    _ = 2 ^ ((n - 1) * Module.finrank F2 M) := by
      rw [finrank_range_cyclicDiff_comp_surjective M π hπ]
      simp [F2]

noncomputable def diagSum (a n : Nat) [NeZero n] :
    (Fin a → ZMod n) → ZMod n :=
  fun x => ∑ i : Fin a, x i

theorem diagSum_eq_first_add_tail {a n : Nat} [NeZero n]
    (ha : 0 < a) (x : Fin a → ZMod n) :
    diagSum a n x =
      x ⟨0, ha⟩ +
        ∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, x i.1 := by
  classical
  unfold diagSum
  let first : Fin a := ⟨0, ha⟩
  have hsplit :
      (∑ i ∈ (Finset.univ : Finset (Fin a)), x i) =
        x first +
          ∑ i ∈ (Finset.univ : Finset (Fin a)) \ {first}, x i :=
    Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ : Finset (Fin a)))
      (i := first)
      (f := x)
      (by intro h; simp at h)
  have htail :
      (∑ i ∈ (Finset.univ : Finset (Fin a)) \ {first}, x i) =
        ∑ i : { i : Fin a // i ≠ first }, x i.1 := by
    refine Finset.sum_subtype ((Finset.univ : Finset (Fin a)) \ {first}) ?_ x
    intro i
    simp [first]
  calc
    (∑ i : Fin a, x i) =
        ∑ i ∈ (Finset.univ : Finset (Fin a)), x i := by
      simp
    _ = x first + ∑ i ∈ (Finset.univ : Finset (Fin a)) \ {first}, x i :=
      hsplit
    _ = x first + ∑ i : { i : Fin a // i ≠ first }, x i.1 := by
      rw [htail]
    _ = x ⟨0, ha⟩ + ∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, x i.1 := rfl

noncomputable def diagSumFiberTailEquiv {a n : Nat} [NeZero n]
    (ha : 0 < a) (t : ZMod n) :
    { x : Fin a → ZMod n // diagSum a n x = t } ≃
      ({ i : Fin a // i ≠ ⟨0, ha⟩ } → ZMod n) := by
  classical
  refine
  { toFun := fun x i => x.1 i.1
    invFun := fun y =>
      let tail : ZMod n := ∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, y i
      ⟨fun i =>
          if h : i = (⟨0, ha⟩ : Fin a) then t - tail else y ⟨i, h⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · dsimp
    rw [diagSum_eq_first_add_tail ha]
    have htail :
        (∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ },
          (if h : i.1 = (⟨0, ha⟩ : Fin a) then
            t - ∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, y i
          else y ⟨i.1, h⟩)) =
        ∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, y i := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [dif_neg i.2]
    rw [htail]
    change t - (∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, y i) +
        (∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, y i) = t
    abel
  · intro x
    apply Subtype.ext
    funext i
    by_cases hi : i = (⟨0, ha⟩ : Fin a)
    · subst i
      dsimp
      change
        t - (∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, x.1 i.1) =
          x.1 ⟨0, ha⟩
      have hsum :
          x.1 ⟨0, ha⟩ +
              (∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, x.1 i.1) = t := by
        exact (diagSum_eq_first_add_tail ha x.1).symm.trans x.2
      have hfirst :
          x.1 ⟨0, ha⟩ =
            t - (∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, x.1 i.1) := by
        have hcongr := congrArg
          (fun z : ZMod n =>
            z - (∑ i : { i : Fin a // i ≠ ⟨0, ha⟩ }, x.1 i.1)) hsum
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcongr
      exact hfirst.symm
    · dsimp
      rw [if_neg hi]
  · intro y
    funext i
    dsimp
    rw [dif_neg i.2]

theorem diagSum_tailIndex_card {a : Nat} (ha : 0 < a) :
    Fintype.card { i : Fin a // i ≠ ⟨0, ha⟩ } = a - 1 := by
  classical
  let first : Fin a := ⟨0, ha⟩
  have hsub : Subsingleton { i : Fin a // i = first } := by
    refine ⟨?_⟩
    intro x y
    apply Subtype.ext
    rw [x.2, y.2]
  have hone : Fintype.card { i : Fin a // i = first } = 1 :=
    Fintype.card_ofSubsingleton (⟨first, rfl⟩ : { i : Fin a // i = first })
  have hcompl := Fintype.card_subtype_compl (fun i : Fin a => i = first)
  simpa [first, hone] using hcompl

theorem diagSum_fiber_card {a n : Nat} [NeZero n]
    (ha : 0 < a) (t : ZMod n) :
    Fintype.card { x : Fin a → ZMod n // diagSum a n x = t } = n ^ (a - 1) := by
  classical
  calc
    Fintype.card { x : Fin a → ZMod n // diagSum a n x = t } =
        Fintype.card ({ i : Fin a // i ≠ ⟨0, ha⟩ } → ZMod n) :=
      Fintype.card_congr (diagSumFiberTailEquiv ha t)
    _ = Fintype.card (ZMod n) ^
          Fintype.card { i : Fin a // i ≠ ⟨0, ha⟩ } := by
      rw [Fintype.card_fun]
    _ = n ^ (a - 1) := by
      rw [ZMod.card, diagSum_tailIndex_card ha]

theorem finrank_tupleFunctionSpace {a n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 ((Fin a → ZMod n) → M) =
      n ^ a * Module.finrank F2 M := by
  classical
  let d := Module.finrank F2 M
  calc
    Module.finrank F2 ((Fin a → ZMod n) → M)
        = ∑ _ : (Fin a → ZMod n), d := by
            simpa [d] using
              (Module.finrank_pi_fintype
                (R := F2) (M := fun _ : (Fin a → ZMod n) => M))
    _ = Fintype.card (Fin a → ZMod n) * d := by simp
    _ = n ^ a * d := by
            have hcard :
                Fintype.card (Fin a → ZMod n) = n ^ a := by
              rw [Fintype.card_fun]
              simp [ZMod.card]
            rw [hcard]

noncomputable def fiberRep (a n : Nat) [NeZero n] (ha : 0 < a) (t : ZMod n) :
    Fin a → ZMod n :=
  fun i => if i = ⟨0, ha⟩ then t else 0

@[simp] theorem fiberRep_first {a n : Nat} [NeZero n]
    (ha : 0 < a) (t : ZMod n) :
    fiberRep a n ha t ⟨0, ha⟩ = t := by
  simp [fiberRep]

theorem fiberRep_ne_first {a n : Nat} [NeZero n]
    (ha : 0 < a) (t : ZMod n) {i : Fin a}
    (hi : i ≠ ⟨0, ha⟩) :
    fiberRep a n ha t i = 0 := by
  simp [fiberRep, hi]

theorem diagSum_fiberRep {a n : Nat} [NeZero n]
    (ha : 0 < a) (t : ZMod n) :
    diagSum a n (fiberRep a n ha t) = t := by
  classical
  unfold diagSum
  rw [Fintype.sum_eq_single (⟨0, ha⟩ : Fin a)]
  · simp [fiberRep]
  · intro i hi
    simp [fiberRep, hi]

def supportedAtFirst {a n : Nat} [NeZero n] (ha : 0 < a)
    (x : Fin a → ZMod n) : Prop :=
  ∀ i : Fin a, i ≠ ⟨0, ha⟩ → x i = 0

theorem diagSum_eq_first_of_supported {a n : Nat} [NeZero n]
    (ha : 0 < a) {x : Fin a → ZMod n}
    (hx : supportedAtFirst ha x) :
    diagSum a n x = x ⟨0, ha⟩ := by
  classical
  unfold diagSum
  rw [Fintype.sum_eq_single (⟨0, ha⟩ : Fin a)]
  intro i hi
  exact hx i hi

theorem eq_fiberRep_of_supported {a n : Nat} [NeZero n]
    (ha : 0 < a) {t : ZMod n}
    (x : { x : Fin a → ZMod n // diagSum a n x = t })
    (hx : supportedAtFirst ha x.1) :
    x.1 = fiberRep a n ha t := by
  funext i
  have hdiag : diagSum a n x.1 = x.1 ⟨0, ha⟩ :=
    diagSum_eq_first_of_supported ha hx
  have hfirst : x.1 ⟨0, ha⟩ = t := by
    rw [← hdiag]
    exact x.2
  by_cases hi : i = ⟨0, ha⟩
  · rw [hi]
    simp [fiberRep, hfirst]
  · rw [hx i hi]
    simp [fiberRep, hi]

noncomputable def fiberSum (a n : Nat) [NeZero n] (M : Type)
    [AddCommMonoid M] [Module F2 M] :
    (((Fin a → ZMod n) → M) →ₗ[F2] (ZMod n → M)) where
  toFun f := fun t =>
    ∑ x : { x : Fin a → ZMod n // diagSum a n x = t }, f x.1
  map_add' f g := by
    ext t
    simp [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c f := by
    ext t
    simp [Pi.smul_apply, Finset.smul_sum]

@[simp] theorem fiberSum_apply {a n : Nat} [NeZero n] {M : Type}
    [AddCommMonoid M] [Module F2 M]
    (f : (Fin a → ZMod n) → M) (t : ZMod n) :
    fiberSum a n M f t =
      ∑ x : { x : Fin a → ZMod n // diagSum a n x = t }, f x.1 := rfl

noncomputable def fiberSumSection {a n : Nat} [NeZero n] (ha : 0 < a)
    {M : Type} [Zero M] (g : ZMod n → M) :
    (Fin a → ZMod n) → M := by
  classical
  exact fun x => if supportedAtFirst ha x then g (x ⟨0, ha⟩) else 0

theorem fiberSum_section_apply {a n : Nat} [NeZero n] (ha : 0 < a)
    {M : Type} [AddCommMonoid M] [Module F2 M] (g : ZMod n → M)
    (t : ZMod n) :
    fiberSum a n M (fiberSumSection ha g) t = g t := by
  classical
  let x0 : { x : Fin a → ZMod n // diagSum a n x = t } :=
    ⟨fiberRep a n ha t, diagSum_fiberRep ha t⟩
  rw [fiberSum_apply, Fintype.sum_eq_single x0]
  · simp [x0, fiberSumSection, supportedAtFirst, fiberRep]
  · intro x hxne
    by_cases hsupp : supportedAtFirst ha x.1
    · have hxeq : x.1 = fiberRep a n ha t :=
        eq_fiberRep_of_supported ha x hsupp
      have hx0 : x = x0 := by
        apply Subtype.ext
        exact hxeq
      exact (hxne hx0).elim
    · simp [fiberSumSection, hsupp]

theorem fiberSum_surjective {a n : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommMonoid M] [Module F2 M] :
    Function.Surjective (fiberSum a n M) := by
  intro g
  refine ⟨fiberSumSection ha g, ?_⟩
  ext t
  exact fiberSum_section_apply ha g t

theorem cyclicDiff_after_fiberSum_reaches_cyclicDiff {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type) [AddCommGroup M] [Module F2 M] :
    ∀ g : ZMod n → M,
      ∃ f : (Fin a → ZMod n) → M,
        cyclicDiff n M (fiberSum a n M f) = cyclicDiff n M g := by
  intro g
  rcases fiberSum_surjective ha M g with ⟨f, hf⟩
  exact ⟨f, by rw [hf]⟩

theorem cyclicDiff_comp_fiberSum_range_eq_totalSum_ker {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type) [AddCommGroup M] [Module F2 M] :
    LinearMap.range ((cyclicDiff n M).comp (fiberSum a n M)) =
      LinearMap.ker (totalSumLinear n M) :=
  cyclicDiff_comp_surjective_range_eq_totalSum_ker M
    (fiberSum a n M) (fiberSum_surjective ha M)

theorem finrank_range_cyclicDiff_comp_fiberSum {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2
        (LinearMap.range ((cyclicDiff n M).comp (fiberSum a n M))) =
      (n - 1) * Module.finrank F2 M := by
  rw [cyclicDiff_comp_fiberSum_range_eq_totalSum_ker ha M,
    finrank_totalSum_ker M]

theorem card_range_cyclicDiff_comp_fiberSum {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Nat.card
        (↥(LinearMap.range ((cyclicDiff n M).comp (fiberSum a n M)))) =
      2 ^ ((n - 1) * Module.finrank F2 M) := by
  classical
  calc
    Nat.card
        (↥(LinearMap.range ((cyclicDiff n M).comp (fiberSum a n M)))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.range ((cyclicDiff n M).comp (fiberSum a n M))) :=
      Module.natCard_eq_pow_finrank
        (K := F2)
        (V := LinearMap.range ((cyclicDiff n M).comp (fiberSum a n M)))
    _ = 2 ^ ((n - 1) * Module.finrank F2 M) := by
      rw [finrank_range_cyclicDiff_comp_fiberSum ha M]
      simp [F2]

theorem finrank_ker_cyclicDiff_comp_fiberSum {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2
        (LinearMap.ker ((cyclicDiff n M).comp (fiberSum a n M))) =
      n ^ a * Module.finrank F2 M -
        (n - 1) * Module.finrank F2 M := by
  classical
  let L := (cyclicDiff n M).comp (fiberSum a n M)
  let d := Module.finrank F2 M
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hdom :
      Module.finrank F2 ((Fin a → ZMod n) → M) = n ^ a * d := by
    simpa [d] using finrank_tupleFunctionSpace (a := a) (n := n) M
  have hrange :
      Module.finrank F2 (LinearMap.range L) = (n - 1) * d := by
    simpa [L, d] using
      finrank_range_cyclicDiff_comp_fiberSum (a := a) (n := n) ha M
  rw [hdom, hrange] at hsum
  let K := Module.finrank F2 (LinearMap.ker L)
  let R := (n - 1) * d
  let D := n ^ a * d
  have hsum' : R + K = D := by
    simpa [K, R, D] using hsum
  have hK : K = D - R := by
    omega
  simpa [L, d, K, R, D] using hK

theorem card_ker_cyclicDiff_comp_fiberSum {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Nat.card
        (↥(LinearMap.ker ((cyclicDiff n M).comp (fiberSum a n M)))) =
      2 ^ (n ^ a * Module.finrank F2 M -
        (n - 1) * Module.finrank F2 M) := by
  classical
  calc
    Nat.card
        (↥(LinearMap.ker ((cyclicDiff n M).comp (fiberSum a n M)))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.ker ((cyclicDiff n M).comp (fiberSum a n M))) :=
      Module.natCard_eq_pow_finrank
        (K := F2)
        (V := LinearMap.ker ((cyclicDiff n M).comp (fiberSum a n M)))
    _ = 2 ^ (n ^ a * Module.finrank F2 M -
        (n - 1) * Module.finrank F2 M) := by
      rw [finrank_ker_cyclicDiff_comp_fiberSum ha M]
      simp [F2]

theorem card_cyclicDiff_comp_fiberSum_fiber_of_totalSum_eq_zero
    {a n : Nat} [NeZero n] (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (g : ZMod n → M) (hg : totalSumLinear n M g = 0) :
    Nat.card
        { f : (Fin a → ZMod n) → M //
          cyclicDiff n M (fiberSum a n M f) = g } =
      2 ^ (n ^ a * Module.finrank F2 M -
        (n - 1) * Module.finrank F2 M) := by
  classical
  let L := (cyclicDiff n M).comp (fiberSum a n M)
  let h := cyclicAntiderivative n M g
  let f0 := fiberSumSection ha h
  have hsum : (∑ t : ZMod n, g t) = 0 := by
    simpa using hg
  have hfiber : fiberSum a n M f0 = h := by
    ext t
    exact fiberSum_section_apply ha h t
  have hf0 : L f0 = g := by
    change cyclicDiff n M (fiberSum a n M f0) = g
    rw [hfiber]
    exact cyclicDiff_cyclicAntiderivative_of_sum_zero M g hsum
  change
    Nat.card { f : (Fin a → ZMod n) → M // L f = g } =
      2 ^ (n ^ a * Module.finrank F2 M -
        (n - 1) * Module.finrank F2 M)
  calc
    Nat.card { f : (Fin a → ZMod n) → M // L f = g } =
        Nat.card (↥(LinearMap.ker L)) :=
      card_linearMap_fiber_eq_card_ker_of_solution L g f0 hf0
    _ = 2 ^ (n ^ a * Module.finrank F2 M -
        (n - 1) * Module.finrank F2 M) := by
      simpa [L] using card_ker_cyclicDiff_comp_fiberSum (a := a) (n := n) ha M

theorem cyclicDiff_after_fiberSum_range_iff_sum_zero {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type) [AddCommGroup M] [Module F2 M]
    (g : ZMod n → M) :
    (∃ f : (Fin a → ZMod n) → M,
        cyclicDiff n M (fiberSum a n M f) = g) ↔
      (∑ t : ZMod n, g t) = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact cyclicDiff_sum_zero M (fiberSum a n M f)
  · intro hsum
    rcases (cyclicDiff_range_iff_sum_zero M g).2 hsum with ⟨h, hh⟩
    rcases fiberSum_surjective ha M h with ⟨f, hf⟩
    exact ⟨f, by rw [hf]; exact hh⟩

noncomputable def paramCyclicDiff (C : Type) (n : Nat) [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] :
    (C → ZMod n → M) →ₗ[F2] (C → ZMod n → M) where
  toFun f := fun c => cyclicDiff n M (f c)
  map_add' f g := by
    ext c t
    simp [Pi.add_apply, add_assoc, add_left_comm, add_comm]
  map_smul' r f := by
    ext c t
    simp [Pi.smul_apply, smul_add]

@[simp] theorem paramCyclicDiff_apply {C : Type} {n : Nat} [NeZero n]
    {M : Type} [AddCommGroup M] [Module F2 M]
    (f : C → ZMod n → M) (c : C) (t : ZMod n) :
    paramCyclicDiff C n M f c t = f c t + f c (t + 1) := rfl

noncomputable def paramTotalSumLinear (C : Type) (n : Nat) [NeZero n]
    (M : Type) [AddCommMonoid M] [Module F2 M] :
    (C → ZMod n → M) →ₗ[F2] (C → M) where
  toFun f := fun c => totalSumLinear n M (f c)
  map_add' f g := by
    ext c
    simp [Pi.add_apply, totalSumLinear_apply, Finset.sum_add_distrib]
  map_smul' r f := by
    ext c
    simp [Pi.smul_apply, totalSumLinear_apply, Finset.smul_sum]

@[simp] theorem paramTotalSumLinear_apply {C : Type} {n : Nat} [NeZero n]
    {M : Type} [AddCommMonoid M] [Module F2 M]
    (f : C → ZMod n → M) (c : C) :
    paramTotalSumLinear C n M f c = ∑ t : ZMod n, f c t := rfl

theorem paramTotalSumLinear_surjective {C : Type} {n : Nat} [NeZero n]
    (M : Type) [AddCommMonoid M] [Module F2 M] :
    Function.Surjective (paramTotalSumLinear C n M) := by
  classical
  intro m
  refine ⟨fun c t => if t = 0 then m c else 0, ?_⟩
  ext c
  rw [paramTotalSumLinear_apply]
  rw [Fintype.sum_eq_single (0 : ZMod n)]
  · simp
  · intro t ht
    simp [ht]

theorem finrank_paramFunctionSpace (C : Type) [Fintype C] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (C → M) =
      Fintype.card C * Module.finrank F2 M := by
  classical
  let d := Module.finrank F2 M
  calc
    Module.finrank F2 (C → M)
        = ∑ _ : C, d := by
            simpa [d] using
              (Module.finrank_pi_fintype
                (R := F2) (M := fun _ : C => M))
    _ = Fintype.card C * d := by simp

theorem finrank_paramZModFunctionSpace (C : Type) [Fintype C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (C → ZMod n → M) =
      Fintype.card C * (n * Module.finrank F2 M) := by
  classical
  let d := Module.finrank F2 M
  have hz :
      Module.finrank F2 (ZMod n → M) = n * d := by
    calc
      Module.finrank F2 (ZMod n → M)
          = ∑ _ : ZMod n, d := by
              simpa [d] using
                (Module.finrank_pi_fintype
                  (R := F2) (M := fun _ : ZMod n => M))
      _ = n * d := by
              simp [ZMod.card, Finset.card_univ]
  calc
    Module.finrank F2 (C → ZMod n → M)
        = ∑ _ : C, Module.finrank F2 (ZMod n → M) := by
            simpa using
              (Module.finrank_pi_fintype
                (R := F2) (M := fun _ : C => ZMod n → M))
    _ = Fintype.card C * (n * d) := by
            simp [hz]

noncomputable def contextSumLinear (C : Type) [Fintype C] (M : Type)
    [AddCommMonoid M] [Module F2 M] :
    (C → M) →ₗ[F2] M where
  toFun f := ∑ c : C, f c
  map_add' f g := by
    simp [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r f := by
    rw [Finset.smul_sum]
    rfl

@[simp] theorem contextSumLinear_apply (C : Type) [Fintype C]
    {M : Type} [AddCommMonoid M] [Module F2 M] (f : C → M) :
    contextSumLinear C M f = ∑ c : C, f c := rfl

theorem contextSumLinear_surjective (C : Type) [Fintype C] [Nonempty C]
    (M : Type) [AddCommMonoid M] [Module F2 M] :
    Function.Surjective (contextSumLinear C M) := by
  classical
  intro m
  let c0 : C := Classical.choice (inferInstance : Nonempty C)
  refine ⟨fun c => if c = c0 then m else 0, ?_⟩
  rw [contextSumLinear_apply]
  rw [Fintype.sum_eq_single c0]
  · simp
  · intro c hc
    simp [hc]

noncomputable def contextSummedCyclicDiff (C : Type) [Fintype C]
    (n : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    (C → ZMod n → M) →ₗ[F2] (ZMod n → M) :=
  (cyclicDiff n M).comp (contextSumLinear C (ZMod n → M))

@[simp] theorem contextSummedCyclicDiff_apply
    (C : Type) [Fintype C] {n : Nat} [NeZero n] {M : Type}
    [AddCommGroup M] [Module F2 M] (f : C → ZMod n → M)
    (t : ZMod n) :
    contextSummedCyclicDiff C n M f t =
      (∑ c : C, f c t) + ∑ c : C, f c (t + 1) := by
  simp [contextSummedCyclicDiff, cyclicDiff, contextSumLinear,
    Finset.sum_apply]

theorem contextSummedCyclicDiff_range_eq_cyclicDiff_range
    (C : Type) [Fintype C] [Nonempty C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    LinearMap.range (contextSummedCyclicDiff C n M) =
      LinearMap.range (cyclicDiff n M) := by
  rw [contextSummedCyclicDiff,
    range_comp_eq_range_of_surjective (cyclicDiff n M)
      (contextSumLinear C (ZMod n → M))
      (contextSumLinear_surjective C (ZMod n → M))]

theorem finrank_range_contextSummedCyclicDiff
    (C : Type) [Fintype C] [Nonempty C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.range (contextSummedCyclicDiff C n M)) =
      (n - 1) * Module.finrank F2 M := by
  rw [contextSummedCyclicDiff_range_eq_cyclicDiff_range C M,
    finrank_range_cyclicDiff M]

theorem finrank_ker_contextSummedCyclicDiff
    (C : Type) [Fintype C] [Nonempty C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.ker (contextSummedCyclicDiff C n M)) =
      Fintype.card C * (n * Module.finrank F2 M) -
        (n - 1) * Module.finrank F2 M := by
  classical
  let L := contextSummedCyclicDiff C n M
  let d := Module.finrank F2 M
  let D := Fintype.card C * (n * d)
  let R := (n - 1) * d
  let K := Module.finrank F2 (LinearMap.ker L)
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hdomain :
      Module.finrank F2 (C → ZMod n → M) = D := by
    simpa [D, d] using finrank_paramZModFunctionSpace C M
  have hrange :
      Module.finrank F2 (LinearMap.range L) = R := by
    simpa [L, R, d] using
      finrank_range_contextSummedCyclicDiff C M
  rw [hdomain, hrange] at hsum
  have hK : K = D - R := by
    omega
  simpa [L, K, D, R, d] using hK

theorem card_ker_contextSummedCyclicDiff
    (C : Type) [Fintype C] [Nonempty C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Nat.card (↥(LinearMap.ker (contextSummedCyclicDiff C n M))) =
      2 ^ (Fintype.card C * (n * Module.finrank F2 M) -
        (n - 1) * Module.finrank F2 M) := by
  classical
  calc
    Nat.card (↥(LinearMap.ker (contextSummedCyclicDiff C n M))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.ker (contextSummedCyclicDiff C n M)) :=
      Module.natCard_eq_pow_finrank
        (K := F2) (V := LinearMap.ker (contextSummedCyclicDiff C n M))
    _ = 2 ^ (Fintype.card C * (n * Module.finrank F2 M) -
        (n - 1) * Module.finrank F2 M) := by
      rw [finrank_ker_contextSummedCyclicDiff C M]
      simp [F2]

theorem card_ker_contextSummedCyclicDiff_F2
    (C : Type) [Fintype C] [Nonempty C]
    {n : Nat} [NeZero n] :
    Nat.card (↥(LinearMap.ker (contextSummedCyclicDiff C n F2))) =
      2 ^ (Fintype.card C * n - (n - 1)) := by
  simpa [F2, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    card_ker_contextSummedCyclicDiff C (n := n) F2

theorem finrank_paramTotalSum_ker (C : Type) [Fintype C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.ker (paramTotalSumLinear C n M)) =
      Fintype.card C * ((n - 1) * Module.finrank F2 M) := by
  classical
  let d := Module.finrank F2 M
  let ccard := Fintype.card C
  have hsum :=
    LinearMap.finrank_range_add_finrank_ker (paramTotalSumLinear C n M)
  have hrange :
      Module.finrank F2 (LinearMap.range (paramTotalSumLinear C n M)) =
        ccard * d := by
    rw [LinearMap.range_eq_top.2 (paramTotalSumLinear_surjective M),
      finrank_top]
    simp [ccard, d, finrank_paramFunctionSpace C M]
  have hdomain :
      Module.finrank F2 (C → ZMod n → M) = ccard * (n * d) := by
    simpa [ccard, d] using finrank_paramZModFunctionSpace C M
  rw [hrange, hdomain] at hsum
  have hnpos : 0 < n := NeZero.pos n
  have hn : n * d = (n - 1) * d + d := by
    have hn' : n = (n - 1) + 1 := by
      omega
    calc
      n * d = ((n - 1) + 1) * d := by
        exact congrArg (fun k => k * d) hn'
      _ = (n - 1) * d + d := by rw [Nat.add_mul, one_mul]
  have hdom_split :
      ccard * (n * d) = ccard * ((n - 1) * d) + ccard * d := by
    rw [hn, Nat.mul_add]
  rw [hdom_split] at hsum
  have hcancel :
      Module.finrank F2 (LinearMap.ker (paramTotalSumLinear C n M)) =
        ccard * ((n - 1) * d) := by
    apply Nat.add_left_cancel (n := ccard * d)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
  simpa [ccard, d] using hcancel

theorem paramCyclicDiff_range_eq_paramTotalSum_ker
    (C : Type) {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    LinearMap.range (paramCyclicDiff C n M) =
      LinearMap.ker (paramTotalSumLinear C n M) := by
  classical
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    ext c
    change totalSumLinear n M (cyclicDiff n M (f c)) = 0
    simpa using cyclicDiff_sum_zero M (f c)
  · intro hg
    refine ⟨fun c => cyclicAntiderivative n M (g c), ?_⟩
    ext c t
    have hsum : (∑ t : ZMod n, g c t) = 0 := by
      have hc :=
        congrArg (fun h : C → M => h c) (LinearMap.mem_ker.mp hg)
      change totalSumLinear n M (g c) = 0 at hc
      simpa using hc
    exact congrArg (fun h : ZMod n → M => h t)
      (cyclicDiff_cyclicAntiderivative_of_sum_zero M (g c) hsum)

theorem finrank_range_paramCyclicDiff (C : Type) [Fintype C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.range (paramCyclicDiff C n M)) =
      Fintype.card C * ((n - 1) * Module.finrank F2 M) := by
  rw [paramCyclicDiff_range_eq_paramTotalSum_ker C M,
    finrank_paramTotalSum_ker C M]

noncomputable def paramFiberSum (C : Type) (a n : Nat) [NeZero n]
    (M : Type) [AddCommMonoid M] [Module F2 M] :
    (C → (Fin a → ZMod n) → M) →ₗ[F2] (C → ZMod n → M) where
  toFun f := fun c => fiberSum a n M (f c)
  map_add' f g := by
    ext c t
    simp [Pi.add_apply, fiberSum_apply, Finset.sum_add_distrib]
  map_smul' r f := by
    ext c t
    simp [Pi.smul_apply, fiberSum_apply, Finset.smul_sum]

@[simp] theorem paramFiberSum_apply {C : Type} {a n : Nat} [NeZero n]
    {M : Type} [AddCommMonoid M] [Module F2 M]
    (f : C → (Fin a → ZMod n) → M) (c : C) (t : ZMod n) :
    paramFiberSum C a n M f c t =
      ∑ x : { x : Fin a → ZMod n // diagSum a n x = t }, f c x.1 := rfl

theorem paramFiberSum_surjective (C : Type) {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type) [AddCommMonoid M] [Module F2 M] :
    Function.Surjective (paramFiberSum C a n M) := by
  intro g
  refine ⟨fun c => fiberSumSection ha (g c), ?_⟩
  ext c t
  exact fiberSum_section_apply ha (g c) t

theorem paramCyclicDiff_comp_paramFiberSum_range_eq_paramTotalSum_ker
    (C : Type) {a n : Nat} [NeZero n] (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] :
    LinearMap.range ((paramCyclicDiff C n M).comp (paramFiberSum C a n M)) =
      LinearMap.ker (paramTotalSumLinear C n M) := by
  rw [range_comp_eq_range_of_surjective (paramCyclicDiff C n M)
      (paramFiberSum C a n M) (paramFiberSum_surjective C ha M),
    paramCyclicDiff_range_eq_paramTotalSum_ker C M]

theorem finrank_paramTupleFunctionSpace (C : Type) [Fintype C]
    {a n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (C → (Fin a → ZMod n) → M) =
      Fintype.card C * (n ^ a * Module.finrank F2 M) := by
  classical
  let d := Module.finrank F2 M
  have htuple :
      Module.finrank F2 ((Fin a → ZMod n) → M) = n ^ a * d := by
    simpa [d] using finrank_tupleFunctionSpace (a := a) (n := n) M
  calc
    Module.finrank F2 (C → (Fin a → ZMod n) → M)
        = ∑ _ : C, Module.finrank F2 ((Fin a → ZMod n) → M) := by
            simpa using
              (Module.finrank_pi_fintype
                (R := F2) (M := fun _ : C => (Fin a → ZMod n) → M))
    _ = Fintype.card C * (n ^ a * d) := by
            simp [htuple]

theorem finrank_range_paramCyclicDiff_comp_paramFiberSum
    (C : Type) [Fintype C] {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2
        (LinearMap.range
          ((paramCyclicDiff C n M).comp (paramFiberSum C a n M))) =
      Fintype.card C * ((n - 1) * Module.finrank F2 M) := by
  rw [paramCyclicDiff_comp_paramFiberSum_range_eq_paramTotalSum_ker C ha M,
    finrank_paramTotalSum_ker C M]

theorem finrank_ker_paramCyclicDiff_comp_paramFiberSum
    (C : Type) [Fintype C] {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2
        (LinearMap.ker
          ((paramCyclicDiff C n M).comp (paramFiberSum C a n M))) =
      Fintype.card C * (n ^ a * Module.finrank F2 M) -
        Fintype.card C * ((n - 1) * Module.finrank F2 M) := by
  classical
  let L := (paramCyclicDiff C n M).comp (paramFiberSum C a n M)
  let d := Module.finrank F2 M
  let D := Fintype.card C * (n ^ a * d)
  let R := Fintype.card C * ((n - 1) * d)
  let K := Module.finrank F2 (LinearMap.ker L)
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hdom :
      Module.finrank F2 (C → (Fin a → ZMod n) → M) = D := by
    simpa [D, d] using finrank_paramTupleFunctionSpace C (a := a) (n := n) M
  have hrange :
      Module.finrank F2 (LinearMap.range L) = R := by
    simpa [L, R, d] using
      finrank_range_paramCyclicDiff_comp_paramFiberSum C ha M
  rw [hdom, hrange] at hsum
  have hK : K = D - R := by
    omega
  simpa [L, K, D, R, d] using hK

theorem card_ker_paramCyclicDiff_comp_paramFiberSum
    (C : Type) [Fintype C] {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Nat.card
        (↥(LinearMap.ker
          ((paramCyclicDiff C n M).comp (paramFiberSum C a n M)))) =
      2 ^ (Fintype.card C * (n ^ a * Module.finrank F2 M) -
        Fintype.card C * ((n - 1) * Module.finrank F2 M)) := by
  classical
  calc
    Nat.card
        (↥(LinearMap.ker
          ((paramCyclicDiff C n M).comp (paramFiberSum C a n M)))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.ker
            ((paramCyclicDiff C n M).comp (paramFiberSum C a n M))) :=
      Module.natCard_eq_pow_finrank
        (K := F2)
        (V := LinearMap.ker
          ((paramCyclicDiff C n M).comp (paramFiberSum C a n M)))
    _ = 2 ^ (Fintype.card C * (n ^ a * Module.finrank F2 M) -
        Fintype.card C * ((n - 1) * Module.finrank F2 M)) := by
      rw [finrank_ker_paramCyclicDiff_comp_paramFiberSum C ha M]
      simp [F2]

theorem card_paramCyclicDiff_comp_paramFiberSum_fiber_of_totalSum_eq_zero
    (C : Type) [Fintype C] {a n : Nat} [NeZero n]
    (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (g : C → ZMod n → M) (hg : paramTotalSumLinear C n M g = 0) :
    Nat.card
        { f : C → (Fin a → ZMod n) → M //
          paramCyclicDiff C n M (paramFiberSum C a n M f) = g } =
      2 ^ (Fintype.card C * (n ^ a * Module.finrank F2 M) -
        Fintype.card C * ((n - 1) * Module.finrank F2 M)) := by
  classical
  let L := (paramCyclicDiff C n M).comp (paramFiberSum C a n M)
  let h := fun c => cyclicAntiderivative n M (g c)
  let f0 : C → (Fin a → ZMod n) → M := fun c => fiberSumSection ha (h c)
  have hfiber : paramFiberSum C a n M f0 = h := by
    ext c t
    exact fiberSum_section_apply ha (h c) t
  have hf0 : L f0 = g := by
    change paramCyclicDiff C n M (paramFiberSum C a n M f0) = g
    rw [hfiber]
    ext c t
    have hsum : (∑ t : ZMod n, g c t) = 0 := by
      have hc := congrArg (fun q : C → M => q c) hg
      change totalSumLinear n M (g c) = 0 at hc
      simpa using hc
    exact congrArg (fun q : ZMod n → M => q t)
      (cyclicDiff_cyclicAntiderivative_of_sum_zero M (g c) hsum)
  change
    Nat.card { f : C → (Fin a → ZMod n) → M // L f = g } =
      2 ^ (Fintype.card C * (n ^ a * Module.finrank F2 M) -
        Fintype.card C * ((n - 1) * Module.finrank F2 M))
  calc
    Nat.card { f : C → (Fin a → ZMod n) → M // L f = g } =
        Nat.card (↥(LinearMap.ker L)) :=
      card_linearMap_fiber_eq_card_ker_of_solution L g f0 hf0
    _ = 2 ^ (Fintype.card C * (n ^ a * Module.finrank F2 M) -
        Fintype.card C * ((n - 1) * Module.finrank F2 M)) := by
      simpa [L] using card_ker_paramCyclicDiff_comp_paramFiberSum C ha M

end RawLinearAlgebra

end TreeGraph
