import Core4loop.TriangleCore.Phase
import Core4loop.ZeroSumSpaces.Matrix

namespace Core4loop
namespace TriangleCore

abbrev TriRootTarget (n s t : ℕ) :=
  TriYVec n s → TriZVec n t → F

abbrev TriYCoeff (n t : ℕ) [NeZero n] :=
  TriZVec n t → ZeroSumProfile n

abbrev TriZCoeff (n s : ℕ) [NeZero n] :=
  TriYVec n s → ZeroSumProfile n

noncomputable def TriYDiffEmbed {n s t : ℕ} [NeZero n] :
    TriYCoeff n t →ₗ[F] TriRootTarget n s t where
  toFun U := fun y z => (U z).1 (vecSum y)
  map_add' U V := by
    funext y z
    rfl
  map_smul' r U := by
    funext y z
    rfl

noncomputable def TriZDiffEmbed {n s t : ℕ} [NeZero n] :
    TriZCoeff n s →ₗ[F] TriRootTarget n s t where
  toFun V := fun y z => (V y).1 (vecSum z)
  map_add' U V := by
    funext y z
    rfl
  map_smul' r U := by
    funext y z
    rfl

noncomputable def TriYDiffSpace {n s t : ℕ} [NeZero n] :
    Submodule F (TriRootTarget n s t) :=
  LinearMap.range (TriYDiffEmbed (n := n) (s := s) (t := t))

noncomputable def TriZDiffSpace {n s t : ℕ} [NeZero n] :
    Submodule F (TriRootTarget n s t) :=
  LinearMap.range (TriZDiffEmbed (n := n) (s := s) (t := t))

theorem TriYDiffEmbed_injective {n s t : ℕ} [NeZero n] (hs : 0 < s) :
    Function.Injective (TriYDiffEmbed (n := n) (s := s) (t := t)) := by
  intro U V h
  funext z
  apply Subtype.ext
  funext sy
  rcases vecSum_surjective (n := n) (k := s) hs sy with ⟨y, hy⟩
  have hv := congrFun (congrFun h y) z
  simpa [TriYDiffEmbed, hy] using hv

theorem TriZDiffEmbed_injective {n s t : ℕ} [NeZero n] (ht : 0 < t) :
    Function.Injective (TriZDiffEmbed (n := n) (s := s) (t := t)) := by
  intro U V h
  funext y
  apply Subtype.ext
  funext sz
  rcases vecSum_surjective (n := n) (k := t) ht sz with ⟨z, hz⟩
  have hv := congrFun (congrFun h y) z
  simpa [TriZDiffEmbed, hz] using hv

lemma finrank_TriYCoeff {n t : ℕ} [NeZero n] :
    Module.finrank F (TriYCoeff n t) = n ^ t * (n - 1) := by
  calc
    Module.finrank F (TriYCoeff n t)
        = ∑ _ : TriZVec n t, Module.finrank F (ZeroSumProfile n) := by
            simp [TriYCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : TriZVec n t => ZeroSumProfile n)]
    _ = Fintype.card (TriZVec n t) * (n - 1) := by
            simp [finrank_ZeroSumProfile]
    _ = n ^ t * (n - 1) := by
            rw [card_vec]

lemma finrank_TriZCoeff {n s : ℕ} [NeZero n] :
    Module.finrank F (TriZCoeff n s) = n ^ s * (n - 1) := by
  calc
    Module.finrank F (TriZCoeff n s)
        = ∑ _ : TriYVec n s, Module.finrank F (ZeroSumProfile n) := by
            simp [TriZCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : TriYVec n s => ZeroSumProfile n)]
    _ = Fintype.card (TriYVec n s) * (n - 1) := by
            simp [finrank_ZeroSumProfile]
    _ = n ^ s * (n - 1) := by
            rw [card_vec]

theorem finrank_TriYDiffSpace {n s t : ℕ} [NeZero n] (hs : 0 < s) :
    Module.finrank F (TriYDiffSpace (n := n) (s := s) (t := t)) =
      (n - 1) * n ^ t := by
  calc
    Module.finrank F (TriYDiffSpace (n := n) (s := s) (t := t))
        = Module.finrank F (TriYCoeff n t) := by
            exact LinearMap.finrank_range_of_inj
              (TriYDiffEmbed_injective (n := n) (s := s) (t := t) hs)
    _ = (n - 1) * n ^ t := by
            rw [finrank_TriYCoeff]
            ring

theorem finrank_TriZDiffSpace {n s t : ℕ} [NeZero n] (ht : 0 < t) :
    Module.finrank F (TriZDiffSpace (n := n) (s := s) (t := t)) =
      (n - 1) * n ^ s := by
  calc
    Module.finrank F (TriZDiffSpace (n := n) (s := s) (t := t))
        = Module.finrank F (TriZCoeff n s) := by
            exact LinearMap.finrank_range_of_inj
              (TriZDiffEmbed_injective (n := n) (s := s) (t := t) ht)
    _ = (n - 1) * n ^ s := by
            rw [finrank_TriZCoeff]
            ring

noncomputable def TriPullYZ {n s t : ℕ} [NeZero n] :
    MatrixZeroSum n →ₗ[F] TriRootTarget n s t where
  toFun M := fun y z => M.1 (vecSum y) (vecSum z)
  map_add' M N := by
    funext y z
    rfl
  map_smul' r M := by
    funext y z
    rfl

theorem TriPullYZ_injective {n s t : ℕ} [NeZero n]
    (hs : 0 < s) (ht : 0 < t) :
    Function.Injective (TriPullYZ (n := n) (s := s) (t := t)) := by
  intro M N h
  apply Subtype.ext
  funext sy sz
  rcases vecSum_surjective (n := n) (k := s) hs sy with ⟨y, hy⟩
  rcases vecSum_surjective (n := n) (k := t) ht sz with ⟨z, hz⟩
  have hv := congrFun (congrFun h y) z
  simpa [TriPullYZ, hy, hz] using hv

theorem finrank_range_TriPullYZ {n s t : ℕ} [NeZero n]
    (hs : 0 < s) (ht : 0 < t) :
    Module.finrank F (LinearMap.range (TriPullYZ (n := n) (s := s) (t := t))) =
      (n - 1) ^ 2 := by
  calc
    Module.finrank F (LinearMap.range (TriPullYZ (n := n) (s := s) (t := t)))
        = Module.finrank F (MatrixZeroSum n) := by
            exact LinearMap.finrank_range_of_inj
              (TriPullYZ_injective (n := n) (s := s) (t := t) hs ht)
    _ = (n - 1) ^ 2 := finrank_MatrixZeroSum (n := n)

theorem range_TriPullYZ_le_inf_YZ {n s t : ℕ} [NeZero n] :
    LinearMap.range (TriPullYZ (n := n) (s := s) (t := t)) ≤
      TriYDiffSpace (n := n) (s := s) (t := t) ⊓
        TriZDiffSpace (n := n) (s := s) (t := t) := by
  intro f hf
  rcases hf with ⟨M, rfl⟩
  constructor
  · refine ⟨(fun z => ⟨fun sy => M.1 sy (vecSum z), ?_⟩), ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact matrix_col_zero M (vecSum z)
    · funext y z
      rfl
  · refine ⟨(fun y => ⟨fun sz => M.1 (vecSum y) sz, ?_⟩), ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact matrix_row_zero M (vecSum y)
    · funext y z
      rfl

theorem inf_YZ_le_range_TriPullYZ {n s t : ℕ} [NeZero n]
    (hs : 0 < s) (ht : 0 < t) :
    TriYDiffSpace (n := n) (s := s) (t := t) ⊓
        TriZDiffSpace (n := n) (s := s) (t := t) ≤
      LinearMap.range (TriPullYZ (n := n) (s := s) (t := t)) := by
  classical
  intro f hf
  rcases hf.1 with ⟨U, hU⟩
  rcases hf.2 with ⟨V, hV⟩
  let yOf : I n → TriYVec n s := fun sy =>
    Classical.choose (vecSum_surjective (n := n) (k := s) hs sy)
  let zOf : I n → TriZVec n t := fun sz =>
    Classical.choose (vecSum_surjective (n := n) (k := t) ht sz)
  have hyOf : ∀ sy : I n, vecSum (yOf sy) = sy := by
    intro sy
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := s) hs sy)
  have hzOf : ∀ sz : I n, vecSum (zOf sz) = sz := by
    intro sz
    exact Classical.choose_spec (vecSum_surjective (n := n) (k := t) ht sz)
  let M : MatrixZeroSum n :=
    ⟨fun sy sz => f (yOf sy) (zOf sz), by
      constructor
      · apply LinearMap.mem_ker.mpr
        funext sy
        calc
          (∑ sz : I n, f (yOf sy) (zOf sz))
              = ∑ sz : I n, (V (yOf sy)).1 sz := by
                  refine Finset.sum_congr rfl ?_
                  intro sz _
                  have hv := congrFun (congrFun hV (yOf sy)) (zOf sz)
                  exact (by simpa [TriZDiffEmbed, hzOf sz] using hv.symm)
          _ = 0 := by
                  exact LinearMap.mem_ker.mp (V (yOf sy)).2
      · apply LinearMap.mem_ker.mpr
        funext sz
        calc
          (∑ sy : I n, f (yOf sy) (zOf sz))
              = ∑ sy : I n, (U (zOf sz)).1 sy := by
                  refine Finset.sum_congr rfl ?_
                  intro sy _
                  have hu := congrFun (congrFun hU (yOf sy)) (zOf sz)
                  exact (by simpa [TriYDiffEmbed, hyOf sy] using hu.symm)
          _ = 0 := by
                  exact LinearMap.mem_ker.mp (U (zOf sz)).2⟩
  refine ⟨M, ?_⟩
  funext y z
  let sy : I n := vecSum y
  let sz : I n := vecSum z
  calc
    (TriPullYZ (n := n) (s := s) (t := t) M) y z
        = f (yOf sy) (zOf sz) := rfl
    _ = (U (zOf sz)).1 sy := by
          have hu := congrFun (congrFun hU (yOf sy)) (zOf sz)
          exact (by simpa [TriYDiffEmbed, sy, hyOf sy] using hu.symm)
    _ = f y (zOf sz) := by
          have hu := congrFun (congrFun hU y) (zOf sz)
          exact (by simpa [TriYDiffEmbed, sy] using hu)
    _ = (V y).1 sz := by
          have hv := congrFun (congrFun hV y) (zOf sz)
          exact (by simpa [TriZDiffEmbed, sz, hzOf sz] using hv.symm)
    _ = f y z := by
          have hv := congrFun (congrFun hV y) z
          exact (by simpa [TriZDiffEmbed, sz] using hv)

theorem range_TriPullYZ_eq_inf_YZ {n s t : ℕ} [NeZero n]
    (hs : 0 < s) (ht : 0 < t) :
    LinearMap.range (TriPullYZ (n := n) (s := s) (t := t)) =
      TriYDiffSpace (n := n) (s := s) (t := t) ⊓
        TriZDiffSpace (n := n) (s := s) (t := t) := by
  apply le_antisymm
  · exact range_TriPullYZ_le_inf_YZ (n := n) (s := s) (t := t)
  · exact inf_YZ_le_range_TriPullYZ (n := n) (s := s) (t := t) hs ht

theorem finrank_inf_TriYZ {n s t : ℕ} [NeZero n]
    (hs : 0 < s) (ht : 0 < t) :
    Module.finrank F
      (↑(TriYDiffSpace (n := n) (s := s) (t := t) ⊓
        TriZDiffSpace (n := n) (s := s) (t := t))) =
      (n - 1) ^ 2 := by
  rw [← range_TriPullYZ_eq_inf_YZ (n := n) (s := s) (t := t) hs ht]
  exact finrank_range_TriPullYZ (n := n) (s := s) (t := t) hs ht

theorem finrank_sup_TriYZ_add_finrank_inf {n s t : ℕ} [NeZero n]
    (hs : 0 < s) (ht : 0 < t) :
    Module.finrank F
        (↑(TriYDiffSpace (n := n) (s := s) (t := t) ⊔
          TriZDiffSpace (n := n) (s := s) (t := t)))
      + (n - 1) ^ 2 =
      (n - 1) * n ^ t + (n - 1) * n ^ s := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (TriYDiffSpace (n := n) (s := s) (t := t))
    (TriZDiffSpace (n := n) (s := s) (t := t))
  rw [finrank_inf_TriYZ (n := n) (s := s) (t := t) hs ht,
    finrank_TriYDiffSpace (n := n) (s := s) (t := t) hs,
    finrank_TriZDiffSpace (n := n) (s := s) (t := t) ht] at h
  exact h

noncomputable def TriKBMap {n r s t : ℕ} [NeZero n] :
    TriBFun n r t →ₗ[F] TriRootTarget n s t where
  toFun B := fun y z => ∑ p : TriPVec n r, (B p (vecSum y) z + B p (vecSum y + 1) z)
  map_add' B B' := by
    funext y z
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  map_smul' a B := by
    funext y z
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring

noncomputable def TriKCMap {n r s t : ℕ} [NeZero n] :
    TriCFun n r s →ₗ[F] TriRootTarget n s t where
  toFun C := fun y z => ∑ p : TriPVec n r, (C p y (vecSum z) + C p y (vecSum z + 1))
  map_add' C C' := by
    funext y z
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  map_smul' a C := by
    funext y z
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring

theorem range_TriKBMap_eq_TriYDiffSpace {n r s t : ℕ} [NeZero n] :
    LinearMap.range (TriKBMap (n := n) (r := r) (s := s) (t := t)) =
      TriYDiffSpace (n := n) (s := s) (t := t) := by
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨B, rfl⟩
    let U : TriYCoeff n t := fun z =>
      ⟨cycDiff (n := n) F (fun sy => ∑ p : TriPVec n r, B p sy z),
        cycDiff_mem_ZeroSumProfile (fun sy => ∑ p : TriPVec n r, B p sy z)⟩
    refine ⟨U, ?_⟩
    funext y z
    simp [TriKBMap, TriYDiffEmbed, U, cycDiff, Finset.sum_add_distrib]
  · intro f hf
    rcases hf with ⟨U, rfl⟩
    choose H hH using fun z =>
      show ∃ h : Profile n, cycDiff (n := n) F h = (U z).1 by
        have hm : (U z).1 ∈ LinearMap.range (cycDiff (n := n) F) := by
          rw [range_cycDiff_eq_ZeroSumProfile]
          exact (U z).2
        exact hm
    let B : TriBFun n r t := fun p sy z =>
      if p = (zeroVec : TriPVec n r) then H z sy else 0
    refine ⟨B, ?_⟩
    funext y z
    have hpoint := congrFun (hH z) (vecSum y)
    calc
      TriKBMap (n := n) (r := r) (s := s) (t := t) B y z
          = H z (vecSum y) + H z (vecSum y + 1) := by
              simp [TriKBMap, B, Finset.sum_add_distrib]
      _ = (U z).1 (vecSum y) := by
              simpa [cycDiff] using hpoint

theorem range_TriKCMap_eq_TriZDiffSpace {n r s t : ℕ} [NeZero n] :
    LinearMap.range (TriKCMap (n := n) (r := r) (s := s) (t := t)) =
      TriZDiffSpace (n := n) (s := s) (t := t) := by
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨C, rfl⟩
    let V : TriZCoeff n s := fun y =>
      ⟨cycDiff (n := n) F (fun sz => ∑ p : TriPVec n r, C p y sz),
        cycDiff_mem_ZeroSumProfile (fun sz => ∑ p : TriPVec n r, C p y sz)⟩
    refine ⟨V, ?_⟩
    funext y z
    simp [TriKCMap, TriZDiffEmbed, V, cycDiff, Finset.sum_add_distrib]
  · intro f hf
    rcases hf with ⟨V, rfl⟩
    choose H hH using fun y =>
      show ∃ h : Profile n, cycDiff (n := n) F h = (V y).1 by
        have hm : (V y).1 ∈ LinearMap.range (cycDiff (n := n) F) := by
          rw [range_cycDiff_eq_ZeroSumProfile]
          exact (V y).2
        exact hm
    let C : TriCFun n r s := fun p y sz =>
      if p = (zeroVec : TriPVec n r) then H y sz else 0
    refine ⟨C, ?_⟩
    funext y z
    have hpoint := congrFun (hH y) (vecSum z)
    calc
      TriKCMap (n := n) (r := r) (s := s) (t := t) C y z
          = H y (vecSum z) + H y (vecSum z + 1) := by
              simp [TriKCMap, C, Finset.sum_add_distrib]
      _ = (V y).1 (vecSum z) := by
              simpa [cycDiff] using hpoint

noncomputable def K_yz {n r s t : ℕ} [NeZero n] :
    (TriBFun n r t × TriCFun n r s) →ₗ[F] TriRootTarget n s t where
  toFun x := fun y z => TriKBMap x.1 y z + TriKCMap x.2 y z
  map_add' x y := by
    funext u v
    change
      TriKBMap (n := n) (r := r) (s := s) (t := t) (x.1 + y.1) u v
        + TriKCMap (n := n) (r := r) (s := s) (t := t) (x.2 + y.2) u v =
      (TriKBMap (n := n) (r := r) (s := s) (t := t) x.1 u v
        + TriKCMap (n := n) (r := r) (s := s) (t := t) x.2 u v)
      + (TriKBMap (n := n) (r := r) (s := s) (t := t) y.1 u v
        + TriKCMap (n := n) (r := r) (s := s) (t := t) y.2 u v)
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext u v
    change
      TriKBMap (n := n) (r := r) (s := s) (t := t) (a • x.1) u v
        + TriKCMap (n := n) (r := r) (s := s) (t := t) (a • x.2) u v =
      a • (TriKBMap (n := n) (r := r) (s := s) (t := t) x.1 u v
        + TriKCMap (n := n) (r := r) (s := s) (t := t) x.2 u v)
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    ring

theorem range_K_yz_eq_sup_YZ {n r s t : ℕ} [NeZero n] :
    LinearMap.range (K_yz (n := n) (r := r) (s := s) (t := t)) =
      TriYDiffSpace (n := n) (s := s) (t := t) ⊔
        TriZDiffSpace (n := n) (s := s) (t := t) := by
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨x, rfl⟩
    refine Submodule.mem_sup.mpr ⟨
      TriKBMap (n := n) (r := r) (s := s) (t := t) x.1, ?_,
      TriKCMap (n := n) (r := r) (s := s) (t := t) x.2, ?_, ?_⟩
    · rw [← range_TriKBMap_eq_TriYDiffSpace (n := n) (r := r) (s := s) (t := t)]
      exact ⟨x.1, rfl⟩
    · rw [← range_TriKCMap_eq_TriZDiffSpace (n := n) (r := r) (s := s) (t := t)]
      exact ⟨x.2, rfl⟩
    · rfl
  · intro f hf
    rcases Submodule.mem_sup.mp hf with ⟨fY, hfY, fZ, hfZ, rfl⟩
    rw [← range_TriKBMap_eq_TriYDiffSpace (n := n) (r := r) (s := s) (t := t)] at hfY
    rw [← range_TriKCMap_eq_TriZDiffSpace (n := n) (r := r) (s := s) (t := t)] at hfZ
    rcases hfY with ⟨B, rfl⟩
    rcases hfZ with ⟨C, rfl⟩
    refine ⟨(B, C), ?_⟩
    rfl

theorem finrank_range_K_yz_add_inf {n r s t : ℕ} [NeZero n]
    (hs : 0 < s) (ht : 0 < t) :
    Module.finrank F (LinearMap.range (K_yz (n := n) (r := r) (s := s) (t := t)))
      + (n - 1) ^ 2 =
      (n - 1) * n ^ t + (n - 1) * n ^ s := by
  rw [range_K_yz_eq_sup_YZ (n := n) (r := r) (s := s) (t := t)]
  exact finrank_sup_TriYZ_add_finrank_inf (n := n) (s := s) (t := t) hs ht

theorem finrank_domain_K_yz {n r s t : ℕ} [NeZero n] (hr : 0 < r) :
    Module.finrank F (TriBFun n r t × TriCFun n r s) =
      n ^ (r + t) + n ^ (r + s) := by
  rw [Module.finrank_prod]
  have hB :
      Module.finrank F (TriBFun n r t) =
        Fintype.card (TriPVec n r × I n × TriZVec n t) := by
    rw [← Module.finrank_fintype_fun_eq_card (R := F)
      (η := TriPVec n r × I n × TriZVec n t)]
    exact LinearEquiv.finrank_eq
      { toFun := fun B u => B u.1 u.2.1 u.2.2
        invFun := fun f p sy z => f (p, sy, z)
        map_add' := by intro B C; rfl
        map_smul' := by intro a B; rfl
        left_inv := by
          intro B
          funext p sy z
          rfl
        right_inv := by
          intro f
          funext u
          rcases u with ⟨p, sy, z⟩
          rfl }
  have hC :
      Module.finrank F (TriCFun n r s) =
        Fintype.card (TriPVec n r × TriYVec n s × I n) := by
    rw [← Module.finrank_fintype_fun_eq_card (R := F)
      (η := TriPVec n r × TriYVec n s × I n)]
    exact LinearEquiv.finrank_eq
      { toFun := fun C u => C u.1 u.2.1 u.2.2
        invFun := fun f p y sz => f (p, y, sz)
        map_add' := by intro C D; rfl
        map_smul' := by intro a C; rfl
        left_inv := by
          intro C
          funext p y sz
          rfl
        right_inv := by
          intro f
          funext u
          rcases u with ⟨p, y, sz⟩
          rfl }
  rw [hB, hC, card_triBIndex hr, card_triCIndex hr]

set_option synthInstance.maxHeartbeats 200000 in
-- The nested product domain makes rank-nullity instance synthesis expensive here.
theorem finrank_ker_K_yz_add {n r s t : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    Module.finrank F (LinearMap.ker (K_yz (n := n) (r := r) (s := s) (t := t)))
      + ((n - 1) * n ^ t + (n - 1) * n ^ s) =
      n ^ (r + t) + n ^ (r + s) + (n - 1) ^ 2 := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (K_yz (n := n) (r := r) (s := s) (t := t))
  have hrange := finrank_range_K_yz_add_inf
    (n := n) (r := r) (s := s) (t := t) hs ht
  rw [finrank_domain_K_yz (n := n) (r := r) (s := s) (t := t) hr] at hnull
  omega

end TriangleCore
end Core4loop
