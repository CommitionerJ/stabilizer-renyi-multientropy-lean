import TreeGraph.Imbalance.FiberSum

namespace TreeGraph
namespace Imbalance

noncomputable def PiCoeff (n : Nat) {a : Nat} [NeZero n]
    (_ha : 0 < a) (C0 : Type) [Fintype C0] :
    ((Block n a × C0 → F2) →ₗ[F2] (Rep n × C0 → F2)) where
  toFun h := fun p =>
    ∑ x : Block n a, if diag n a x = p.1 then h (x, p.2) else 0
  map_add' h k := by
    classical
    ext p
    change
      (∑ x : Block n a, if diag n a x = p.1 then h (x, p.2) + k (x, p.2) else 0) =
        (∑ x : Block n a, if diag n a x = p.1 then h (x, p.2) else 0) +
          ∑ x : Block n a, if diag n a x = p.1 then k (x, p.2) else 0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases hx : diag n a x = p.1 <;> simp [hx]
  map_smul' r h := by
    classical
    ext p
    change
      (∑ x : Block n a, if diag n a x = p.1 then r * h (x, p.2) else 0) =
        r * ∑ x : Block n a, if diag n a x = p.1 then h (x, p.2) else 0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases hx : diag n a x = p.1 <;> simp [hx]

@[simp] theorem PiCoeff_apply (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (h : Block n a × C0 → F2) (p : Rep n × C0) :
    PiCoeff n ha C0 h p =
      ∑ x : Block n a, if diag n a x = p.1 then h (x, p.2) else 0 := rfl

theorem PiCoeff_surjective (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0] :
    Function.Surjective (PiCoeff n ha C0) := by
  classical
  intro g
  let h : Block n a × C0 → F2 := fun p =>
    if p.1 = diagSection n ha (diag n a p.1) then
      g (diag n a p.1, p.2)
    else
      0
  refine ⟨h, ?_⟩
  ext p
  rw [PiCoeff_apply]
  rw [Fintype.sum_eq_single (diagSection n ha p.1)]
  · simp [h, diag_diagSection]
  · intro x hx
    by_cases hdiag : diag n a x = p.1
    · simp [hdiag, h, hx]
    · simp [hdiag]

noncomputable def PiFull (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0] :
    ((Block n a × C0 → F2) →ₗ[F2]
      (Rep n → Module.Dual F2 (C0 → F2))) where
  toFun h := fun s =>
    TreeGraph.dotLinear C0 (fun y => PiCoeff n ha C0 h (s, y))
  map_add' h k := by
    classical
    funext s
    apply LinearMap.ext
    intro m
    change
      (∑ y : C0, m y *
        (∑ x : Block n a,
          if diag n a x = s then h (x, y) + k (x, y) else 0)) =
        (∑ y : C0, m y *
          (∑ x : Block n a, if diag n a x = s then h (x, y) else 0)) +
          ∑ y : C0, m y *
            (∑ x : Block n a, if diag n a x = s then k (x, y) else 0)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro y _
    have hinner :
        (∑ x : Block n a,
          if diag n a x = s then h (x, y) + k (x, y) else 0) =
          (∑ x : Block n a, if diag n a x = s then h (x, y) else 0) +
            ∑ x : Block n a, if diag n a x = s then k (x, y) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases hx : diag n a x = s <;> simp [hx]
    rw [hinner, mul_add]
  map_smul' r h := by
    classical
    funext s
    apply LinearMap.ext
    intro m
    change
      (∑ y : C0, m y *
        (∑ x : Block n a, if diag n a x = s then r * h (x, y) else 0)) =
        r * ∑ y : C0, m y *
          (∑ x : Block n a, if diag n a x = s then h (x, y) else 0)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y _
    have hinner :
        (∑ x : Block n a, if diag n a x = s then r * h (x, y) else 0) =
          r * ∑ x : Block n a, if diag n a x = s then h (x, y) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases hx : diag n a x = s <;> simp [hx]
    rw [hinner]
    ring

@[simp] theorem PiFull_apply (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (h : Block n a × C0 → F2) (s : Rep n) :
    PiFull n ha C0 h s =
      TreeGraph.dotLinear C0 (fun y => PiCoeff n ha C0 h (s, y)) := rfl

theorem PiFull_surjective (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0] :
    Function.Surjective (PiFull n ha C0) := by
  classical
  intro g
  let coeff : Rep n × C0 → F2 := fun p =>
    TreeGraph.linearFunctionalCoeff C0 (g p.1) p.2
  rcases PiCoeff_surjective n ha C0 coeff with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  funext s
  apply LinearMap.ext
  intro m
  have hcoeff :
      (fun y : C0 => PiCoeff n ha C0 h (s, y)) =
        TreeGraph.linearFunctionalCoeff C0 (g s) := by
    funext y
    have hp := congrArg (fun φ : Rep n × C0 → F2 => φ (s, y)) hh
    simpa [coeff] using hp
  rw [PiFull_apply, hcoeff]
  have hdot :=
    congrArg (fun ell : (C0 → F2) →ₗ[F2] F2 => ell m)
      (TreeGraph.linearFunctional_eq_dotLinear_coeff C0 (g s))
  simpa using hdot.symm

noncomputable def restrictDual {B : Type}
    [AddCommGroup B] [Module F2 B]
    (Msub : Submodule F2 B) :
    Module.Dual F2 B →ₗ[F2] Module.Dual F2 Msub :=
  Msub.subtype.dualMap

@[simp] theorem restrictDual_apply {B : Type}
    [AddCommGroup B] [Module F2 B]
    (Msub : Submodule F2 B)
    (ell : Module.Dual F2 B) (m : Msub) :
    restrictDual Msub ell m = ell m.1 := rfl

theorem dual_restrict_surjective {B : Type}
    [AddCommGroup B] [Module F2 B]
    (Msub : Submodule F2 B) :
    Function.Surjective (restrictDual Msub) := by
  exact LinearMap.dualMap_surjective_of_injective Msub.injective_subtype

noncomputable def PiSubmodule (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (Msub : Submodule F2 (C0 → F2)) :
    ((Block n a × C0 → F2) →ₗ[F2]
      (Rep n → Module.Dual F2 Msub)) where
  toFun h := fun s => restrictDual Msub (PiFull n ha C0 h s)
  map_add' h k := by
    ext s m
    have hPi :
        PiFull n ha C0 (h + k) s =
          PiFull n ha C0 h s + PiFull n ha C0 k s := by
      exact congrFun (map_add (PiFull n ha C0) h k) s
    rw [hPi]
    simp
  map_smul' r h := by
    ext s m
    have hPi :
        PiFull n ha C0 (r • h) s =
          r • PiFull n ha C0 h s := by
      exact congrFun (map_smul (PiFull n ha C0) r h) s
    rw [hPi]
    simp

@[simp] theorem PiSubmodule_apply (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (Msub : Submodule F2 (C0 → F2))
    (h : Block n a × C0 → F2) (s : Rep n) :
    PiSubmodule n ha C0 Msub h s =
      restrictDual Msub (PiFull n ha C0 h s) := rfl

theorem PiSubmodule_surjective (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (Msub : Submodule F2 (C0 → F2)) :
    Function.Surjective (PiSubmodule n ha C0 Msub) := by
  classical
  intro g
  have hsurj : ∀ s : Rep n,
      ∃ ell : Module.Dual F2 (C0 → F2),
        restrictDual Msub ell = g s := by
    intro s
    exact dual_restrict_surjective Msub (g s)
  choose ell hell using hsurj
  rcases PiFull_surjective n ha C0 ell with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  ext s m
  have hs := congrFun hh s
  have hrestr := congrArg (fun phi : Module.Dual F2 Msub => phi m) (hell s)
  rw [PiSubmodule_apply, hs]
  exact hrestr

end Imbalance
end TreeGraph
