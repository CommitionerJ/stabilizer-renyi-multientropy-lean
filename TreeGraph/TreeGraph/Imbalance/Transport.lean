import TreeGraph.Imbalance.MessageSpace

namespace TreeGraph
namespace Imbalance

noncomputable def precomposeLinearEquiv
    (A B V : Type) [AddCommMonoid V] [Module F2 V]
    (e : A ≃ B) :
    (B → V) ≃ₗ[F2] (A → V) :=
  LinearEquiv.funCongrLeft F2 V e

@[simp] theorem precomposeLinearEquiv_apply
    (A B V : Type) [AddCommMonoid V] [Module F2 V]
    (e : A ≃ B) (f : B → V) (a : A) :
    precomposeLinearEquiv A B V e f a = f (e a) := rfl

noncomputable def transportedSubmodule
    (A B V : Type) [AddCommMonoid V] [Module F2 V]
    (e : A ≃ B) (K : Submodule F2 (B → V)) :
    Submodule F2 (A → V) :=
  K.map (precomposeLinearEquiv A B V e).toLinearMap

noncomputable def transportedSubmoduleEquiv
    (A B V : Type) [AddCommMonoid V] [Module F2 V]
    (e : A ≃ B) (K : Submodule F2 (B → V)) :
    K ≃ₗ[F2] transportedSubmodule A B V e K := by
  unfold transportedSubmodule
  exact LinearEquiv.submoduleMap (precomposeLinearEquiv A B V e) K

theorem finrank_transportedSubmodule
    (A B V : Type) [AddCommMonoid V] [Module F2 V]
    (e : A ≃ B) (K : Submodule F2 (B → V)) :
    Module.finrank F2 (transportedSubmodule A B V e K) =
      Module.finrank F2 K := by
  exact (LinearEquiv.finrank_eq
    (transportedSubmoduleEquiv A B V e K)).symm

theorem transportedSubmodule_top
    (A B V : Type) [AddCommMonoid V] [Module F2 V]
    (e : A ≃ B) :
    transportedSubmodule A B V e ⊤ = ⊤ := by
  ext f
  constructor
  · intro _
    exact Submodule.mem_top
  · intro _
    rw [transportedSubmodule, Submodule.mem_map]
    exact ⟨fun b : B => f (e.symm b), Submodule.mem_top, by
      ext a
      simp [precomposeLinearEquiv]⟩

theorem mem_transportedSubmodule_iff
    (A B V : Type) [AddCommMonoid V] [Module F2 V]
    (e : A ≃ B) (K : Submodule F2 (B → V)) (f : A → V) :
    f ∈ transportedSubmodule A B V e K ↔
      ∃ g : B → V, g ∈ K ∧
        (fun a : A => g (e a)) = f := by
  constructor
  · intro hf
    rw [transportedSubmodule] at hf
    rw [Submodule.mem_map] at hf
    rcases hf with ⟨g, hgK, hg⟩
    exact ⟨g, hgK, by simpa [precomposeLinearEquiv] using hg⟩
  · rintro ⟨g, hgK, hg⟩
    rw [transportedSubmodule]
    rw [Submodule.mem_map]
    exact ⟨g, hgK, by simpa [precomposeLinearEquiv] using hg⟩

noncomputable def transportedByShear (n : Nat) [NeZero n]
    (ι V : Type) [Fintype ι] [AddCommMonoid V] [Module F2 V]
    (K : Submodule F2 ((Rep n × (ι → Rep n)) → V)) :
    Submodule F2 ((Rep n × (ι → Rep n)) → V) :=
  transportedSubmodule
    (Rep n × (ι → Rep n))
    (Rep n × (ι → Rep n))
    V
    (incidenceShear n ι)
    K

theorem mem_transportedByShear_iff (n : Nat) [NeZero n]
    (ι V : Type) [Fintype ι] [AddCommMonoid V] [Module F2 V]
    (K : Submodule F2 ((Rep n × (ι → Rep n)) → V))
    (f : (Rep n × (ι → Rep n)) → V) :
    f ∈ transportedByShear n ι V K ↔
      ∃ g : (Rep n × (ι → Rep n)) → V, g ∈ K ∧
        (fun x => g (incidenceShear n ι x)) = f := by
  exact
    mem_transportedSubmodule_iff
      (Rep n × (ι → Rep n))
      (Rep n × (ι → Rep n))
      V
      (incidenceShear n ι)
      K
      f

theorem finrank_transportedByShear (n : Nat) [NeZero n]
    (ι V : Type) [Fintype ι] [AddCommMonoid V] [Module F2 V]
    (K : Submodule F2 ((Rep n × (ι → Rep n)) → V)) :
    Module.finrank F2 (transportedByShear n ι V K) =
      Module.finrank F2 K := by
  unfold transportedByShear
  exact finrank_transportedSubmodule
    (Rep n × (ι → Rep n)) (Rep n × (ι → Rep n)) V
    (incidenceShear n ι) K

end Imbalance
end TreeGraph
