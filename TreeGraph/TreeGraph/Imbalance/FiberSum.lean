import TreeGraph.Imbalance.CyclicDifference

namespace TreeGraph
namespace Imbalance

noncomputable def diag (n a : Nat) (x : Block n a) : Rep n :=
  ∑ j : Fin a, x j

def diagSection (n : Nat) {a : Nat} (ha : 0 < a) (t : Rep n) :
    Block n a :=
  fun j => if j = ⟨0, ha⟩ then t else 0

@[simp] theorem diag_diagSection (n : Nat) {a : Nat} (ha : 0 < a)
    (t : Rep n) :
    diag n a (diagSection n ha t) = t := by
  classical
  unfold diag diagSection
  rw [Fintype.sum_eq_single (⟨0, ha⟩ : Fin a)]
  · simp
  · intro j hj
    simp [hj]

noncomputable def fiberSum (n : Nat) {a : Nat} [NeZero n] (_ha : 0 < a)
    (M : Type) [AddCommMonoid M] [Module F2 M] :
    (Block n a → M) →ₗ[F2] (Rep n → M) where
  toFun f := fun s =>
    ∑ x : Block n a, if diag n a x = s then f x else 0
  map_add' f g := by
    classical
    ext s
    change
      (∑ x : Block n a, if diag n a x = s then f x + g x else 0) =
        (∑ x : Block n a, if diag n a x = s then f x else 0) +
          ∑ x : Block n a, if diag n a x = s then g x else 0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases h : diag n a x = s <;> simp [h]
  map_smul' r f := by
    classical
    ext s
    change
      (∑ x : Block n a, if diag n a x = s then r • f x else 0) =
        r • ∑ x : Block n a, if diag n a x = s then f x else 0
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases h : diag n a x = s <;> simp [h]

@[simp] theorem fiberSum_apply (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (M : Type) [AddCommMonoid M] [Module F2 M]
    (f : Block n a → M) (s : Rep n) :
    fiberSum n ha M f s =
      ∑ x : Block n a, if diag n a x = s then f x else 0 := rfl

theorem fiberSum_surjective (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (M : Type) [AddCommMonoid M] [Module F2 M] :
    Function.Surjective (fiberSum n ha M) := by
  classical
  intro g
  let f : Block n a → M := fun x =>
    if x = diagSection n ha (diag n a x) then g (diag n a x) else 0
  refine ⟨f, ?_⟩
  ext s
  rw [fiberSum_apply]
  rw [Fintype.sum_eq_single (diagSection n ha s)]
  · simp [f, diag_diagSection]
  · intro x hx
    by_cases hdiag : diag n a x = s
    · simp [hdiag, f, hx]
    · simp [hdiag]

end Imbalance
end TreeGraph
