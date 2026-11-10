import Core4loop.TriangleLeaf.BCEncoding
import Core4loop.ZeroSumSpaces.Profile

namespace Core4loop
namespace TriangleLeaf

abbrev PassiveRaw (n d : ℕ) := WVec n d → F

noncomputable def PassiveDiffEmbed {n d : ℕ} [NeZero n] :
    ZeroSumProfile n →ₗ[F] PassiveRaw n d where
  toFun R := fun w => R.1 (vecSum w)
  map_add' R S := by
    funext w
    rfl
  map_smul' r R := by
    funext w
    rfl

noncomputable def PassiveDiffSpace (n d : ℕ) [NeZero n] :
    Submodule F (PassiveRaw n d) :=
  LinearMap.range (PassiveDiffEmbed (n := n) (d := d))

abbrev PassiveQuot (n d : ℕ) [NeZero n] :=
  PassiveRaw n d ⧸ PassiveDiffSpace n d

theorem PassiveDiffEmbed_injective {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Function.Injective (PassiveDiffEmbed (n := n) (d := d)) := by
  intro R S h
  apply Subtype.ext
  funext s
  rcases vecSum_surjective (n := n) (k := d) hd s with ⟨w, hw⟩
  have hv := congrFun h w
  simpa [PassiveDiffEmbed, hw] using hv

theorem finrank_PassiveRaw {n d : ℕ} [NeZero n] :
    Module.finrank F (PassiveRaw n d) = n ^ d := by
  calc
    Module.finrank F (PassiveRaw n d)
        = Fintype.card (WVec n d) := by
            rw [← Module.finrank_fintype_fun_eq_card (R := F) (η := WVec n d)]
    _ = n ^ d := card_vec n d

theorem finrank_PassiveDiffSpace {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (PassiveDiffSpace n d) = n - 1 := by
  calc
    Module.finrank F (PassiveDiffSpace n d)
        = Module.finrank F (ZeroSumProfile n) := by
            exact LinearMap.finrank_range_of_inj
              (PassiveDiffEmbed_injective (n := n) (d := d) hd)
    _ = n - 1 := finrank_ZeroSumProfile

theorem finrank_PassiveQuot_add {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (PassiveQuot n d) + (n - 1) = n ^ d := by
  have h :=
    Submodule.finrank_quotient_add_finrank
      (PassiveDiffSpace (n := n) (d := d))
  rw [finrank_PassiveDiffSpace (n := n) (d := d) hd,
    finrank_PassiveRaw (n := n) (d := d)] at h
  exact h

theorem finrank_PassiveQuot {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (PassiveQuot n d) = n ^ d - (n - 1) := by
  have h := finrank_PassiveQuot_add (n := n) (d := d) hd
  omega

end TriangleLeaf
end Core4loop
