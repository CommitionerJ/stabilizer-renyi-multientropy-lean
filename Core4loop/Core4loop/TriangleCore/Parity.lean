import Core4loop.TriangleCore.Phase

namespace Core4loop
namespace TriangleCore

def specialBranch (r s t n : ℕ) : Prop :=
  Even n ∧ 2 ≤ r ∧ 2 ≤ s ∧ 2 ≤ t

instance specialBranchDecidable (r s t n : ℕ) :
    Decidable (specialBranch r s t n) := by
  unfold specialBranch
  infer_instance

lemma ThetaZ_eq_of_special
    {r s t n : ℕ} (h : specialBranch r s t n) :
    ThetaZ r s t n = 3 * (mZ n) ^ 2 := by
  unfold ThetaZ specialBranch at *
  simp [h]

lemma ThetaZ_eq_of_not_special
    {r s t n : ℕ} (h : ¬ specialBranch r s t n) :
    ThetaZ r s t n = mZ n * (2 * (n : ℤ) - 1) := by
  unfold ThetaZ specialBranch at *
  simp [h]

theorem triangleLeaf_specialBranch_iff
    {a b c d n : ℕ} (ha : 0 < a) (hd : 0 < d) :
    specialBranch (a + d) b c n ↔ Even n ∧ 2 ≤ b ∧ 2 ≤ c := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  · intro h
    refine ⟨h.1, ?_, h.2.1, h.2.2⟩
    omega

lemma ThetaZ_triangleLeaf_eq_of_even_large
    {a b c d n : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hn : Even n) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ThetaZ (a + d) b c n = 3 * (mZ n) ^ 2 := by
  apply ThetaZ_eq_of_special
  rw [triangleLeaf_specialBranch_iff (a := a) (b := b) (c := c) (d := d) ha hd]
  exact ⟨hn, hb, hc⟩

lemma ThetaZ_triangleLeaf_eq_of_not_even_or_small
    {a b c d n : ℕ} (ha : 0 < a) (hd : 0 < d)
    (h : ¬ (Even n ∧ 2 ≤ b ∧ 2 ≤ c)) :
    ThetaZ (a + d) b c n = mZ n * (2 * (n : ℤ) - 1) := by
  apply ThetaZ_eq_of_not_special
  rwa [triangleLeaf_specialBranch_iff (a := a) (b := b) (c := c) (d := d) ha hd]

end TriangleCore
end Core4loop
