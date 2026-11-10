import TreeGraph.Imbalance.Coordinates

namespace TreeGraph
namespace Imbalance

noncomputable def coordinateSum (n : Nat) {ι : Type} [Fintype ι]
    (s : ι → Rep n) : Rep n :=
  ∑ i : ι, s i

noncomputable def incidenceShear (n : Nat) [NeZero n]
    (ι : Type) [Fintype ι] :
    (Rep n × (ι → Rep n)) ≃ (Rep n × (ι → Rep n)) where
  toFun p := (p.1 + coordinateSum n p.2, p.2)
  invFun p := (p.1 - coordinateSum n p.2, p.2)
  left_inv p := by
    ext
    · simp [coordinateSum]
    · simp
  right_inv p := by
    ext
    · simp [coordinateSum]
    · simp

@[simp] theorem incidenceShear_apply (n : Nat) [NeZero n]
    (ι : Type) [Fintype ι] (p : Rep n × (ι → Rep n)) :
    incidenceShear n ι p = (p.1 + coordinateSum n p.2, p.2) := rfl

@[simp] theorem incidenceShear_symm_apply (n : Nat) [NeZero n]
    (ι : Type) [Fintype ι] (p : Rep n × (ι → Rep n)) :
    (incidenceShear n ι).symm p = (p.1 - coordinateSum n p.2, p.2) := rfl

theorem incidenceShear_alpha (n : Nat) [NeZero n]
    (ι : Type) [Fintype ι] (t : Rep n) (s : ι → Rep n) :
    (incidenceShear n ι (t, s)).1 = t + coordinateSum n s := rfl

theorem incidenceShear_visible (n : Nat) [NeZero n]
    (ι : Type) [Fintype ι] (t : Rep n) (s : ι → Rep n) :
    (incidenceShear n ι (t, s)).2 = s := rfl

theorem incidenceShear_symm_alpha (n : Nat) [NeZero n]
    (ι : Type) [Fintype ι] (alpha : Rep n) (u : ι → Rep n) :
    ((incidenceShear n ι).symm (alpha, u)).1 =
      alpha - coordinateSum n u := rfl

theorem incidenceShear_symm_visible (n : Nat) [NeZero n]
    (ι : Type) [Fintype ι] (alpha : Rep n) (u : ι → Rep n) :
    ((incidenceShear n ι).symm (alpha, u)).2 = u := rfl

theorem coordinateSum_update_sub_one (n : Nat) [NeZero n]
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (s : ι → Rep n) (i : ι) :
    coordinateSum n (Function.update s i (s i - 1)) =
      coordinateSum n s - 1 := by
  classical
  let u : Finset ι := Finset.univ
  have hi : i ∈ u := Finset.mem_univ i
  have h_erase :
      (∑ x ∈ u.erase i, Function.update s i (s i - 1) x) =
        ∑ x ∈ u.erase i, s x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
    simp [Function.update, hxi]
  have hupd :
      ∑ x ∈ u, Function.update s i (s i - 1) x =
        (∑ x ∈ u.erase i, s x) + (s i - 1) := by
    rw [← Finset.sum_erase_add u (Function.update s i (s i - 1)) hi]
    rw [h_erase]
    simp [Function.update]
  have horig :
      ∑ x ∈ u, s x = (∑ x ∈ u.erase i, s x) + s i := by
    rw [← Finset.sum_erase_add u s hi]
  have hupd_univ :
      (∑ x, Function.update s i (s i - 1) x) =
        (∑ x ∈ u.erase i, s x) + (s i - 1) := by
    simpa only [u] using hupd
  have horig_univ :
      (∑ x, s x) = (∑ x ∈ u.erase i, s x) + s i := by
    simpa only [u] using horig
  change (∑ x, Function.update s i (s i - 1) x) = (∑ x, s x) - 1
  rw [hupd_univ, horig_univ]
  abel

theorem incidenceShear_child_step (n : Nat) [NeZero n]
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (t : Rep n) (s : ι → Rep n) (i : ι) :
    incidenceShear n ι (t + 1, Function.update s i (s i - 1)) =
      (t + coordinateSum n s, Function.update s i (s i - 1)) := by
  apply Prod.ext
  · simp [coordinateSum_update_sub_one]
  · rfl

end Imbalance
end TreeGraph
