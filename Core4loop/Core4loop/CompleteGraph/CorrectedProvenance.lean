import Core4loop.CompleteGraph.CorrectedProvenance.Singleton
import Core4loop.CompleteGraph.CorrectedProvenance.Odd
import Core4loop.CompleteGraph.CorrectedProvenance.EvenAllLarge

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

noncomputable section

private theorem X4SourceZ_eq_X4PaperOldZ_add_K4CorrectionZ
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 <= n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    X4SourceZ a b c d n =
      X4PaperOldZ a b c d n + K4CorrectionZ n a b c d := by
  by_cases ha1 : a = 1
  · subst a
    rw [X4SourceZ_of_a_eq_one rfl, K4CorrectionZ_of_a_eq_one rfl]
    exact k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_a_one hb hc hd
  by_cases hb1 : b = 1
  · subst b
    rw [X4SourceZ_of_a_ne_one_b_eq_one ha1 rfl,
      K4CorrectionZ_of_a_ne_one_b_eq_one ha1 rfl]
    exact k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_b_one ha hc hd
  by_cases hc1 : c = 1
  · subst c
    rw [X4SourceZ_of_ab_ne_one_c_eq_one ha1 hb1 rfl,
      K4CorrectionZ_of_ab_ne_one_c_eq_one ha1 hb1 rfl]
    exact k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_c_one ha hb hd
  by_cases hd1 : d = 1
  · subst d
    rw [X4SourceZ_of_abc_ne_one_d_eq_one ha1 hb1 hc1 rfl,
      K4CorrectionZ_of_abc_ne_one_d_eq_one ha1 hb1 hc1 rfl]
    exact k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_d_one ha hb hc
  have ha2 : 2 <= a := by omega
  have hb2 : 2 <= b := by omega
  have hc2 : 2 <= c := by omega
  have hd2 : 2 <= d := by omega
  by_cases hnodd : Odd n
  · rw [X4SourceZ_of_all_ne_one_odd ha1 hb1 hc1 hd1 hnodd,
      K4CorrectionZ_of_all_ne_one_odd ha1 hb1 hc1 hd1 hnodd]
    rw [add_zero]
    exact k4OddRawExponentNat_eq_X4PaperOldZ
      hn2 hnodd ha2 hb2 hc2 hd2
  · have hneven : Even n := Nat.not_odd_iff_even.mp hnodd
    rw [X4SourceZ_of_all_ne_one_even ha1 hb1 hc1 hd1 hneven,
      K4CorrectionZ_of_all_ne_one_even ha1 hb1 hc1 hd1 hneven]
    rw [k4EvenAllLargeRawExponentNat_eq_X4PaperOldZ_add_correction
      hn2 hneven ha2 hb2 hc2 hd2]
    ring

theorem K4CorrectionZ_of_odd
    {n a b c d : Nat} (hn : Odd n) :
    K4CorrectionZ n a b c d = 0 := by
  by_cases ha1 : a = 1
  · rw [K4CorrectionZ_of_a_eq_one ha1]
    exact k4ThetaCorrectionZ_of_odd hn
  by_cases hb1 : b = 1
  · rw [K4CorrectionZ_of_a_ne_one_b_eq_one ha1 hb1]
    exact k4ThetaCorrectionZ_of_odd hn
  by_cases hc1 : c = 1
  · rw [K4CorrectionZ_of_ab_ne_one_c_eq_one ha1 hb1 hc1]
    exact k4ThetaCorrectionZ_of_odd hn
  by_cases hd1 : d = 1
  · rw [K4CorrectionZ_of_abc_ne_one_d_eq_one ha1 hb1 hc1 hd1]
    exact k4ThetaCorrectionZ_of_odd hn
  exact K4CorrectionZ_of_all_ne_one_odd ha1 hb1 hc1 hd1 hn

theorem K4CorrectionZ_of_two_singletons
    {n a b c d : Nat}
    (h : (a = 1 ∧ b = 1) ∨ (a = 1 ∧ c = 1) ∨
      (a = 1 ∧ d = 1) ∨ (b = 1 ∧ c = 1) ∨
      (b = 1 ∧ d = 1) ∨ (c = 1 ∧ d = 1)) :
    K4CorrectionZ n a b c d = 0 := by
  rcases h with hab | hac | had | hbc | hbd | hcd
  · rcases hab with ⟨rfl, rfl⟩
    simp [K4CorrectionZ, k4ThetaCorrectionZ, k4GenericThetaZ, ThetaZ]
  · rcases hac with ⟨rfl, rfl⟩
    simp [K4CorrectionZ, k4ThetaCorrectionZ, k4GenericThetaZ, ThetaZ]
  · rcases had with ⟨rfl, rfl⟩
    simp [K4CorrectionZ, k4ThetaCorrectionZ, k4GenericThetaZ, ThetaZ]
  · rcases hbc with ⟨rfl, rfl⟩
    simp [K4CorrectionZ, k4ThetaCorrectionZ, k4GenericThetaZ, ThetaZ]
  · rcases hbd with ⟨rfl, rfl⟩
    simp [K4CorrectionZ, k4ThetaCorrectionZ, k4GenericThetaZ, ThetaZ]
  · rcases hcd with ⟨rfl, rfl⟩
    simp [K4CorrectionZ, k4ThetaCorrectionZ, k4GenericThetaZ, ThetaZ]

theorem K4CorrectionZ_of_even_a_one
    {n a b c d : Nat} (hn : Even n) (ha1 : a = 1)
    (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d) :
    K4CorrectionZ n a b c d = -(mZ n * ((n : Int) - 2)) := by
  rw [K4CorrectionZ_of_a_eq_one ha1]
  exact k4ThetaCorrectionZ_of_even_large hn hb2 hc2 hd2

theorem K4CorrectionZ_of_even_b_one
    {n a b c d : Nat} (hn : Even n) (hb1 : b = 1)
    (ha2 : 2 <= a) (hc2 : 2 <= c) (hd2 : 2 <= d) :
    K4CorrectionZ n a b c d = -(mZ n * ((n : Int) - 2)) := by
  rw [K4CorrectionZ_of_a_ne_one_b_eq_one (by omega) hb1]
  exact k4ThetaCorrectionZ_of_even_large hn ha2 hc2 hd2

theorem K4CorrectionZ_of_even_c_one
    {n a b c d : Nat} (hn : Even n) (hc1 : c = 1)
    (ha2 : 2 <= a) (hb2 : 2 <= b) (hd2 : 2 <= d) :
    K4CorrectionZ n a b c d = -(mZ n * ((n : Int) - 2)) := by
  rw [K4CorrectionZ_of_ab_ne_one_c_eq_one (by omega) (by omega) hc1]
  exact k4ThetaCorrectionZ_of_even_large hn ha2 hb2 hd2

theorem K4CorrectionZ_of_even_d_one
    {n a b c d : Nat} (hn : Even n) (hd1 : d = 1)
    (ha2 : 2 <= a) (hb2 : 2 <= b) (hc2 : 2 <= c) :
    K4CorrectionZ n a b c d = -(mZ n * ((n : Int) - 2)) := by
  rw [K4CorrectionZ_of_abc_ne_one_d_eq_one
    (by omega) (by omega) (by omega) hd1]
  exact k4ThetaCorrectionZ_of_even_large hn ha2 hb2 hc2

theorem K4CorrectionZ_of_even_all_large
    {n a b c d : Nat} (hn : Even n)
    (ha2 : 2 <= a) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d) :
    K4CorrectionZ n a b c d =
      -(mZ n * ((n : Int) - 2) * (3 * (n : Int) + 1)) := by
  exact K4CorrectionZ_of_all_ne_one_even
    (by omega) (by omega) (by omega) (by omega) hn

theorem X4CorrectedZ_eq_X4PaperOldZ_add_K4CorrectionZ
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 <= n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    X4CorrectedZ a b c d n =
      X4PaperOldZ a b c d n + K4CorrectionZ n a b c d := by
  unfold X4CorrectedZ
  exact X4SourceZ_eq_X4PaperOldZ_add_K4CorrectionZ hn2 ha hb hc hd

end
end Core4loop
