import Core3loop.PhaseReduction
import No16.Main

open scoped BigOperators

namespace Core3loop

noncomputable def site222EquivQuint (n : ℕ) : Site 2 2 2 n ≃ No16.Quint n where
  toFun xyz := ⟨xyz.1 0, xyz.2.1 0, xyz.2.1 1, xyz.2.2 0, xyz.2.2 1⟩
  invFun u := ((fun _ : Fin 1 => u.1), No13Migration.vec2 u.2.1 u.2.2.1,
    No13Migration.vec2 u.2.2.2.1 u.2.2.2.2)
  left_inv := by
    intro xyz
    rcases xyz with ⟨x, y, z⟩
    simp [No13Migration.xCoord_two_eta, No13Migration.vec2_eta]
  right_inv := by
    intro u
    rcases u with ⟨u1, u2, u3, u4, u5⟩
    simp [No13Migration.vec2]

noncomputable def abc222NormalFormEquivNo16NFData (n : ℕ) [NeZero n] :
    ABCNormalForm 2 2 2 n ≃ No16.NFData n where
  toFun nf :=
    { A := fun u2 u3 u4 u5 => nf.1 (No13Migration.vec2 u2 u3, No13Migration.vec2 u4 u5)
      B := fun u1 t u4 u5 =>
        nf.2.1 ((fun _ : Fin 1 => u1), t, No13Migration.vec2 u4 u5)
      C := fun u1 u2 u3 r =>
        nf.2.2 ((fun _ : Fin 1 => u1), No13Migration.vec2 u2 u3, r) }
  invFun nf :=
    (fun yz : YCoord 2 n × ZCoord 2 n =>
      nf.A (yz.1 0) (yz.1 1) (yz.2 0) (yz.2 1),
      (fun bz : XCoord 2 n × I n × ZCoord 2 n =>
        nf.B (bz.1 0) bz.2.1 (bz.2.2 0) (bz.2.2 1),
        fun cy : XCoord 2 n × YCoord 2 n × I n =>
          nf.C (cy.1 0) (cy.2.1 0) (cy.2.1 1) cy.2.2))
  left_inv := by
    intro nf
    rcases nf with ⟨A, B, C⟩
    apply Prod.ext
    · funext yz
      rcases yz with ⟨y, z⟩
      simp [No13Migration.vec2_eta]
    · apply Prod.ext
      · funext bz
        rcases bz with ⟨x, t, z⟩
        simp [No13Migration.xCoord_two_eta, No13Migration.vec2_eta]
      · funext cy
        rcases cy with ⟨x, y, r⟩
        simp [No13Migration.xCoord_two_eta, No13Migration.vec2_eta]
  right_inv := by
    intro nf
    apply No16.NFData.ext
    · funext u2 u3 u4 u5
      simp [No13Migration.vec2]
    · funext u1 t u4 u5
      simp [No13Migration.vec2]
    · funext u1 u2 u3 r
      simp [No13Migration.vec2]

set_option maxHeartbeats 4000000 in
-- Expanding the `(2,2,2)` bridge into the imported `No16` normal form is expensive here.
lemma localPhaseBitABC_toAssignmentABC_eq_no16_phiQ {n : ℕ} [NeZero n]
    (nf : ABCNormalForm 2 2 2 n) (u : Site 2 2 2 n) :
    localPhaseBitABC (toAssignmentABC nf) u =
      No16.phiQ ((abc222NormalFormEquivNo16NFData n nf).toAssignment) (site222EquivQuint n u) := by
  let nf16 := abc222NormalFormEquivNo16NFData n nf
  rw [localPhaseBit_toAssignmentABC]
  rw [No16.phiQ_toAssignment nf16 (site222EquivQuint n u)]
  rcases u with ⟨x, y, z⟩
  simp [nf16, abc222NormalFormEquivNo16NFData, site222EquivQuint,
    linBC_abc, pairBC_abc, No16.linBC, No16.pairBC, No16.quadApply, No16.aFunEquivQuad,
    No13Migration.sumY_two,
    No13Migration.xCoord_two_eta, No13Migration.vec2_eta,
    add_assoc, add_left_comm, add_comm]

lemma phaseExponentABC_toAssignmentABC_eq_no16_phaseExponent {n : ℕ} [NeZero n]
    (nf : ABCNormalForm 2 2 2 n) :
    phaseExponentABC (toAssignmentABC nf) =
      No16.phaseExponent ((abc222NormalFormEquivNo16NFData n nf).toAssignment) := by
  let nf16 := abc222NormalFormEquivNo16NFData n nf
  unfold phaseExponentABC No16.phaseExponent
  calc
    ∑ u : Site 2 2 2 n, localPhaseBitABC (toAssignmentABC nf) u
      = ∑ u : Site 2 2 2 n, No16.phiQ nf16.toAssignment (site222EquivQuint n u) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          simpa [nf16] using localPhaseBitABC_toAssignmentABC_eq_no16_phiQ (n := n) nf u
    _ = ∑ q : No16.Quint n, No16.phiQ nf16.toAssignment q := by
          simpa [nf16] using
            (Equiv.sum_comp (site222EquivQuint n)
              (fun q : No16.Quint n => No16.phiQ nf16.toAssignment q))

lemma W_abc_raw_toAssignmentABC_eq_no16_phase {n : ℕ} [NeZero n]
    (nf : ABCNormalForm 2 2 2 n) :
    W_abc_raw (toAssignmentABC nf) =
      No16.bitSign (No16.phaseExponent ((abc222NormalFormEquivNo16NFData n nf).toAssignment)) := by
  unfold W_abc_raw
  rw [phaseExponentABC_toAssignmentABC_eq_no16_phaseExponent (n := n) nf]
  rfl

theorem DeltaABC_regression_222 {n : ℕ} [NeZero n] :
    DeltaABC 2 2 2 n = No16.Delta16 n := by
  rw [DeltaABC_eq_sum_normalForm (a := 2) (b := 2) (c := 2) (n := n) (by decide) (by decide)]
  unfold No16.Delta16
  rw [No16.Delta16Raw_eq_sum_normalForm]
  let e := abc222NormalFormEquivNo16NFData n
  calc
    ∑ nf : ABCNormalForm 2 2 2 n, W_abc_raw (toAssignmentABC nf)
      = ∑ nf : ABCNormalForm 2 2 2 n,
          No16.bitSign (No16.phaseExponent ((e nf).toAssignment)) := by
            refine Finset.sum_congr rfl ?_
            intro nf hnf
            simpa [e] using W_abc_raw_toAssignmentABC_eq_no16_phase (n := n) nf
    _ = ∑ nf : No16.NFData n, No16.bitSign (No16.phaseExponent nf.toAssignment) := by
          simpa using
            (Equiv.sum_comp e
              (fun nf : No16.NFData n => No16.bitSign (No16.phaseExponent nf.toAssignment)))

theorem DeltaABC_closed_regression_222_formula_of_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    DeltaABC 2 2 2 n = (2 : ℤ) ^ (3 * n ^ 4 + 5 * n ^ 2 + 1 - (3 * n ^ 3 + 3 * n)) := by
  rw [DeltaABC_regression_222, No16.Delta16_odd_closed_standard_of_odd hn]
  rfl

theorem DeltaABC_closed_regression_222_formula_of_even {n : ℕ} [NeZero n] (hn : Even n) :
    DeltaABC 2 2 2 n = (2 : ℤ) ^ (3 * n ^ 4 + 6 * n ^ 2 + 3 - (3 * n ^ 3 + 6 * n)) := by
  rw [DeltaABC_regression_222, No16.Delta16_even_closed_standard_of_even hn]
  rfl

theorem DeltaABC_closed_regression_222_formula {n : ℕ} [NeZero n] :
    DeltaABC 2 2 2 n =
      if Even n then
        (2 : ℤ) ^ (3 * n ^ 4 + 6 * n ^ 2 + 3 - (3 * n ^ 3 + 6 * n))
      else
        (2 : ℤ) ^ (3 * n ^ 4 + 5 * n ^ 2 + 1 - (3 * n ^ 3 + 3 * n)) := by
  by_cases hn : Even n
  · rw [if_pos hn]
    exact DeltaABC_closed_regression_222_formula_of_even (n := n) hn
  · rw [if_neg hn]
    exact DeltaABC_closed_regression_222_formula_of_odd (n := n) ((Nat.not_even_iff_odd).1 hn)

end Core3loop
