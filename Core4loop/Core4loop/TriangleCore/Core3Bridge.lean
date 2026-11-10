import Core4loop.TriangleCore.AElimination
import Core3loop.Main

open scoped BigOperators

namespace Core4loop
namespace TriangleCore

noncomputable def triAFunToCore3 {n s t : ℕ} [NeZero n] :
    TriAFun n s t ≃ Core3loop.AFieldABC s t n where
  toFun A := fun yz => A yz.1 yz.2
  invFun A := fun y z => A (y, z)
  left_inv A := by
    funext y z
    rfl
  right_inv A := by
    funext yz
    rcases yz with ⟨y, z⟩
    rfl

noncomputable def triBFunToCore3 {n r t : ℕ} [NeZero n] :
    TriBFun n r t ≃ Core3loop.BFieldABC r t n where
  toFun B := fun u => B u.1 u.2.1 u.2.2
  invFun B := fun p sy z => B (p, sy, z)
  left_inv B := by
    funext p sy z
    rfl
  right_inv B := by
    funext u
    rcases u with ⟨p, sy, z⟩
    rfl

noncomputable def triCFunToCore3 {n r s : ℕ} [NeZero n] :
    TriCFun n r s ≃ Core3loop.CFieldABC r s n where
  toFun C := fun u => C u.1 u.2.1 u.2.2
  invFun C := fun p y sz => C (p, y, sz)
  left_inv C := by
    funext p y sz
    rfl
  right_inv C := by
    funext u
    rcases u with ⟨p, y, sz⟩
    rfl

noncomputable def triNFEquivCore3ABC {n r s t : ℕ} [NeZero n] :
    TriNF n r s t ≃ Core3loop.ABCNormalForm r s t n where
  toFun nf :=
    (triAFunToCore3 (n := n) (s := s) (t := t) nf.A,
      triBFunToCore3 (n := n) (r := r) (t := t) nf.B,
      triCFunToCore3 (n := n) (r := r) (s := s) nf.C)
  invFun nf :=
    { A := (triAFunToCore3 (n := n) (s := s) (t := t)).symm nf.1
      B := (triBFunToCore3 (n := n) (r := r) (t := t)).symm nf.2.1
      C := (triCFunToCore3 (n := n) (r := r) (s := s)).symm nf.2.2 }
  left_inv nf := by
    cases nf
    rfl
  right_inv nf := by
    rcases nf with ⟨A, B, C⟩
    rfl

lemma core3_linBC_eq_triLinearTerms
    {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t)
    (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) :
    Core3loop.linBC_abc
      ((triNFEquivCore3ABC (n := n) (r := r) (s := s) (t := t) nf).2.1)
      ((triNFEquivCore3ABC (n := n) (r := r) (s := s) (t := t) nf).2.2)
      (p, y, z) =
    triLinearTerms nf p y z := by
  cases nf
  simp [Core3loop.linBC_abc, triNFEquivCore3ABC, triBFunToCore3, triCFunToCore3,
    triLinearTerms, triBeta, triGamma, triDelta, triEta, Core3loop.sumY, Core3loop.sumZ,
    No13Migration.sumY, No13Migration.sumZ, No13Migration.sumCoord, vecSum]
  ac_rfl

lemma core3_pairBC_eq_triPair
    {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t)
    (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) :
    Core3loop.pairBC_abc
      ((triNFEquivCore3ABC (n := n) (r := r) (s := s) (t := t) nf).2.1)
      ((triNFEquivCore3ABC (n := n) (r := r) (s := s) (t := t) nf).2.2)
      (p, y, z) =
    triBeta nf p y z * triDelta nf p y z +
      triGamma nf p y z * triEta nf p y z := by
  cases nf
  simp [Core3loop.pairBC_abc, triNFEquivCore3ABC, triBFunToCore3, triCFunToCore3,
    triBeta, triGamma, triDelta, triEta, Core3loop.sumY, Core3loop.sumZ,
    No13Migration.sumY, No13Migration.sumZ, No13Migration.sumCoord, vecSum]

lemma core3_A_apply_eq_triAlpha
    {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t)
    (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) :
    (triNFEquivCore3ABC (n := n) (r := r) (s := s) (t := t) nf).1 (y, z) =
      triAlpha nf p y z := by
  cases nf
  rfl

lemma core3_localPhase_toAssignment_eq_triNo16Phase
    {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t)
    (p : TriPVec n r) (y : TriYVec n s) (z : TriZVec n t) :
    Core3loop.localPhaseBitABC
      (Core3loop.toAssignmentABC
        ((triNFEquivCore3ABC (n := n) (r := r) (s := s) (t := t)) nf))
      (p, y, z) =
    triNo16Phase nf p y z := by
  rw [Core3loop.localPhaseBit_toAssignmentABC]
  rw [core3_linBC_eq_triLinearTerms (n := n) (r := r) (s := s) (t := t) nf p y z]
  rw [core3_pairBC_eq_triPair (n := n) (r := r) (s := s) (t := t) nf p y z]
  rw [core3_A_apply_eq_triAlpha (n := n) (r := r) (s := s) (t := t) nf p y z]
  unfold triNo16Phase triGraphPhase triLinearTerms
  ring_nf

lemma core3_phaseExponent_eq_triNo16Exponent
    {n r s t : ℕ} [NeZero n]
    (nf : TriNF n r s t) :
    Core3loop.phaseExponentABC
      (Core3loop.toAssignmentABC
        ((triNFEquivCore3ABC (n := n) (r := r) (s := s) (t := t)) nf))
    = triNo16Exponent nf := by
  unfold Core3loop.phaseExponentABC triNo16Exponent
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro z _
  exact core3_localPhase_toAssignment_eq_triNo16Phase
    (n := n) (r := r) (s := s) (t := t) nf p y z

lemma core3_phaseExponent_eq_triGraphExponent
    {n r s t : ℕ} [NeZero n]
    (hs : 0 < s) (ht : 0 < t)
    (nf : TriNF n r s t) :
    Core3loop.phaseExponentABC
      (Core3loop.toAssignmentABC
        ((triNFEquivCore3ABC (n := n) (r := r) (s := s) (t := t)) nf))
    = triGraphExponent nf := by
  rw [core3_phaseExponent_eq_triNo16Exponent (n := n) (r := r) (s := s) (t := t)]
  exact (triGraphExponent_eq_triNo16Exponent
    (n := n) (r := r) (s := s) (t := t) hs ht nf).symm

theorem DeltaTriangleCore_eq_Core3DeltaABC
    {r s t n : ℕ} [NeZero n]
    (_hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    DeltaTriangleCore r s t n = Core3loop.DeltaABC r s t n := by
  rw [Core3loop.DeltaABC_eq_sum_normalForm (a := r) (b := s) (c := t) (n := n) hs ht]
  unfold DeltaTriangleCore Core3loop.W_abc_raw
  symm
  calc
    (∑ nf : Core3loop.ABCNormalForm r s t n,
        bitSign (Core3loop.phaseExponentABC (Core3loop.toAssignmentABC nf)))
        =
      ∑ nf : TriNF n r s t,
        bitSign
          (Core3loop.phaseExponentABC
            (Core3loop.toAssignmentABC
              ((triNFEquivCore3ABC (n := n) (r := r) (s := s) (t := t)) nf))) := by
        exact
          ((triNFEquivCore3ABC (n := n) (r := r) (s := s) (t := t)).sum_comp
            (fun nf : Core3loop.ABCNormalForm r s t n =>
              bitSign (Core3loop.phaseExponentABC (Core3loop.toAssignmentABC nf)))).symm
    _ = ∑ nf : TriNF n r s t, bitSign (triGraphExponent nf) := by
        refine Finset.sum_congr rfl ?_
        intro nf _
        rw [core3_phaseExponent_eq_triGraphExponent
          (n := n) (r := r) (s := s) (t := t) hs ht nf]

end TriangleCore
end Core4loop
