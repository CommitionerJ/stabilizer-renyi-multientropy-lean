import Core3loop.Basic

namespace Core3loop

abbrev AssignmentABC (a b c n : ℕ) := No13Migration.RawAssignmentABC a b c n

abbrev ValidPrimitiveABC {a b c n : ℕ} [NeZero n] (S : AssignmentABC a b c n) : Prop :=
  No13Migration.RawValidPrimitiveABC S

abbrev ValidAssignmentsABC (a b c n : ℕ) [NeZero n] :=
  No13Migration.ABCValidPrimitiveAssignmentsHonest a b c n

abbrev ABCNormalForm (a b c n : ℕ) [NeZero n] :=
  No13Migration.ABCAssignment a b c n

noncomputable abbrev toAssignmentABC {a b c n : ℕ} [NeZero n] :
    ABCNormalForm a b c n → AssignmentABC a b c n :=
  No13Migration.toRawAssignmentABC

noncomputable abbrev toABCNormalForm {a b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    ∀ (S : AssignmentABC a b c n), ValidPrimitiveABC S → ABCNormalForm a b c n :=
  fun S hS => No13Migration.rawToABCAssignment (a := a) (b := b) (c := c) (n := n) hb hc S
    (No13Migration.rawValidPrimitiveABC_to_rawValidABC (b := b) (c := c) (n := n) hb hc hS)

noncomputable def validAssignmentsEquivNormalForm {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    ValidAssignmentsABC a b c n ≃ ABCNormalForm a b c n :=
  No13Migration.abcValidPrimitiveAssignmentsHonestEquivABCAssignment
    (a := a) (b := b) (c := c) (n := n) hb hc

theorem card_validAssignments_abc {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ValidAssignmentsABC a b c n) =
      2 ^ (n ^ (b + c) + n ^ (a + c) + n ^ (a + b)) := by
  simpa [ValidAssignmentsABC] using
    No13Migration.card_validAssignments_abc_primitive_honest
      (a := a) (b := b) (c := c) (n := n) ha hb hc

end Core3loop
