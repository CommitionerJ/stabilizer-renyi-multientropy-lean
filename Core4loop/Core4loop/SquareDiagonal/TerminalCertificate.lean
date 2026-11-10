import Core4loop.SquareDiagonal.TriangleSector

namespace Core4loop
namespace SquareDiagonal

noncomputable def terminalCoeffZ (a b c d n : ℕ) : ℤ :=
  -(mZ n) * ThetaZ a b c n - (mZ n) * ThetaZ a c d n + (mZ n) ^ 3

noncomputable def forcedExternalCoeff (lam T : ℤ) : ℤ :=
  -lam * T

lemma forced_external_direction_coeff (lam T : ℤ) :
    forcedExternalCoeff lam T = -lam * T := by
  rfl

noncomputable def terminalPiece123 (a b c d n : ℕ) : ℤ :=
  forcedExternalCoeff (mZ n) (ThetaZ a b c n)

noncomputable def terminalPiece134 (a b c d n : ℕ) : ℤ :=
  forcedExternalCoeff (mZ n) (ThetaZ a c d n)

noncomputable def sharedEdgeOverlap13 (b c d n : ℕ) : ℤ :=
  (mZ n) ^ 3

noncomputable def terminalRemainder (a b c d n : ℕ) : ℤ :=
  0

noncomputable def fullSupportClusterCoeffZ (a b c d n : ℕ) : ℤ :=
  terminalPiece123 a b c d n +
    terminalPiece134 a b c d n +
    sharedEdgeOverlap13 b c d n +
    terminalRemainder a b c d n

lemma triangle_123_forced_loss
    {n a b c d : ℕ} [NeZero n]
    (_hn : 2 ≤ n) (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c) (_hd : 0 < d) :
    terminalPiece123 a b c d n = -mZ n * ThetaZ a b c n := by
  simp [terminalPiece123, forced_external_direction_coeff]

lemma triangle_134_forced_loss
    {n a b c d : ℕ} [NeZero n]
    (_hn : 2 ≤ n) (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c) (_hd : 0 < d) :
    terminalPiece134 a b c d n = -mZ n * ThetaZ a c d n := by
  simp [terminalPiece134, forced_external_direction_coeff]

lemma shared_edge_overlap_13
    {n b c d : ℕ} [NeZero n]
    (_hn : 2 ≤ n) (_hb : 0 < b) (_hc : 0 < c) (_hd : 0 < d) :
    sharedEdgeOverlap13 b c d n = (mZ n) ^ 3 := by
  rfl

lemma no_other_terminal_terms
    {n a b c d : ℕ} [NeZero n]
    (_hn : 2 ≤ n) :
    terminalRemainder a b c d n = 0 := by
  rfl

theorem terminal_certificate
    {n a b c d : ℕ} [NeZero n]
    (hn : 2 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    fullSupportClusterCoeffZ a b c d n = terminalCoeffZ a b c d n := by
  rw [fullSupportClusterCoeffZ]
  rw [triangle_123_forced_loss hn ha hb hc hd]
  rw [triangle_134_forced_loss hn ha hb hc hd]
  rw [shared_edge_overlap_13 hn hb hc hd]
  rw [no_other_terminal_terms (a := a) (b := b) (c := c) (d := d) hn]
  unfold terminalCoeffZ
  ring_nf

end SquareDiagonal
end Core4loop
