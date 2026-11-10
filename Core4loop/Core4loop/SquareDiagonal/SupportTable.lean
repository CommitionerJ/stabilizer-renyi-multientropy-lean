import Core4loop.Exponents

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

inductive V4 where
  | v1 | v2 | v3 | v4
  deriving DecidableEq, Fintype, Repr

open V4

def vsize (a b c d : ℕ) : V4 → ℕ
  | v1 => a
  | v2 => b
  | v3 => c
  | v4 => d

noncomputable def compSize (a b c d : ℕ) (U : Finset V4) : ℕ :=
  (if v1 ∈ U then 0 else a) + (if v2 ∈ U then 0 else b) +
    (if v3 ∈ U then 0 else c) + (if v4 ∈ U then 0 else d)

noncomputable def NsupportZ (a b c d n : ℕ) (U : Finset V4) : ℤ :=
  nPowZ n (compSize a b c d U)

def Edge : V4 → V4 → Prop
  | v1, v2 => True
  | v2, v1 => True
  | v2, v3 => True
  | v3, v2 => True
  | v3, v4 => True
  | v4, v3 => True
  | v1, v4 => True
  | v4, v1 => True
  | v1, v3 => True
  | v3, v1 => True
  | _, _ => False

lemma not_edge_24 : ¬ Edge v2 v4 := by
  intro h
  cases h

def allSupports : Finset (Finset V4) :=
  ({{}, {v1}, {v2}, {v3}, {v4},
    {v1, v2}, {v1, v3}, {v1, v4}, {v2, v3}, {v2, v4}, {v3, v4},
    {v1, v2, v3}, {v1, v2, v4}, {v1, v3, v4}, {v2, v3, v4},
    {v1, v2, v3, v4}} : Finset (Finset V4))

lemma allSupports_eq_univ :
    allSupports = (Finset.univ : Finset (Finset V4)) := by
  classical
  ext U
  constructor
  · intro _
    exact Finset.mem_univ U
  · intro _
    fin_cases U <;> decide

noncomputable def coeffZ (a b c d n : ℕ) (U : Finset V4) : ℤ :=
  let lam := mZ n
  if U = ∅ then 0
  else if U.card = 1 then 1
  else if U.card = 2 then
    if v2 ∈ U ∧ v4 ∈ U then 0 else -lam
  else if U.card = 3 then
    if v4 ∉ U then ThetaZ a b c n
    else if v2 ∉ U then ThetaZ a c d n
    else lam ^ 2
  else if U.card = 4 then
    -lam * ThetaZ a b c n - lam * ThetaZ a c d n + lam ^ 3
  else 0

noncomputable def supportSumZ (a b c d n : ℕ) : ℤ :=
  ∑ U : Finset V4, coeffZ a b c d n U * NsupportZ a b c d n U

theorem supportSumZ_eq_closed (a b c d n : ℕ) :
    supportSumZ a b c d n =
      Sigma1Z a b c d n
      - mZ n * Sigma2_3Z a b c d n
      + (mZ n) ^ 2 * (nPowZ n a + nPowZ n c)
      + SectorExpZ a b c d n
      + SectorExpZ a c d b n
      + OverlapG3Z n := by
  classical
  rw [supportSumZ]
  rw [← allSupports_eq_univ]
  unfold allSupports
  repeat (rw [Finset.sum_insert] <;> try decide)
  rw [Finset.sum_singleton]
  simp [coeffZ, NsupportZ, compSize, Sigma1Z, Sigma2_3Z, nPowZ,
    SectorExpZ, OverlapG3Z]
  ring_nf

theorem supportSumZ_eq_X3Z (a b c d n : ℕ) :
    supportSumZ a b c d n = X3Z a b c d n := by
  rw [supportSumZ_eq_closed]
  simpa using (X3Z_sector_formula a b c d n).symm

end SquareDiagonal
end Core4loop
