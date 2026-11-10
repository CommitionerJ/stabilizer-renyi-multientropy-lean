import Core4loop.ZeroSumSpaces.ProfileMRange
import Core4loop.ZeroSumSpaces.Matrix

open scoped BigOperators

namespace Core4loop

noncomputable def shearDiagVal {n : ℕ} [NeZero n]
    (M : MatrixProfile n) : MatrixProfile n :=
  fun sz t => M (t - sz) sz

noncomputable def unshearDiagVal {n : ℕ} [NeZero n]
    (N : MatrixProfile n) : MatrixProfile n :=
  fun sy sz => N sz (sy + sz)

lemma shearDiagVal_unshearDiagVal {n : ℕ} [NeZero n]
    (N : MatrixProfile n) :
    shearDiagVal (n := n) (unshearDiagVal (n := n) N) = N := by
  funext sz t
  unfold shearDiagVal unshearDiagVal
  have h : t - sz + sz = t := by abel
  rw [h]

lemma unshearDiagVal_shearDiagVal {n : ℕ} [NeZero n]
    (M : MatrixProfile n) :
    unshearDiagVal (n := n) (shearDiagVal (n := n) M) = M := by
  funext sy sz
  unfold shearDiagVal unshearDiagVal
  change M (sy + sz - sz) sz = M sy sz
  have h : sy + sz - sz = sy := by abel
  rw [h]

lemma shearDiagVal_mem_MatrixZeroSum {n : ℕ} [NeZero n]
    (M : MatrixProfile n)
    (hcol : ∀ sz : I n, (∑ sy : I n, M sy sz) = 0)
    (hdiag : ∀ t : I n, (∑ sz : I n, M (t - sz) sz) = 0) :
    shearDiagVal (n := n) M ∈ MatrixZeroSum n := by
  constructor
  · apply LinearMap.mem_ker.mpr
    funext sz
    unfold rowSum2Map shearDiagVal
    change (∑ t : I n, M (t - sz) sz) = 0
    have hshift : (∑ t : I n, M (t - sz) sz) = ∑ sy : I n, M sy sz := by
      simpa [sub_eq_add_neg] using
        ((Equiv.addRight (-sz)).sum_comp
          (Finset.univ : Finset (I n)) (fun sy : I n => M sy sz))
    rw [hshift, hcol sz]
  · apply LinearMap.mem_ker.mpr
    funext t
    unfold colSum2Map shearDiagVal
    exact hdiag t

end Core4loop
