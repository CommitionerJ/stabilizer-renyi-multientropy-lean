import Core4loop.TriangleLeaf.Transfer
import Core4loop.TriangleCore.AElimination

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

open TriangleCore

noncomputable def pvecPassiveEquiv (n a d : ℕ) (ha : 0 < a) :
    PVec n (a + d) ≃ PVec n a × WVec n d := by
  classical
  have hlen : a + d - 1 = (a - 1) + d := by omega
  exact
    ((Equiv.piCongrLeft (fun _ : Fin ((a - 1) + d) => I n) (finCongr hlen)).trans
      (Fin.appendEquiv (a - 1) d).symm)

noncomputable def triBFunLeafEquiv {n a c d : ℕ} (ha : 0 < a) :
    TriBFun n (a + d) c ≃ BFun4 n a c d where
  toFun B := fun p sy z w =>
    B ((pvecPassiveEquiv n a d ha).symm (p, w)) sy z
  invFun B := fun q sy z =>
    let x := pvecPassiveEquiv n a d ha q
    B x.1 sy z x.2
  left_inv B := by
    funext q sy z
    simp
  right_inv B := by
    funext p sy z w
    simp

noncomputable def triCFunLeafEquiv {n a b d : ℕ} (ha : 0 < a) :
    TriCFun n (a + d) b ≃ CFun4 n a b d where
  toFun C := fun p y sz w =>
    C ((pvecPassiveEquiv n a d ha).symm (p, w)) y sz
  invFun C := fun q y sz =>
    let x := pvecPassiveEquiv n a d ha q
    C x.1 y sz x.2
  left_inv C := by
    funext q y sz
    simp
  right_inv C := by
    funext p y sz w
    simp

theorem TriQraw_leaf_encoding {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (B : BFun4 n a c d) (C : CFun4 n a b d) :
    TriQraw ((triBFunLeafEquiv (n := n) (a := a) (c := c) (d := d) ha).symm B)
        ((triCFunLeafEquiv (n := n) (a := a) (b := b) (d := d) ha).symm C)
      =
      Q1 B C := by
  classical
  let e := pvecPassiveEquiv n a d ha
  unfold TriQraw Q1
  calc
    (∑ q : TriPVec n (a + d), ∑ y : TriYVec n b, ∑ z : TriZVec n c,
      (
      ((triBFunLeafEquiv (n := n) (a := a) (c := c) (d := d) ha).symm B)
          q (vecSum y) z *
        ((triCFunLeafEquiv (n := n) (a := a) (b := b) (d := d) ha).symm C)
          q y (vecSum z) +
      ((triBFunLeafEquiv (n := n) (a := a) (c := c) (d := d) ha).symm B)
          q (vecSum y + 1) z *
        ((triCFunLeafEquiv (n := n) (a := a) (b := b) (d := d) ha).symm C)
          q y (vecSum z + 1)))
        =
        ∑ x : PVec n a × WVec n d, ∑ y : YVec n b, ∑ z : ZVec n c,
          (
          B x.1 (vecSum y) z x.2 * C x.1 y (vecSum z) x.2
            + B x.1 (vecSum y + 1) z x.2 * C x.1 y (vecSum z + 1) x.2) := by
          simpa [e, triBFunLeafEquiv, triCFunLeafEquiv] using
            (Equiv.sum_comp e
              (fun x : PVec n a × WVec n d =>
                ∑ y : YVec n b, ∑ z : ZVec n c,
                  (
                  B x.1 (vecSum y) z x.2 * C x.1 y (vecSum z) x.2
                    + B x.1 (vecSum y + 1) z x.2 * C x.1 y (vecSum z + 1) x.2)))
    _ =
        ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
          (
          B p (vecSum y) z w * C p y (vecSum z) w
            + B p (vecSum y + 1) z w * C p y (vecSum z + 1) w) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [Finset.sum_comm]

end TriangleLeaf
end Core4loop
