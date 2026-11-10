import Core4loop.TriangleLeaf.TotalQCdCoeff

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private theorem eq_of_add_eq_zero_F {x y : F} (h : x + y = 0) : x = y := by
  calc
    x = x + 0 := by simp
    _ = x + (x + y) := by rw [h]
    _ = (x + x) + y := by ring
    _ = y := by rw [F_add_self]; simp

private theorem add_eq_zero_of_eq_F {x y : F} (h : x = y) : x + y = 0 := by
  rw [h, F_add_self]

theorem qLeafProfileKernelTotalCdCoeffRead_eq_zero_iff_forall_coeff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCdCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0
      ↔
      ∀ i : LeafCdFamilyIndex n b, ∀ p : PVec n a, ∀ s : NonzeroI n,
        qLeafProfileKernelTotalCdCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
            i p s.1
          =
        qLeafProfileKernelTotalCdCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
            i p 0 := by
  constructor
  · intro hread i p s
    have hpoint := congrFun hread (i, (p, s))
    have hsum :
        qLeafProfileKernelTotalCdCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
            i p s.1
          +
        qLeafProfileKernelTotalCdCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
            i p 0
          =
          0 := by
      simpa [qLeafProfileKernelTotalCdCoeffRead, leafDiffFamilyCoeffRead,
        leafDiffCoeffRead] using hpoint
    exact eq_of_add_eq_zero_F hsum
  · intro hcoeff
    funext ips
    rcases ips with ⟨i, ps⟩
    rcases ps with ⟨p, s⟩
    have hs := hcoeff i p s
    have hsum :
        qLeafProfileKernelTotalCdCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
            i p s.1
          +
        qLeafProfileKernelTotalCdCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
            i p 0
          =
          0 :=
      add_eq_zero_of_eq_F hs
    simpa [qLeafProfileKernelTotalCdCoeffRead, leafDiffFamilyCoeffRead,
      leafDiffCoeffRead] using hsum

end

end TriangleLeaf
end Core4loop
