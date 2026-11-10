import Core4loop.TriangleLeaf.ProfileKernelIndexDiffQ
import Core4loop.TriangleLeaf.ScalarProfileKernelBridge

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private lemma sum_ωyzp_comm
    {Ω Y Z P : Type*} [Fintype Ω] [Fintype Y] [Fintype Z] [Fintype P]
    (f : Ω → Y → Z → P → F) :
    (∑ ω : Ω, ∑ y : Y, ∑ z : Z, ∑ p : P, f ω y z p)
      =
      ∑ y : Y, ∑ z : Z, ∑ p : P, ∑ ω : Ω, f ω y z p := by
  calc
    (∑ ω : Ω, ∑ y : Y, ∑ z : Z, ∑ p : P, f ω y z p)
        = ∑ y : Y, ∑ ω : Ω, ∑ z : Z, ∑ p : P, f ω y z p := by
            rw [Finset.sum_comm]
    _ = ∑ y : Y, ∑ z : Z, ∑ ω : Ω, ∑ p : P, f ω y z p := by
            refine Finset.sum_congr rfl ?_
            intro y _
            rw [Finset.sum_comm]
    _ = ∑ y : Y, ∑ z : Z, ∑ p : P, ∑ ω : Ω, f ω y z p := by
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro z _
            rw [Finset.sum_comm]

def qLeafProfileKernelVisibleIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (kBv :
      PassiveVisibleIndex n d hd → I n → ZVec n c → LeafScalarProfileKernel n a)
    (kCv :
      PassiveVisibleIndex n d hd → YVec n b → I n → LeafScalarProfileKernel n a) :
    F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
      (leafScalarBProfileKernelCoordEquivCore3BWodd
        (n := n) (a := a) (c := c) (kBv ω)).1
      (leafScalarCProfileKernelCoordEquivCore3CWodd
        (n := n) (a := a) (b := b) (kCv ω)).1

theorem qLeafProfileKernelVisibleIndexDiff_eq_visibleVisibleTerms
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (kBv :
      PassiveVisibleIndex n d hd → I n → ZVec n c → LeafScalarProfileKernel n a)
    (kCv :
      PassiveVisibleIndex n d hd → YVec n b → I n → LeafScalarProfileKernel n a) :
    qLeafProfileKernelVisibleIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd kBv kCv
      =
      (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
        ∑ ω : PassiveVisibleIndex n d hd,
          (kBv ω (vecSum y) z).1 p * (kCv ω y (vecSum z)).1 p)
      +
      (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
        ∑ ω : PassiveVisibleIndex n d hd,
          (kBv ω (vecSum y + 1) z).1 p *
            (kCv ω y (vecSum z + 1)).1 p) := by
  unfold qLeafProfileKernelVisibleIndexDiff
  simp_rw [Core3loop.qProfileABC, Core3loop.qLeftProfileABC,
    Core3loop.qRightProfileABC, Core3loop.dotProfile,
    leafScalarBProfileKernelCoordEquivCore3BWodd_apply,
    leafScalarCProfileKernelCoordEquivCore3CWodd_apply]
  rw [Finset.sum_add_distrib]
  conv_lhs =>
    rw [sum_ωyzp_comm
      (Ω := PassiveVisibleIndex n d hd)
      (Y := YVec n b) (Z := ZVec n c) (P := PVec n a)
      (f := fun ω y z p =>
        (kBv ω (Core3loop.sumY y) z).1 p *
          (kCv ω y (Core3loop.sumZ z)).1 p)]
    rw [sum_ωyzp_comm
      (Ω := PassiveVisibleIndex n d hd)
      (Y := YVec n b) (Z := ZVec n c) (P := PVec n a)
      (f := fun ω y z p =>
        (kBv ω (Core3loop.sumY y + 1) z).1 p *
          (kCv ω y (Core3loop.sumZ z + 1)).1 p)]
  simp [vecSum, Core3loop.sumY, Core3loop.sumZ, No13Migration.sumY,
    No13Migration.sumZ, No13Migration.sumCoord]

end

end TriangleLeaf
end Core4loop
