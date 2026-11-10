import Core4loop.TriangleLeaf.LeafProfileKernelFullCoordinates

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafBProfileKernelIndexDiffCoord
    (n a c d : ℕ) [NeZero n] (hd : 0 < d) :=
  (PassiveVisibleIndex n d hd → I n → ZVec n c → LeafScalarProfileKernel n a)
    × (I n → ZVec n c → LeafDiffProfileCoord n a)

abbrev LeafCProfileKernelIndexDiffCoord
    (n a b d : ℕ) [NeZero n] (hd : 0 < d) :=
  (PassiveVisibleIndex n d hd → YVec n b → I n → LeafScalarProfileKernel n a)
    × (YVec n b → I n → LeafDiffProfileCoord n a)

noncomputable def leafBProfileKernelCoordEquivIndexDiff
    {n a c d : ℕ} [NeZero n] (hd : 0 < d) :
    (I n → ZVec n c → LeafProfileKernel n a d)
      ≃ₗ[F]
    LeafBProfileKernelIndexDiffCoord n a c d hd where
  toFun k :=
    (fun ω sy z =>
      (leafProfileKernelEquivIndexDiff
        (n := n) (a := a) (d := d) hd (k sy z)).1 ω,
     fun sy z =>
      (leafProfileKernelEquivIndexDiff
        (n := n) (a := a) (d := d) hd (k sy z)).2)
  invFun X := fun sy z =>
    (leafProfileKernelEquivIndexDiff
      (n := n) (a := a) (d := d) hd).symm
      ((fun ω => X.1 ω sy z), X.2 sy z)
  left_inv k := by
    funext sy z
    exact
      (leafProfileKernelEquivIndexDiff
        (n := n) (a := a) (d := d) hd).left_inv (k sy z)
  right_inv X := by
    apply Prod.ext
    · funext ω sy z
      exact congrFun
        (congrArg Prod.fst
          ((leafProfileKernelEquivIndexDiff
            (n := n) (a := a) (d := d) hd).right_inv
            ((fun ω => X.1 ω sy z), X.2 sy z))) ω
    · funext sy z
      exact congrArg Prod.snd
        ((leafProfileKernelEquivIndexDiff
          (n := n) (a := a) (d := d) hd).right_inv
          ((fun ω => X.1 ω sy z), X.2 sy z))
  map_add' k l := by
    apply Prod.ext
    · funext ω sy z
      exact congrFun
        (congrArg Prod.fst
          (map_add
            (leafProfileKernelEquivIndexDiff
              (n := n) (a := a) (d := d) hd)
            (k sy z) (l sy z))) ω
    · funext sy z
      exact congrArg Prod.snd
        (map_add
          (leafProfileKernelEquivIndexDiff
            (n := n) (a := a) (d := d) hd)
          (k sy z) (l sy z))
  map_smul' r k := by
    apply Prod.ext
    · funext ω sy z
      exact congrFun
        (congrArg Prod.fst
          (map_smul
            (leafProfileKernelEquivIndexDiff
              (n := n) (a := a) (d := d) hd)
            r (k sy z))) ω
    · funext sy z
      exact congrArg Prod.snd
        (map_smul
          (leafProfileKernelEquivIndexDiff
            (n := n) (a := a) (d := d) hd)
          r (k sy z))

noncomputable def leafCProfileKernelCoordEquivIndexDiff
    {n a b d : ℕ} [NeZero n] (hd : 0 < d) :
    (YVec n b → I n → LeafProfileKernel n a d)
      ≃ₗ[F]
    LeafCProfileKernelIndexDiffCoord n a b d hd where
  toFun k :=
    (fun ω y sz =>
      (leafProfileKernelEquivIndexDiff
        (n := n) (a := a) (d := d) hd (k y sz)).1 ω,
     fun y sz =>
      (leafProfileKernelEquivIndexDiff
        (n := n) (a := a) (d := d) hd (k y sz)).2)
  invFun X := fun y sz =>
    (leafProfileKernelEquivIndexDiff
      (n := n) (a := a) (d := d) hd).symm
      ((fun ω => X.1 ω y sz), X.2 y sz)
  left_inv k := by
    funext y sz
    exact
      (leafProfileKernelEquivIndexDiff
        (n := n) (a := a) (d := d) hd).left_inv (k y sz)
  right_inv X := by
    apply Prod.ext
    · funext ω y sz
      exact congrFun
        (congrArg Prod.fst
          ((leafProfileKernelEquivIndexDiff
            (n := n) (a := a) (d := d) hd).right_inv
            ((fun ω => X.1 ω y sz), X.2 y sz))) ω
    · funext y sz
      exact congrArg Prod.snd
        ((leafProfileKernelEquivIndexDiff
          (n := n) (a := a) (d := d) hd).right_inv
          ((fun ω => X.1 ω y sz), X.2 y sz))
  map_add' k l := by
    apply Prod.ext
    · funext ω y sz
      exact congrFun
        (congrArg Prod.fst
          (map_add
            (leafProfileKernelEquivIndexDiff
              (n := n) (a := a) (d := d) hd)
            (k y sz) (l y sz))) ω
    · funext y sz
      exact congrArg Prod.snd
        (map_add
          (leafProfileKernelEquivIndexDiff
            (n := n) (a := a) (d := d) hd)
          (k y sz) (l y sz))
  map_smul' r k := by
    apply Prod.ext
    · funext ω y sz
      exact congrFun
        (congrArg Prod.fst
          (map_smul
            (leafProfileKernelEquivIndexDiff
              (n := n) (a := a) (d := d) hd)
            r (k y sz))) ω
    · funext y sz
      exact congrArg Prod.snd
        (map_smul
          (leafProfileKernelEquivIndexDiff
            (n := n) (a := a) (d := d) hd)
          r (k y sz))

theorem leafBProfileKernelCoordEquivIndexDiff_symm_apply
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (X : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (sy : I n) (z : ZVec n c) :
    ((leafBProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd).symm X) sy z =
      (leafProfileKernelEquivIndexDiff
        (n := n) (a := a) (d := d) hd).symm
        ((fun ω => X.1 ω sy z), X.2 sy z) := rfl

theorem leafCProfileKernelCoordEquivIndexDiff_symm_apply
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (X : LeafCProfileKernelIndexDiffCoord n a b d hd)
    (y : YVec n b) (sz : I n) :
    ((leafCProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (b := b) (d := d) hd).symm X) y sz =
      (leafProfileKernelEquivIndexDiff
        (n := n) (a := a) (d := d) hd).symm
        ((fun ω => X.1 ω y sz), X.2 y sz) := rfl

end

end TriangleLeaf
end Core4loop
