import Core4loop.TriangleLeaf.LeafProfileKernelDecomposition

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafScalarProfile (n a : ℕ) [NeZero n] :=
  PVec n a → F

noncomputable def leafScalarProfileSum {n a : ℕ} [NeZero n] :
    LeafScalarProfile n a →ₗ[F] F where
  toFun f := ∑ p : PVec n a, f p
  map_add' f g := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]

abbrev LeafScalarProfileKernel (n a : ℕ) [NeZero n] :=
  LinearMap.ker (leafScalarProfileSum (n := n) (a := a))

abbrev LeafVisibleProfileCoordIndex (n a d : ℕ) [NeZero n] (hd : 0 < d) :=
  PassiveVisibleIndex n d hd → LeafScalarProfile n a

noncomputable def leafVisibleProfileCoordEquivIndex
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafVisibleProfileCoord n a d hd ≃ₗ[F]
      LeafVisibleProfileCoordIndex n a d hd where
  toFun V := fun ω p =>
    passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (V p) ω
  invFun G := fun p =>
    (passiveVisibleSpaceEquivIndex (n := n) (d := d) hd).symm
      (fun ω => G ω p)
  left_inv V := by
    funext p
    exact
      (passiveVisibleSpaceEquivIndex
        (n := n) (d := d) hd).left_inv (V p)
  right_inv G := by
    funext ω p
    exact congrFun
      ((passiveVisibleSpaceEquivIndex
        (n := n) (d := d) hd).right_inv (fun ω => G ω p)) ω
  map_add' V W := by
    funext ω p
    rfl
  map_smul' r V := by
    funext ω p
    rfl

theorem leafVisibleProfileCoordEquivIndex_sum_apply
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafVisibleProfileCoord n a d hd) (ω : PassiveVisibleIndex n d hd) :
    leafScalarProfileSum (n := n) (a := a)
        ((leafVisibleProfileCoordEquivIndex
          (n := n) (a := a) (d := d) hd V) ω)
      =
      passiveVisibleSpaceEquivIndex (n := n) (d := d) hd
        (leafVisibleProfileSum (n := n) (a := a) (d := d) hd V) ω := by
  change
    (∑ p : PVec n a,
      passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (V p) ω)
      =
      passiveVisibleSpaceEquivIndex (n := n) (d := d) hd
        (∑ p : PVec n a, V p) ω
  rw [map_sum]
  simp

theorem leafVisibleProfileCoord_mem_ker_iff_index
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafVisibleProfileCoord n a d hd) :
    V ∈ LeafVisibleProfileKernel n a d hd
      ↔
      ∀ ω : PassiveVisibleIndex n d hd,
        (leafVisibleProfileCoordEquivIndex
          (n := n) (a := a) (d := d) hd V) ω
          ∈ LeafScalarProfileKernel n a := by
  constructor
  · intro hV ω
    rw [LinearMap.mem_ker]
    rw [leafVisibleProfileCoordEquivIndex_sum_apply
      (n := n) (a := a) (d := d) hd V ω]
    rw [LinearMap.mem_ker] at hV
    simp [hV]
  · intro hV
    rw [LinearMap.mem_ker]
    let e := passiveVisibleSpaceEquivIndex (n := n) (d := d) hd
    apply e.injective
    funext ω
    have hω := LinearMap.mem_ker.mp (hV ω)
    rw [leafVisibleProfileCoordEquivIndex_sum_apply
      (n := n) (a := a) (d := d) hd V ω] at hω
    simpa [e] using hω

noncomputable def leafVisibleProfileKernelEquivIndex
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafVisibleProfileKernel n a d hd ≃ₗ[F]
      (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a) where
  toFun V := fun ω =>
    ⟨(leafVisibleProfileCoordEquivIndex
        (n := n) (a := a) (d := d) hd V.1) ω,
      (leafVisibleProfileCoord_mem_ker_iff_index
        (n := n) (a := a) (d := d) hd V.1).1 V.2 ω⟩
  invFun G :=
    let V :=
      (leafVisibleProfileCoordEquivIndex
        (n := n) (a := a) (d := d) hd).symm
        (fun ω => (G ω).1)
    ⟨V,
      by
        apply
          (leafVisibleProfileCoord_mem_ker_iff_index
            (n := n) (a := a) (d := d) hd V).2
        intro ω
        have hω :
            (leafVisibleProfileCoordEquivIndex
              (n := n) (a := a) (d := d) hd V) ω =
              (G ω).1 :=
          congrFun
            ((leafVisibleProfileCoordEquivIndex
              (n := n) (a := a) (d := d) hd).right_inv
              (fun ω => (G ω).1)) ω
        rw [hω]
        exact (G ω).2⟩
  left_inv V := by
    apply Subtype.ext
    exact
      (leafVisibleProfileCoordEquivIndex
        (n := n) (a := a) (d := d) hd).left_inv V.1
  right_inv G := by
    funext ω
    apply Subtype.ext
    exact congrFun
      ((leafVisibleProfileCoordEquivIndex
        (n := n) (a := a) (d := d) hd).right_inv
        (fun ω => (G ω).1)) ω
  map_add' V W := by
    funext ω
    apply Subtype.ext
    change
      (leafVisibleProfileCoordEquivIndex
        (n := n) (a := a) (d := d) hd (V.1 + W.1)) ω =
        (leafVisibleProfileCoordEquivIndex
          (n := n) (a := a) (d := d) hd V.1) ω
          + (leafVisibleProfileCoordEquivIndex
            (n := n) (a := a) (d := d) hd W.1) ω
    exact congrFun
      (map_add (leafVisibleProfileCoordEquivIndex
        (n := n) (a := a) (d := d) hd) V.1 W.1) ω
  map_smul' r V := by
    funext ω
    apply Subtype.ext
    change
      (leafVisibleProfileCoordEquivIndex
        (n := n) (a := a) (d := d) hd (r • V.1)) ω =
        r • (leafVisibleProfileCoordEquivIndex
          (n := n) (a := a) (d := d) hd V.1) ω
    exact congrFun
      (map_smul (leafVisibleProfileCoordEquivIndex
        (n := n) (a := a) (d := d) hd) r V.1) ω

theorem leafVisibleProfileKernelEquivIndex_apply
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafVisibleProfileKernel n a d hd) (ω : PassiveVisibleIndex n d hd) :
    ((leafVisibleProfileKernelEquivIndex
      (n := n) (a := a) (d := d) hd V) ω : LeafScalarProfile n a)
      =
      (leafVisibleProfileCoordEquivIndex
        (n := n) (a := a) (d := d) hd V.1) ω := rfl

end

end TriangleLeaf
end Core4loop
