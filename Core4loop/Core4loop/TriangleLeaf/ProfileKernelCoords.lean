import Core4loop.TriangleLeaf.FiberCard
import Core4loop.TriangleLeaf.PassiveProfileExp

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafProfileKernel (n a d : ℕ) [NeZero n] :=
  LinearMap.ker (leafSigmaQuot (n := n) (a := a) (d := d))

noncomputable instance instFintypeLeafProfileKernel {n a d : ℕ} [NeZero n] :
    Fintype (LeafProfileKernel n a d) := by
  classical
  letI : Finite (LeafProfileKernel n a d) :=
    Finite.of_injective
      (fun x : LeafProfileKernel n a d => (x.1 : LeafProfile n a d))
      (fun _ _ h => Subtype.ext h)
  exact Fintype.ofFinite (LeafProfileKernel n a d)

noncomputable def leafBVisKernelEquivProfileKernelCoord
    {n a c d : ℕ} [NeZero n] :
    LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d))
      ≃
    (I n → ZVec n c → LeafProfileKernel n a d) where
  toFun K := fun sy z =>
    ⟨leafBProfile K.1 sy z, by
      apply LinearMap.mem_ker.mpr
      have hK := LinearMap.mem_ker.mp K.2
      have h := congrFun (congrFun hK sy) z
      exact h⟩
  invFun f :=
    ⟨fun p sy z w => (f sy z).1 p w, by
      apply LinearMap.mem_ker.mpr
      funext sy z
      have hf := LinearMap.mem_ker.mp (f sy z).2
      exact hf⟩
  left_inv K := by
    apply Subtype.ext
    funext p sy z w
    rfl
  right_inv f := by
    funext sy z
    apply Subtype.ext
    funext p w
    rfl

noncomputable def leafCVisKernelEquivProfileKernelCoord
    {n a b d : ℕ} [NeZero n] :
    LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d))
      ≃
    (YVec n b → I n → LeafProfileKernel n a d) where
  toFun K := fun y sz =>
    ⟨leafCProfile K.1 y sz, by
      apply LinearMap.mem_ker.mpr
      have hK := LinearMap.mem_ker.mp K.2
      have h := congrFun (congrFun hK y) sz
      exact h⟩
  invFun f :=
    ⟨fun p y sz w => (f y sz).1 p w, by
      apply LinearMap.mem_ker.mpr
      funext y sz
      have hf := LinearMap.mem_ker.mp (f y sz).2
      exact hf⟩
  left_inv K := by
    apply Subtype.ext
    funext p y sz w
    rfl
  right_inv f := by
    funext y sz
    apply Subtype.ext
    funext p w
    rfl

noncomputable def leafBVisFiberEquivProfileKernelCoord
    {n a c d : ℕ} [NeZero n] (V : LeafBVisible n c d) :
    LeafBVisFiber (n := n) (a := a) (c := c) (d := d) V
      ≃
    (I n → ZVec n c → LeafProfileKernel n a d) :=
  (leafBVisFiberEquivKer (n := n) (a := a) (c := c) (d := d) V).trans
    (leafBVisKernelEquivProfileKernelCoord (n := n) (a := a) (c := c) (d := d))

noncomputable def leafCVisFiberEquivProfileKernelCoord
    {n a b d : ℕ} [NeZero n] (V : LeafCVisible n b d) :
    LeafCVisFiber (n := n) (a := a) (b := b) (d := d) V
      ≃
    (YVec n b → I n → LeafProfileKernel n a d) :=
  (leafCVisFiberEquivKer (n := n) (a := a) (b := b) (d := d) V).trans
    (leafCVisKernelEquivProfileKernelCoord (n := n) (a := a) (b := b) (d := d))

theorem card_ker_leafBVisMap_profileKernelCoord {n a c d : ℕ} [NeZero n] :
    Fintype.card
        (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d)))
      =
      (Fintype.card (LeafProfileKernel n a d) ^ Fintype.card (ZVec n c))
        ^ Fintype.card (I n) := by
  rw [Fintype.card_congr
    (leafBVisKernelEquivProfileKernelCoord (n := n) (a := a) (c := c) (d := d))]
  rw [Fintype.card_fun]
  rw [Fintype.card_fun]

theorem card_ker_leafCVisMap_profileKernelCoord {n a b d : ℕ} [NeZero n] :
    Fintype.card
        (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d)))
      =
      (Fintype.card (LeafProfileKernel n a d) ^ Fintype.card (I n))
        ^ Fintype.card (YVec n b) := by
  rw [Fintype.card_congr
    (leafCVisKernelEquivProfileKernelCoord (n := n) (a := a) (b := b) (d := d))]
  rw [Fintype.card_fun]
  rw [Fintype.card_fun]

theorem card_LeafProfileKernel_eq_pow_finrank {n a d : ℕ} [NeZero n] :
    Fintype.card (LeafProfileKernel n a d) =
      2 ^ Module.finrank F (LeafProfileKernel n a d) := by
  rw [← Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

end

end TriangleLeaf
end Core4loop
