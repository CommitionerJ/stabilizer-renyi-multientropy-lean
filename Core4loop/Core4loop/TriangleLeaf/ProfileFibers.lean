import Core4loop.TriangleLeaf.VisibleRoot

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable instance instFintypeLeafBVisible {n c d : ℕ} [NeZero n] :
    Fintype (LeafBVisible n c d) := by
  classical
  exact inferInstanceAs (Fintype (I n → ZVec n c → PassiveQuot n d))

noncomputable instance instFintypeLeafCVisible {n b d : ℕ} [NeZero n] :
    Fintype (LeafCVisible n b d) := by
  classical
  exact inferInstanceAs (Fintype (YVec n b → I n → PassiveQuot n d))

abbrev LeafVisibleKernel (n b c d : ℕ) [NeZero n] :=
  LinearMap.ker (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d))

noncomputable instance instFintypeLeafVisibleKernel {n b c d : ℕ} [NeZero n] :
    Fintype (LeafVisibleKernel n b c d) := by
  classical
  haveI : Fintype (LeafBVisible n c d × LeafCVisible n b d) := by infer_instance
  letI : Finite (LeafVisibleKernel n b c d) :=
    Finite.of_injective
      (fun H : LeafVisibleKernel n b c d =>
        (H.1 : LeafBVisible n c d × LeafCVisible n b d))
      (fun _ _ h => Subtype.ext h)
  exact Fintype.ofFinite (LeafVisibleKernel n b c d)

abbrev LeafCompatibleBC (n a b c d : ℕ) [NeZero n] :=
  {X : BFun4 n a c d × CFun4 n a b d //
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d) X.1
      + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) X.2
        ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)}

abbrev LeafBVisFiber {n a c d : ℕ} [NeZero n] (V : LeafBVisible n c d) :=
  {B : BFun4 n a c d //
    leafBVisMap (n := n) (a := a) (c := c) (d := d) B = V}

abbrev LeafCVisFiber {n a b d : ℕ} [NeZero n] (V : LeafCVisible n b d) :=
  {C : CFun4 n a b d //
    leafCVisMap (n := n) (a := a) (b := b) (d := d) C = V}

noncomputable instance instFintypeLeafBVisFiber {n a c d : ℕ} [NeZero n]
    (V : LeafBVisible n c d) :
    Fintype (LeafBVisFiber (n := n) (a := a) (c := c) (d := d) V) := by
  classical
  infer_instance

noncomputable instance instFintypeLeafCVisFiber {n a b d : ℕ} [NeZero n]
    (V : LeafCVisible n b d) :
    Fintype (LeafCVisFiber (n := n) (a := a) (b := b) (d := d) V) := by
  classical
  infer_instance

abbrev LeafVisibleFiberPair {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d) :=
  LeafBVisFiber (n := n) (a := a) (c := c) (d := d) H.1.1 ×
    LeafCVisFiber (n := n) (a := a) (b := b) (d := d) H.1.2

abbrev LeafSurvivingSigma (n a b c d : ℕ) [NeZero n] :=
  Σ H : LeafVisibleKernel n b c d,
    LeafVisibleFiberPair (n := n) (a := a) (b := b) (c := c) (d := d) H

noncomputable instance instFintypeLeafSurvivingSigma {n a b c d : ℕ} [NeZero n] :
    Fintype (LeafSurvivingSigma n a b c d) := by
  classical
  infer_instance

abbrev leafVisiblePairMap {n a b c d : ℕ} [NeZero n] :
    BFun4 n a c d × CFun4 n a b d → LeafBVisible n c d × LeafCVisible n b d :=
  fun X =>
    (leafBVisMap (n := n) (a := a) (c := c) (d := d) X.1,
      leafCVisMap (n := n) (a := a) (b := b) (d := d) X.2)

theorem leafCompatible_iff_visiblePairMap_mem_ker
    {n a b c d : ℕ} [NeZero n] (X : BFun4 n a c d × CFun4 n a b d) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d) X.1
      + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) X.2
        ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)
      ↔
      leafVisiblePairMap (n := n) (a := a) (b := b) (c := c) (d := d) X
        ∈ LinearMap.ker (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d)) :=
  triangleLeaf_compatible_iff_visiblePair_mem_ker
    (n := n) (a := a) (b := b) (c := c) (d := d) X.1 X.2

noncomputable def leafVisiblePairFiberEquiv
    {n a b c d : ℕ} [NeZero n] (H : LeafVisibleKernel n b c d) :
    {X : BFun4 n a c d × CFun4 n a b d //
      leafVisiblePairMap (n := n) (a := a) (b := b) (c := c) (d := d) X = H}
      ≃
    LeafVisibleFiberPair (n := n) (a := a) (b := b) (c := c) (d := d) H where
  toFun X :=
    (⟨X.1.1, congrArg Prod.fst X.2⟩,
      ⟨X.1.2, congrArg Prod.snd X.2⟩)
  invFun X :=
    ⟨(X.1.1, X.2.1), Prod.ext X.1.2 X.2.2⟩
  left_inv X := by
    apply Subtype.ext
    rfl
  right_inv X := by
    ext <;> rfl

noncomputable def leafCompatibleBCEquivVisibleSigma
    {n a b c d : ℕ} [NeZero n] :
    LeafCompatibleBC n a b c d ≃ LeafSurvivingSigma n a b c d :=
  (Equiv.sigmaSubtypeFiberEquivSubtype
    (leafVisiblePairMap (n := n) (a := a) (b := b) (c := c) (d := d))
    (fun X =>
      leafCompatible_iff_visiblePairMap_mem_ker
        (n := n) (a := a) (b := b) (c := c) (d := d) X)).symm.trans
    (Equiv.sigmaCongrRight
      (fun H =>
        leafVisiblePairFiberEquiv
          (n := n) (a := a) (b := b) (c := c) (d := d) H))

private lemma sum_if_eq_sum_subtype_int {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (f : α → ℤ) :
    (∑ x : α, if p x then f x else 0) =
      ∑ x : {x // p x}, f x.1 := by
  classical
  calc
    (∑ x : α, if p x then f x else 0)
        = ∑ x ∈ (Finset.univ : Finset α) with p x, f x := by
            rw [Finset.sum_filter]
    _ = ∑ x : {x // p x}, f x.1 := by
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset α)) (p := p) (f := f)).symm

def leafCompatibleResidualSum (n a b c d : ℕ) [NeZero n] : ℤ := by
  classical
  exact
    ∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d,
      if
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
          + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
            ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)
      then bitSign (Q1 B C)
      else 0

def leafCompatibleSubtypeSignSum (n a b c d : ℕ) [NeZero n] : ℤ := by
  classical
  exact ∑ X : LeafCompatibleBC n a b c d, bitSign (Q1 X.1.1 X.1.2)

def leafVisibleSigmaSignSum (n a b c d : ℕ) [NeZero n] : ℤ := by
  classical
  exact ∑ S : LeafSurvivingSigma n a b c d, bitSign (Q1 S.2.1.1 S.2.2.1)

theorem leafCompatibleResidualSum_eq_subtypeSignSum
    {n a b c d : ℕ} [NeZero n] :
    leafCompatibleResidualSum n a b c d =
      leafCompatibleSubtypeSignSum n a b c d := by
  classical
  let p : BFun4 n a c d × CFun4 n a b d → Prop :=
    fun X =>
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) X.1
        + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) X.2
          ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)
  let f : BFun4 n a c d × CFun4 n a b d → ℤ :=
    fun X => bitSign (Q1 X.1 X.2)
  have hprod :
      leafCompatibleResidualSum n a b c d =
        ∑ X : BFun4 n a c d × CFun4 n a b d,
          if p X then f X else 0 := by
    unfold leafCompatibleResidualSum
    rw [Fintype.sum_prod_type]
  calc
    leafCompatibleResidualSum n a b c d
        =
        ∑ X : BFun4 n a c d × CFun4 n a b d,
          if p X then f X else 0 := hprod
    _ = ∑ X : {X // p X}, f X.1 := by
          exact sum_if_eq_sum_subtype_int p f
    _ = leafCompatibleSubtypeSignSum n a b c d := by
          simp [leafCompatibleSubtypeSignSum, p, f]

theorem leafCompatibleSubtypeSignSum_eq_visibleSigmaSignSum
    {n a b c d : ℕ} [NeZero n] :
    leafCompatibleSubtypeSignSum n a b c d =
      leafVisibleSigmaSignSum n a b c d := by
  classical
  let e := leafCompatibleBCEquivVisibleSigma
    (n := n) (a := a) (b := b) (c := c) (d := d)
  unfold leafCompatibleSubtypeSignSum leafVisibleSigmaSignSum
  simpa [e, leafCompatibleBCEquivVisibleSigma, leafVisiblePairFiberEquiv] using
    (Equiv.sum_comp e
      (fun S : LeafSurvivingSigma n a b c d =>
        bitSign (Q1 S.2.1.1 S.2.2.1)))

theorem leafCompatibleResidualSum_eq_visibleSigmaSignSum
    {n a b c d : ℕ} [NeZero n] :
    leafCompatibleResidualSum n a b c d =
      leafVisibleSigmaSignSum n a b c d := by
  rw [leafCompatibleResidualSum_eq_subtypeSignSum,
    leafCompatibleSubtypeSignSum_eq_visibleSigmaSignSum]

end

end TriangleLeaf
end Core4loop
