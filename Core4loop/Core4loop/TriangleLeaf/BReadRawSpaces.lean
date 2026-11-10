import Core4loop.TriangleLeaf.BReadTailElimination

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafRawCTraceSpace
    (n b d : ℕ) [NeZero n] (hd : 0 < d) :=
  PassiveVisibleIndex n d hd → Core3loop.ScalarCCoef b n

abbrev LeafRawBTraceSpace
    (n c d : ℕ) [NeZero n] (hd : 0 < d) :=
  PassiveVisibleIndex n d hd → Core3loop.ScalarBCoef c n

local instance instFintypeLeafScalarEvenBlockDataRaw
    {n b c : ℕ} [NeZero n] :
    Fintype (LeafScalarEvenBlockData n b c) := by
  classical
  exact Fintype.ofFinite _

local instance instFintypeLeafRawCTraceSpace
    {n b d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype (LeafRawCTraceSpace n b d hd) := by
  classical
  exact Fintype.ofFinite _

local instance instFintypeLeafRawBTraceSpace
    {n c d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype (LeafRawBTraceSpace n c d hd) := by
  classical
  exact Fintype.ofFinite _

local instance instFintypeLeafEvenBlockTraceFamilyRaw
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype (PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c) := by
  classical
  exact Fintype.ofFinite _

def leafRawEvenBlockDataOfTraces
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (C₂ : LeafRawCTraceSpace n b d hd)
    (B₂ : LeafRawBTraceSpace n c d hd) :
    PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c :=
  fun ω =>
    (((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω,
      C₂ ω),
      B₂ ω)

theorem leafBReadTraceData_eq_rawEvenBlockDataOfTraces
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (U : LeafBReadTarget n a b c d hd)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    leafBReadTraceData
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB
      =
    leafRawEvenBlockDataOfTraces
        (n := n) (b := b) (c := c) (d := d) hd H
        (fun ω =>
          leafBReadDualScalarCTrace
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω)
        (fun ω =>
          leafBReadKernelScalarBTrace
            (n := n) (a := a) (c := c) (d := d) hd XB ω) := by
  rfl

def leafRawVisibleBasePhase
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    Core3loop.qScalar (b := b) (c := c) (n := n)
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2

def leafRawCTraceVisibleBPair
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (C₂ : LeafRawCTraceSpace n b d hd)
    (H : LeafVisibleKernel n b c d) : F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    Core3loop.qScalar (b := b) (c := c) (n := n)
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
      (C₂ ω)

def leafRawBTraceVisibleCPair
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (B₂ : LeafRawBTraceSpace n c d hd)
    (H : LeafVisibleKernel n b c d) : F :=
  ∑ ω : PassiveVisibleIndex n d hd,
    Core3loop.qScalar (b := b) (c := c) (n := n)
      (B₂ ω)
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2

private lemma prod_bitSign_eq_bitSign_sum {α : Type*} (s : Finset α)
    (f : α → F) :
    s.prod (fun a => bitSign (f a)) = bitSign (s.sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [bitSign_zero]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, bitSign_add, ih]

private lemma sum_three_eq {α : Type*} [Fintype α]
    (f g h : α → F) :
    Finset.univ.sum f + Finset.univ.sum g + Finset.univ.sum h
      =
    Finset.univ.sum (fun x : α => f x + g x + h x) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem leafEvenRawBlockProductSign_eq_bitSign_rawPhase
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (C₂ : LeafRawCTraceSpace n b d hd)
    (B₂ : LeafRawBTraceSpace n c d hd) :
    leafEvenRawBlockProductSign
        (n := n) (b := b) (c := c) (d := d) hd
        (leafRawEvenBlockDataOfTraces
          (n := n) (b := b) (c := c) (d := d) hd H C₂ B₂)
      =
    bitSign
      (leafRawVisibleBasePhase
          (n := n) (b := b) (c := c) (d := d) hd H
        + leafRawCTraceVisibleBPair
          (n := n) (b := b) (c := c) (d := d) hd C₂ H
        + leafRawBTraceVisibleCPair
          (n := n) (b := b) (c := c) (d := d) hd B₂ H) := by
  unfold leafEvenRawBlockProductSign
    leafRawEvenBlockDataOfTraces
    leafScalarEvenRawBlockSign
    leafScalarEvenRawVisibleKernelSign
    leafRawVisibleBasePhase
    leafRawCTraceVisibleBPair
    leafRawBTraceVisibleCPair
  rw [prod_bitSign_eq_bitSign_sum]
  congr 1
  exact (sum_three_eq
    (α := PassiveVisibleIndex n d hd)
    (fun ω =>
      Core3loop.qScalar (b := b) (c := c) (n := n)
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2)
    (fun ω =>
      Core3loop.qScalar (b := b) (c := c) (n := n)
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
        (C₂ ω))
    (fun ω =>
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (B₂ ω)
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2)).symm

noncomputable def leafRawEvenBlockTraceEquiv
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    (PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c)
      ≃
    (LeafVisibleKernel n b c d × LeafRawCTraceSpace n b d hd)
      × LeafRawBTraceSpace n c d hd where
  toFun X :=
    (((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd).symm
        (fun ω => (X ω).1.1),
      fun ω => (X ω).1.2),
      fun ω => (X ω).2)
  invFun T :=
    leafRawEvenBlockDataOfTraces
      (n := n) (b := b) (c := c) (d := d) hd T.1.1 T.1.2 T.2
  left_inv := by
    intro X
    funext ω
    simp [leafRawEvenBlockDataOfTraces]
  right_inv := by
    intro T
    rcases T with ⟨⟨H, C₂⟩, B₂⟩
    simp [leafRawEvenBlockDataOfTraces]

theorem sum_leafEvenRawBlockProductSign_eq_sum_raw_traces
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign
        (n := n) (b := b) (c := c) (d := d) hd X)
      =
    ∑ H : LeafVisibleKernel n b c d,
      ∑ C₂ : LeafRawCTraceSpace n b d hd,
        ∑ B₂ : LeafRawBTraceSpace n c d hd,
          leafEvenRawBlockProductSign
            (n := n) (b := b) (c := c) (d := d) hd
            (leafRawEvenBlockDataOfTraces
              (n := n) (b := b) (c := c) (d := d) hd H C₂ B₂) := by
  classical
  let e := leafRawEvenBlockTraceEquiv
    (n := n) (b := b) (c := c) (d := d) hd
  calc
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign
        (n := n) (b := b) (c := c) (d := d) hd X)
        =
      ∑ T : (LeafVisibleKernel n b c d × LeafRawCTraceSpace n b d hd)
          × LeafRawBTraceSpace n c d hd,
        leafEvenRawBlockProductSign
          (n := n) (b := b) (c := c) (d := d) hd (e.symm T) := by
        simpa [e] using
          (Equiv.sum_comp e
            (fun T :
              (LeafVisibleKernel n b c d × LeafRawCTraceSpace n b d hd)
                × LeafRawBTraceSpace n c d hd =>
              leafEvenRawBlockProductSign
                (n := n) (b := b) (c := c) (d := d) hd (e.symm T)))
    _ =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ C₂ : LeafRawCTraceSpace n b d hd,
          ∑ B₂ : LeafRawBTraceSpace n c d hd,
            leafEvenRawBlockProductSign
              (n := n) (b := b) (c := c) (d := d) hd
              (leafRawEvenBlockDataOfTraces
                (n := n) (b := b) (c := c) (d := d) hd H C₂ B₂) := by
        rw [Fintype.sum_prod_type]
        rw [Fintype.sum_prod_type]
        simp [e, leafRawEvenBlockTraceEquiv]

end

end TriangleLeaf
end Core4loop
