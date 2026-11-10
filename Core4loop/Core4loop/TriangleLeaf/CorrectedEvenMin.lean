import Core4loop.TriangleLeaf.BReadEvenAeqOne
import Core4loop.TriangleLeaf.PassiveDotFiber
import Core4loop.TriangleLeaf.CompatibleResidualBCondition
import Core4loop.TriangleLeaf.VisibleCard
import Core4loop.TriangleLeaf.AfterWResidual
import Core4loop.TriangleLeaf.ExponentSplit
import Core4loop.TriangleCore.Parity
import Core3loop.AeqOneClosed

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

theorem qLeafProfileKernelRemainderCdCoeff_eq_zero_even_one
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n 1) (s : I n) :
    qLeafProfileKernelRemainderCdCoeff
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd XB i p s = 0 := by
  have hcard :
      (Fintype.card (Vec n (d - 1)) : F) = 0 := by
    exact natCast_card_vec_eq_zero_of_even_pos
      (n := n) (k := d - 1) hn (by omega)
  have hpow : (n : F) ^ (d - 1) = 0 := by
    simpa [card_vec] using hcard
  simp [qLeafProfileKernelRemainderCdCoeff, hpow,
    leafScalarProfileKernel_one_apply]

theorem triangleLeafE2_leafVisibleKernelEquivCoord_add
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H K : LeafVisibleKernel n b c d) :
    leafVisibleKernelEquivCoord hd (H + K) =
      leafVisibleKernelEquivCoord hd H
        + leafVisibleKernelEquivCoord hd K := by
  funext ω
  apply Subtype.ext
  exact congrFun
    ((leafVisiblePairEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd).map_add H.1 K.1) ω

theorem triangleLeafE2_leafVisibleKernelEquivCoord_smul
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (r : F) (H : LeafVisibleKernel n b c d) :
    leafVisibleKernelEquivCoord hd (r • H) =
      r • leafVisibleKernelEquivCoord hd H := by
  funext ω
  apply Subtype.ext
  exact congrFun
    ((leafVisiblePairEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd).map_smul r H.1) ω

noncomputable def triangleLeafE2Aggregate
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (s : NonzeroI n) :
    LeafScalarVisibleKernel n b c :=
  (∑ ω : PassiveVisibleIndex n d hd,
      if s.1 = vecSum ω.1 then
        (leafVisibleKernelEquivCoord hd H) ω
      else 0)
    +
  ∑ ω : PassiveVisibleIndex n d hd,
    if 0 = vecSum ω.1 then
      (leafVisibleKernelEquivCoord hd H) ω
    else 0

noncomputable def triangleLeafE2Phi
    {n b c : ℕ} [NeZero n] :
    LeafScalarVisibleKernel n b c →ₗ[F]
      (Core3loop.ScalarCCoef b n × Core3loop.ScalarBCoef c n) where
  toFun X :=
    let bc :=
      leafScalarVisibleKernelEquivCore3
        (n := n) (b := b) (c := c) X
    (Core3loop.TAdjScalar bc.bcoef, Core3loop.TScalar bc.ccoef)
  map_add' X Y := by
    apply Prod.ext <;>
      simp [leafScalarVisibleKernelEquivCore3]
  map_smul' r X := by
    apply Prod.ext <;>
      simp [leafScalarVisibleKernelEquivCore3]

noncomputable def triangleLeafE2Map
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafVisibleKernel n b c d →ₗ[F]
      (NonzeroI n →
        (Core3loop.ScalarCCoef b n × Core3loop.ScalarBCoef c n)) where
  toFun H := fun s => triangleLeafE2Phi (triangleLeafE2Aggregate hd H s)
  map_add' H K := by
    funext s
    change
      triangleLeafE2Phi (triangleLeafE2Aggregate hd (H + K) s) =
        triangleLeafE2Phi (triangleLeafE2Aggregate hd H s) +
          triangleLeafE2Phi (triangleLeafE2Aggregate hd K s)
    rw [← (triangleLeafE2Phi (n := n) (b := b) (c := c)).map_add]
    congr 1
    unfold triangleLeafE2Aggregate
    rw [triangleLeafE2_leafVisibleKernelEquivCoord_add]
    simp only [Pi.add_apply, ite_add_zero, Finset.sum_add_distrib]
    abel
  map_smul' r H := by
    funext s
    change
      triangleLeafE2Phi (triangleLeafE2Aggregate hd (r • H) s) =
        r • triangleLeafE2Phi (triangleLeafE2Aggregate hd H s)
    rw [← (triangleLeafE2Phi (n := n) (b := b) (c := c)).map_smul]
    congr 1
    unfold triangleLeafE2Aggregate
    rw [triangleLeafE2_leafVisibleKernelEquivCoord_smul]
    simp [Finset.smul_sum, smul_add]

theorem triangleLeafE2Aggregate_bcoef_apply
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (s : NonzeroI n)
    (sy : I n) (z : ZVec n c) :
    (leafScalarVisibleKernelEquivCore3
        (triangleLeafE2Aggregate hd H s)).bcoef sy z
      =
    (∑ ω : PassiveVisibleIndex n d hd,
        if s.1 = vecSum ω.1 then
          ((leafVisibleKernelEquivCoord hd H) ω).1.1 sy z
        else 0)
      +
    ∑ ω : PassiveVisibleIndex n d hd,
      if 0 = vecSum ω.1 then
        ((leafVisibleKernelEquivCoord hd H) ω).1.1 sy z
      else 0 := by
  simp only [triangleLeafE2Aggregate, leafScalarVisibleKernelEquivCore3]
  apply congrArg₂ (fun x y : F => x + y)
  ·
    rw [Submodule.coe_sum]
    simp only [Prod.fst_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro ω _
    by_cases h : s.1 = vecSum ω.1 <;> simp [h]
  ·
    rw [Submodule.coe_sum]
    simp only [Prod.fst_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro ω _
    by_cases h0 : 0 = vecSum ω.1 <;> simp [h0]

theorem triangleLeafE2_sum_ite_add_zero
    {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (f g : ι → F) :
    (∑ i, if P i then f i + g i else 0) =
      (∑ i, if P i then f i else 0) +
      ∑ i, if P i then g i else 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : P i <;> simp [h]

theorem triangleLeafE2_sum_ite_sum_ite_comm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → Prop) [DecidablePred P]
    (Q : κ → Prop) [DecidablePred Q]
    (f : ι → κ → F) :
    (∑ i, if P i then (∑ k, if Q k then f i k else 0) else 0)
      =
    ∑ k, if Q k then (∑ i, if P i then f i k else 0) else 0 := by
  calc
    (∑ i, if P i then (∑ k, if Q k then f i k else 0) else 0)
        =
        ∑ i, ∑ k, if P i then (if Q k then f i k else 0) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          by_cases hi : P i <;> simp [hi]
    _ =
        ∑ k, ∑ i, if P i then (if Q k then f i k else 0) else 0 := by
          rw [Finset.sum_comm]
    _ =
        ∑ k, if Q k then (∑ i, if P i then f i k else 0) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro k _
          by_cases hk : Q k
          · simp [hk]
          · simp [hk]

theorem triangleLeafE2_totalCdCoeff_add_base_eq_TAdjScalar
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n 1) (s : NonzeroI n) :
    qLeafProfileKernelTotalCdCoeff
          (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB
          i p s.1
        +
      qLeafProfileKernelTotalCdCoeff
          (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB
          i p 0
      =
    Core3loop.TAdjScalar
      ((leafScalarVisibleKernelEquivCore3
        (triangleLeafE2Aggregate hd H s)).bcoef) i.1 i.2 := by
  letI := PVec_one_subsingleton (n := n)
  rw [Subsingleton.elim p (zeroVec : PVec n 1)]
  unfold qLeafProfileKernelTotalCdCoeff
  rw [qLeafProfileKernelRemainderCdCoeff_eq_zero_even_one hn hd2 hd]
  rw [qLeafProfileKernelRemainderCdCoeff_eq_zero_even_one hn hd2 hd]
  simp only [zero_add]
  simp only [qLeafScalarCanonicalProfileBlockCdCoeff, ite_true]
  change
    _ =
    Core3loop.BAgg
        (leafScalarVisibleKernelEquivCore3
          (triangleLeafE2Aggregate hd H s)).bcoef
        (vecSum i.1) i.2
      +
    Core3loop.BAgg
        (leafScalarVisibleKernelEquivCore3
          (triangleLeafE2Aggregate hd H s)).bcoef
        (vecSum i.1 + 1) (i.2 - 1)
  unfold Core3loop.BAgg
  simp_rw [triangleLeafE2Aggregate_bcoef_apply]
  rw [triangleLeafE2_sum_ite_add_zero]
  rw [triangleLeafE2_sum_ite_add_zero]
  have hs1 :=
    triangleLeafE2_sum_ite_sum_ite_comm
      (P := fun ω : PassiveVisibleIndex n d hd => s.1 = vecSum ω.1)
      (Q := fun z : ZVec n c => i.2 = vecSum z)
      (f := fun ω z =>
        ((leafVisibleKernelEquivCoord hd H) ω).1.1 (vecSum i.1) z)
  have hs2 :=
    triangleLeafE2_sum_ite_sum_ite_comm
      (P := fun ω : PassiveVisibleIndex n d hd => s.1 = vecSum ω.1)
      (Q := fun z : ZVec n c => i.2 = vecSum z + 1)
      (f := fun ω z =>
        ((leafVisibleKernelEquivCoord hd H) ω).1.1 (vecSum i.1 + 1) z)
  have h01 :=
    triangleLeafE2_sum_ite_sum_ite_comm
      (P := fun ω : PassiveVisibleIndex n d hd => 0 = vecSum ω.1)
      (Q := fun z : ZVec n c => i.2 = vecSum z)
      (f := fun ω z =>
        ((leafVisibleKernelEquivCoord hd H) ω).1.1 (vecSum i.1) z)
  have h02 :=
    triangleLeafE2_sum_ite_sum_ite_comm
      (P := fun ω : PassiveVisibleIndex n d hd => 0 = vecSum ω.1)
      (Q := fun z : ZVec n c => i.2 = vecSum z + 1)
      (f := fun ω z =>
        ((leafVisibleKernelEquivCoord hd H) ω).1.1 (vecSum i.1 + 1) z)
  rw [hs1, hs2, h01, h02]
  simp only [ite_add_zero, Finset.sum_add_distrib]
  have hfirst :
      ∀ z : ZVec n c,
        (i.2 = vecSum z) ↔ (Core3loop.sumZ z = i.2) := by
    intro z
    exact eq_comm
  have hshift :
      ∀ z : ZVec n c,
        (i.2 = vecSum z + 1) ↔
          (Core3loop.sumZ z = i.2 - 1) := by
    intro z
    change (i.2 = vecSum z + 1 ↔ vecSum z = i.2 - 1)
    constructor
    · intro hz
      rw [hz]
      abel
    · intro hz
      rw [hz]
      abel
  simp_rw [hfirst, hshift]
  abel

theorem triangleLeafE2_totalCvCoeffCondition
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd) :
    TotalCvCoeffCondition
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB := by
  letI := PVec_one_subsingleton (n := n)
  intro i p
  rw [Subsingleton.elim p (zeroVec : PVec n 1)]

theorem triangleLeafE2_totalBCoeffCondition_iff
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd) :
    TotalBCoeffCondition
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB
      ↔
    ∀ s : NonzeroI n,
      Core3loop.TAdjScalar (b := b) (c := c) (n := n)
        ((leafScalarVisibleKernelEquivCore3
          (triangleLeafE2Aggregate hd H s)).bcoef) = 0 := by
  constructor
  · intro hTotal s
    funext y r
    have hcoeff := hTotal.1 (y, r) (zeroVec : PVec n 1) s
    have hadd :=
      triangleLeafE2_totalCdCoeff_add_base_eq_TAdjScalar
        hn hd2 hd H XB (y, r) (zeroVec : PVec n 1) s
    rw [hcoeff] at hadd
    simpa only [F_add_self] using hadd.symm
  · intro hT
    constructor
    · intro i p s
      have hadd :=
        triangleLeafE2_totalCdCoeff_add_base_eq_TAdjScalar
          hn hd2 hd H XB i p s
      have hTs := congrFun (congrFun (hT s) i.1) i.2
      simp only [Pi.zero_apply] at hTs
      rw [hTs] at hadd
      calc
        qLeafProfileKernelTotalCdCoeff
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              hd H XB i p s.1
            =
          qLeafProfileKernelTotalCdCoeff
                (n := n) (a := 1) (b := b) (c := c) (d := d)
                hd H XB i p s.1
            + 0 := by simp
        _ =
          qLeafProfileKernelTotalCdCoeff
                (n := n) (a := 1) (b := b) (c := c) (d := d)
                hd H XB i p s.1
            +
          (qLeafProfileKernelTotalCdCoeff
                (n := n) (a := 1) (b := b) (c := c) (d := d)
                hd H XB i p s.1
            +
           qLeafProfileKernelTotalCdCoeff
                (n := n) (a := 1) (b := b) (c := c) (d := d)
                hd H XB i p 0) := by rw [hadd]
        _ =
          qLeafProfileKernelTotalCdCoeff
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              hd H XB i p 0 := by
                calc
                  qLeafProfileKernelTotalCdCoeff hd H XB i p s.1
                        +
                      (qLeafProfileKernelTotalCdCoeff hd H XB i p s.1
                        + qLeafProfileKernelTotalCdCoeff hd H XB i p 0)
                      =
                    (qLeafProfileKernelTotalCdCoeff hd H XB i p s.1
                        + qLeafProfileKernelTotalCdCoeff hd H XB i p s.1)
                      + qLeafProfileKernelTotalCdCoeff hd H XB i p 0 := by
                        abel
                  _ = qLeafProfileKernelTotalCdCoeff hd H XB i p 0 := by
                    rw [F_add_self, zero_add]
    · exact triangleLeafE2_totalCvCoeffCondition hd H XB

theorem triangleLeafE2Aggregate_ccoef_apply
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (s : NonzeroI n)
    (y : YVec n b) (r : I n) :
    (leafScalarVisibleKernelEquivCore3
        (triangleLeafE2Aggregate hd H s)).ccoef y r
      =
    (∑ ω : PassiveVisibleIndex n d hd,
        if s.1 = vecSum ω.1 then
          ((leafVisibleKernelEquivCoord hd H) ω).1.2 y r
        else 0)
      +
    ∑ ω : PassiveVisibleIndex n d hd,
      if 0 = vecSum ω.1 then
        ((leafVisibleKernelEquivCoord hd H) ω).1.2 y r
      else 0 := by
  simp only [triangleLeafE2Aggregate, leafScalarVisibleKernelEquivCore3]
  apply congrArg₂ (fun x y : F => x + y)
  ·
    rw [Submodule.coe_sum]
    simp only [Prod.snd_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro ω _
    by_cases h : s.1 = vecSum ω.1 <;> simp [h]
  ·
    rw [Submodule.coe_sum]
    simp only [Prod.snd_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro ω _
    by_cases h0 : 0 = vecSum ω.1 <;> simp [h0]

theorem triangleLeafE2Aggregate_TScalar_apply
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (s : NonzeroI n)
    (t : I n) (z : ZVec n c) :
    Core3loop.TScalar
        ((leafScalarVisibleKernelEquivCore3
          (triangleLeafE2Aggregate hd H s)).ccoef) t z
      =
    (∑ ω : PassiveVisibleIndex n d hd,
        if s.1 = vecSum ω.1 then
          Core3loop.TScalar
            ((leafScalarVisibleKernelEquivCore3
              ((leafVisibleKernelEquivCoord hd H) ω)).ccoef) t z
        else 0)
      +
    ∑ ω : PassiveVisibleIndex n d hd,
      if 0 = vecSum ω.1 then
        Core3loop.TScalar
          ((leafScalarVisibleKernelEquivCore3
            ((leafVisibleKernelEquivCoord hd H) ω)).ccoef) t z
      else 0 := by
  have hc :
      (leafScalarVisibleKernelEquivCore3
          (triangleLeafE2Aggregate hd H s)).ccoef
        =
      (∑ ω : PassiveVisibleIndex n d hd,
          if s.1 = vecSum ω.1 then
            (leafScalarVisibleKernelEquivCore3
              ((leafVisibleKernelEquivCoord hd H) ω)).ccoef
          else 0)
        +
      ∑ ω : PassiveVisibleIndex n d hd,
        if 0 = vecSum ω.1 then
          (leafScalarVisibleKernelEquivCore3
            ((leafVisibleKernelEquivCoord hd H) ω)).ccoef
        else 0 := by
    funext y r
    rw [triangleLeafE2Aggregate_ccoef_apply]
    simp only [Pi.add_apply, Finset.sum_apply]
    apply congrArg₂ (fun x y : F => x + y)
    · refine Finset.sum_congr rfl ?_
      intro ω _
      by_cases h : s.1 = vecSum ω.1 <;>
        simp [h, leafScalarVisibleKernelEquivCore3]
    · refine Finset.sum_congr rfl ?_
      intro ω _
      by_cases h0 : 0 = vecSum ω.1 <;>
        simp [h0, leafScalarVisibleKernelEquivCore3]
  rw [hc, map_add, map_sum, map_sum]
  simp only [Pi.add_apply, Finset.sum_apply]
  apply congrArg₂ (fun x y : F => x + y)
  · refine Finset.sum_congr rfl ?_
    intro ω _
    by_cases h : s.1 = vecSum ω.1 <;> simp [h]
  · refine Finset.sum_congr rfl ?_
    intro ω _
    by_cases h0 : 0 = vecSum ω.1 <;> simp [h0]

theorem triangleLeafE2_phaseLinearMap_eq_zero_iff
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    qLeafProfileKernelTotalCvConstLinearMap
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd H = 0
      ↔
    ∀ s : NonzeroI n,
      Core3loop.TScalar (b := b) (c := c) (n := n)
        ((leafScalarVisibleKernelEquivCore3
          (triangleLeafE2Aggregate hd H s)).ccoef) = 0 := by
  classical
  let L :=
    qLeafProfileKernelTotalCvConstLinearMap
      (n := n) (a := 1) (b := b) (c := c) (d := d) hd H
  let Ldiff :
      ((I n × ZVec n c) → LeafDiffProfileCoord n 1) →ₗ[F] F :=
    { toFun := fun X => L (0, fun sy z => X (sy, z))
      map_add' := by
        intro X Y
        rw [← L.map_add]
        congr 1
      map_smul' := by
        intro r X
        rw [← L.map_smul]
        congr 1 }
  let C : (I n × ZVec n c) → PVec n 1 → I n → F :=
    fun i p s =>
      if p = (zeroVec : PVec n 1) then
        ∑ ω : PassiveVisibleIndex n d hd,
          if s = vecSum ω.1 then
            Core3loop.TScalarFun (b := b) (c := c) (n := n)
              ((leafVisibleKernelEquivCoord hd H) ω).1.2 i.1 i.2
          else 0
      else 0
  have hphase :
      ∀ X : (I n × ZVec n c) → LeafDiffProfileCoord n 1,
        Ldiff X =
          leafDiffFamilyCoeffApply
            (ι := I n × ZVec n c) (n := n) (a := 1) C X := by
    intro X
    change
      qLeafProfileKernelTotalCvConstLinearMap
          (n := n) (a := 1) (b := b) (c := c) (d := d) hd H
          (0, fun sy z => X (sy, z))
        =
      leafDiffFamilyCoeffApply
        (ι := I n × ZVec n c) (n := n) (a := 1) C X
    rw [qLeafProfileKernelTotalCvConstLinearMap_eq_scalarBTrace_visibleC]
    let TS :=
      fun (ω : PassiveVisibleIndex n d hd) (i : I n × ZVec n c) =>
        Core3loop.TScalarFun (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord hd H) ω).1.2 i.1 i.2
    calc
      (∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          (leafBReadKernelScalarBTrace hd
            (0, fun sy z => X (sy, z)) ω)
          ((leafVisibleKernelEquivCoord hd H) ω).1.2)
          =
        ∑ ω : PassiveVisibleIndex n d hd,
          ∑ i : I n × ZVec n c,
            (X i (zeroVec : PVec n 1)).1 (vecSum ω.1) * TS ω i := by
            refine Finset.sum_congr rfl ?_
            intro ω _
            rw [Core3loop.qScalar_eq_bPair_TScalarFun]
            unfold Core3loop.bPairScalar
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro sy _
            refine Finset.sum_congr rfl ?_
            intro z _
            rw [leafBReadKernelScalarBTrace_one_apply]
      _ =
        ∑ i : I n × ZVec n c,
          ∑ ω : PassiveVisibleIndex n d hd,
            TS ω i * (X i (zeroVec : PVec n 1)).1 (vecSum ω.1) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro ω _
              ring
      _ =
        ∑ i : I n × ZVec n c,
          ∑ s : I n,
            (X i (zeroVec : PVec n 1)).1 s *
              ∑ ω : PassiveVisibleIndex n d hd,
                if s = vecSum ω.1 then TS ω i else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [sum_mul_sum_ite_eq
                (K := fun s : I n =>
                  (X i (zeroVec : PVec n 1)).1 s)
                (A := fun ω : PassiveVisibleIndex n d hd => TS ω i)
                (target := fun ω : PassiveVisibleIndex n d hd =>
                  vecSum ω.1)]
      _ =
        leafDiffFamilyCoeffApply
          (ι := I n × ZVec n c) (n := n) (a := 1) C X := by
              symm
              unfold leafDiffFamilyCoeffApply leafDiffCoeffApply C
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
              · simp [TS]
              · intro p _ hp
                simp [hp]
              · simp
  have hLzero : L = 0 ↔ Ldiff = 0 := by
    constructor
    · intro hzero
      apply LinearMap.ext
      intro X
      change L (0, fun sy z => X (sy, z)) = 0
      rw [hzero]
      rfl
    · intro hzero
      apply LinearMap.ext
      intro XB
      have hfst : XB.1 = 0 := by
        funext ω sy z
        exact leafScalarProfileKernel_one_eq_zero (XB.1 ω sy z)
      have hXB : XB = (0, XB.2) := by
        apply Prod.ext
        · exact hfst
        · rfl
      rw [hXB]
      have happly := LinearMap.congr_fun hzero
        (fun i : I n × ZVec n c => XB.2 i.1 i.2)
      exact happly
  have hread :
      leafDiffFamilyCoeffRead
          (n := n) (a := 1) C = 0
        ↔
      ∀ s : NonzeroI n,
        Core3loop.TScalar (b := b) (c := c) (n := n)
          ((leafScalarVisibleKernelEquivCore3
            (triangleLeafE2Aggregate hd H s)).ccoef) = 0 := by
    letI := PVec_one_subsingleton (n := n)
    constructor
    · intro hzero s
      funext t z
      have ht := congrFun hzero
        ((t, z), ((zeroVec : PVec n 1), s))
      simp only [Pi.zero_apply] at ht
      unfold leafDiffFamilyCoeffRead leafDiffCoeffRead C at ht
      simp only [ite_true] at ht
      rw [triangleLeafE2Aggregate_TScalar_apply]
      exact ht
    · intro hzero
      funext ips
      rcases ips with ⟨⟨t, z⟩, p, s⟩
      rw [Subsingleton.elim p (zeroVec : PVec n 1)]
      unfold leafDiffFamilyCoeffRead leafDiffCoeffRead C
      simp only [ite_true, Pi.zero_apply]
      have hs := congrFun (congrFun (hzero s) t) z
      simp only [Pi.zero_apply] at hs
      rw [triangleLeafE2Aggregate_TScalar_apply] at hs
      exact hs
  rw [hLzero]
  rw [linearMap_eq_zero_iff_of_apply_eq_leafDiffFamilyCoeffApply
    (n := n) (a := 1) Ldiff C hphase]
  have hd_scope :
      hd = (by omega : 0 < d) :=
    Subsingleton.elim _ _
  simpa only [hd_scope] using hread

theorem triangleLeafE2_visibleConst_eq_zero
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    qLeafProfileKernelTotalCvVisibleConst hd H = 0 := by
  unfold qLeafProfileKernelTotalCvVisibleConst
  apply Finset.sum_eq_zero
  intro ω _
  let bc :=
    leafScalarVisibleKernelEquivCore3
      ((leafVisibleKernelEquivCoord hd H) ω)
  exact Core3loop.qScalar_eq_zero_on_visible_of_even hb hc hn bc

noncomputable def triangleLeafE2PhiKerEquiv
    {n b c : ℕ} [NeZero n] :
    LinearMap.ker
        (triangleLeafE2Phi (n := n) (b := b) (c := c))
      ≃
    Core3loop.EvenVisibleKernelData b c n where
  toFun X :=
    ⟨leafScalarVisibleKernelEquivCore3 X.1, by
      have h := X.2
      change
        (Core3loop.TAdjScalar
            (leafScalarVisibleKernelEquivCore3 X.1).bcoef,
          Core3loop.TScalar
            (leafScalarVisibleKernelEquivCore3 X.1).ccoef) = 0 at h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
  invFun X :=
    ⟨(leafScalarVisibleKernelEquivCore3).symm X.1, by
      change
        (Core3loop.TAdjScalar
            (leafScalarVisibleKernelEquivCore3
              ((leafScalarVisibleKernelEquivCore3).symm X.1)).bcoef,
          Core3loop.TScalar
            (leafScalarVisibleKernelEquivCore3
              ((leafScalarVisibleKernelEquivCore3).symm X.1)).ccoef) = 0
      rw [(leafScalarVisibleKernelEquivCore3).apply_symm_apply]
      exact Prod.ext X.2.1 X.2.2⟩
  left_inv X := by
    apply Subtype.ext
    exact (leafScalarVisibleKernelEquivCore3).symm_apply_apply X.1
  right_inv X := by
    apply Subtype.ext
    exact (leafScalarVisibleKernelEquivCore3).apply_symm_apply X.1

theorem triangleLeafE2_card_Phi_ker
    {n b c : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) :
    Fintype.card
        (LinearMap.ker
          (triangleLeafE2Phi (n := n) (b := b) (c := c)))
      =
    2 ^ (n ^ b + n ^ c - n + 1) := by
  rw [Fintype.card_congr
    (triangleLeafE2PhiKerEquiv (n := n) (b := b) (c := c))]
  exact Core3loop.card_evenVisibleKernelData_closed_min_eq_one
    hn hb hc hdeg

theorem triangleLeafE2_finrank_localSource
    {n b c : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    Module.finrank F (LeafScalarVisibleKernel n b c)
      =
    n ^ b + n ^ c + (n - 1) ^ 2 := by
  have hcard :=
    card_LeafScalarVisibleKernel
      (n := n) (b := b) (c := c) hb hc
  rw [Module.card_eq_pow_finrank
    (K := F) (V := LeafScalarVisibleKernel n b c)] at hcard
  simp only [F, ZMod.card] at hcard
  exact Nat.pow_right_injective (by omega : 1 < 2) hcard

theorem triangleLeafE2_finrank_Phi_ker
    {n b c : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) :
    Module.finrank F
        (LinearMap.ker
          (triangleLeafE2Phi (n := n) (b := b) (c := c)))
      =
    n ^ b + n ^ c - n + 1 := by
  have hcard := triangleLeafE2_card_Phi_ker
    (n := n) (b := b) (c := c) hn hb hc hdeg
  rw [Module.card_eq_pow_finrank
    (K := F)
    (V := LinearMap.ker
      (triangleLeafE2Phi (n := n) (b := b) (c := c)))] at hcard
  simp only [F, ZMod.card] at hcard
  exact Nat.pow_right_injective (by omega : 1 < 2) hcard

theorem triangleLeafE2_finrank_Phi_range
    {n b c : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafE2Phi (n := n) (b := b) (c := c)))
      =
    n * (n - 1) := by
  have hdim :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafE2Phi (n := n) (b := b) (c := c))
  rw [triangleLeafE2_finrank_Phi_ker hn hb hc hdeg,
    triangleLeafE2_finrank_localSource hb hc] at hdim
  have hn2 : 2 ≤ n := by
    rcases hn with ⟨k, hk⟩
    have hn0 : n ≠ 0 := NeZero.ne n
    omega
  have hnle : n ≤ n ^ b := Nat.le_pow hb
  have hrange :
      Module.finrank F
          (LinearMap.range
            (triangleLeafE2Phi (n := n) (b := b) (c := c)))
        =
      (n - 1) ^ 2 + n - 1 := by
    omega
  rw [hrange]
  have hnrep : n = (n - 1) + 1 := by omega
  calc
    (n - 1) ^ 2 + n - 1
        = (n - 1) ^ 2 + ((n - 1) + 1) - 1 := by rw [← hnrep]
    _ = (n - 1) ^ 2 + (n - 1) := by omega
    _ = ((n - 1) + 1) * (n - 1) := by ring
    _ = n * (n - 1) := congrArg (fun x => x * (n - 1)) hnrep.symm

noncomputable def triangleLeafE2PassiveWitnessRaw
    {n d : ℕ} [NeZero n] (hd2 : 2 ≤ d) (hd : 0 < d)
    (s : NonzeroI n) : WVec n d :=
  shiftVec
    (shiftVec (vecSumRep (n := n) (k := d) hd s.1)
      (⟨0, by omega⟩ : Fin d) 1)
    (⟨1, by omega⟩ : Fin d) (-1)

@[simp] theorem vecSum_triangleLeafE2PassiveWitnessRaw
    {n d : ℕ} [NeZero n] (hd2 : 2 ≤ d) (hd : 0 < d)
    (s : NonzeroI n) :
    vecSum (triangleLeafE2PassiveWitnessRaw hd2 hd s) = s.1 := by
  unfold triangleLeafE2PassiveWitnessRaw
  rw [vecSum_shiftVec, vecSum_shiftVec,
    vecSum_vecSumRep (n := n) (k := d) hd]
  abel

theorem triangleLeafE2PassiveWitnessRaw_ne_rep
    {n d : ℕ} [NeZero n] (hn : Even n)
    (hd2 : 2 ≤ d) (hd : 0 < d) (s : NonzeroI n) :
    triangleLeafE2PassiveWitnessRaw hd2 hd s
      ≠ vecSumRep (n := n) (k := d) hd s.1 := by
  letI : Fact (1 < n) := ⟨by
    have hn0 : n ≠ 0 := NeZero.ne n
    rcases hn with ⟨k, hk⟩
    omega⟩
  intro h
  have hi := congrFun h (⟨1, by omega⟩ : Fin d)
  simp [triangleLeafE2PassiveWitnessRaw, shiftVec] at hi

noncomputable def triangleLeafE2PassiveWitness
    {n d : ℕ} [NeZero n] (hn : Even n)
    (hd2 : 2 ≤ d) (hd : 0 < d) :
    NonzeroI n → PassiveVisibleIndex n d hd :=
  fun s =>
    ⟨triangleLeafE2PassiveWitnessRaw hd2 hd s, by
      intro t ht heq
      have hsum := congrArg (vecSum (n := n) (k := d)) heq
      rw [vecSum_triangleLeafE2PassiveWitnessRaw,
        vecSum_vecSumRep (n := n) (k := d) hd] at hsum
      subst t
      exact triangleLeafE2PassiveWitnessRaw_ne_rep hn hd2 hd s heq⟩

@[simp] theorem vecSum_triangleLeafE2PassiveWitness
    {n d : ℕ} [NeZero n] (hn : Even n)
    (hd2 : 2 ≤ d) (hd : 0 < d) (s : NonzeroI n) :
    vecSum (triangleLeafE2PassiveWitness hn hd2 hd s).1 = s.1 :=
  vecSum_triangleLeafE2PassiveWitnessRaw hd2 hd s

theorem triangleLeafE2PassiveWitness_injective
    {n d : ℕ} [NeZero n] (hn : Even n)
    (hd2 : 2 ≤ d) (hd : 0 < d) :
    Function.Injective (triangleLeafE2PassiveWitness hn hd2 hd) := by
  intro s t hst
  apply Subtype.ext
  have hval := congrArg Subtype.val hst
  change
    triangleLeafE2PassiveWitnessRaw hd2 hd s
      = triangleLeafE2PassiveWitnessRaw hd2 hd t at hval
  have hsum := congrArg (vecSum (n := n) (k := d)) hval
  rw [vecSum_triangleLeafE2PassiveWitnessRaw,
    vecSum_triangleLeafE2PassiveWitnessRaw] at hsum
  exact hsum

theorem triangleLeafE2_sum_passiveWitness_nonzero_class
    {M : Type*} [AddCommMonoid M]
    {n d : ℕ} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) (hd : 0 < d)
    (f : NonzeroI n → M) (s : NonzeroI n) :
    (∑ ω : PassiveVisibleIndex n d hd,
      if s.1 = vecSum ω.1 then
        ∑ r : NonzeroI n,
          if ω = triangleLeafE2PassiveWitness hn hd2 hd r then f r else 0
      else 0)
      = f s := by
  calc
    (∑ ω : PassiveVisibleIndex n d hd,
      if s.1 = vecSum ω.1 then
        ∑ r : NonzeroI n,
          if ω = triangleLeafE2PassiveWitness hn hd2 hd r then f r else 0
      else 0)
        =
      ∑ ω : PassiveVisibleIndex n d hd, ∑ r : NonzeroI n,
        if s.1 = vecSum ω.1 then
          (if ω = triangleLeafE2PassiveWitness hn hd2 hd r then f r else 0)
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hsω : s.1 = vecSum ω.1 <;> simp [hsω]
    _ =
      ∑ r : NonzeroI n, ∑ ω : PassiveVisibleIndex n d hd,
        if s.1 = vecSum ω.1 then
          (if ω = triangleLeafE2PassiveWitness hn hd2 hd r then f r else 0)
        else 0 := by rw [Finset.sum_comm]
    _ = ∑ r : NonzeroI n, if s = r then f r else 0 := by
      refine Finset.sum_congr rfl ?_
      intro r _
      by_cases hsr : s = r
      · subst r
        rw [Finset.sum_eq_single
          (triangleLeafE2PassiveWitness hn hd2 hd s)]
        · rw [if_pos
            (vecSum_triangleLeafE2PassiveWitness hn hd2 hd s).symm]
          simp
        · intro ω _ hne
          simp [hne]
        · simp
      · have hval : s.1 ≠ r.1 := fun h => hsr (Subtype.ext h)
        rw [if_neg hsr]
        refine Finset.sum_eq_zero ?_
        intro ω _
        by_cases hω :
            ω = triangleLeafE2PassiveWitness hn hd2 hd r
        · rw [hω]
          have hout :
              s.1 ≠ vecSum (triangleLeafE2PassiveWitness hn hd2 hd r).1 := by
            rw [vecSum_triangleLeafE2PassiveWitness]
            exact hval
          rw [if_neg hout]
        · simp [hω]
    _ = f s := by
      rw [Finset.sum_eq_single s]
      · simp
      · intro r _ hrs
        rw [if_neg (fun hsr => hrs hsr.symm)]
      · simp

theorem triangleLeafE2_sum_passiveWitness_zero_class
    {M : Type*} [AddCommMonoid M]
    {n d : ℕ} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) (hd : 0 < d)
    (f : NonzeroI n → M) :
    (∑ ω : PassiveVisibleIndex n d hd,
      if 0 = vecSum ω.1 then
        ∑ r : NonzeroI n,
          if ω = triangleLeafE2PassiveWitness hn hd2 hd r then f r else 0
      else 0)
      = 0 := by
  refine Finset.sum_eq_zero ?_
  intro ω _
  by_cases hzero : 0 = vecSum ω.1
  · rw [if_pos hzero]
    refine Finset.sum_eq_zero ?_
    intro r _
    by_cases hω : ω = triangleLeafE2PassiveWitness hn hd2 hd r
    · have hsum := congrArg (vecSum (n := n) (k := d))
        (congrArg Subtype.val hω)
      rw [vecSum_triangleLeafE2PassiveWitness] at hsum
      have hr0 : r.1 = 0 := by
        calc
          r.1 = vecSum ω.1 := hsum.symm
          _ = 0 := hzero.symm
      exact False.elim (r.2 hr0)
    · simp [hω]
  · simp [hzero]

noncomputable def triangleLeafE2RangeMap
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafVisibleKernel n b c d →ₗ[F]
      (NonzeroI n →
        LinearMap.range
          (triangleLeafE2Phi (n := n) (b := b) (c := c))) where
  toFun H := fun s =>
    ⟨triangleLeafE2Phi (triangleLeafE2Aggregate hd H s),
      ⟨triangleLeafE2Aggregate hd H s, rfl⟩⟩
  map_add' H K := by
    funext s
    apply Subtype.ext
    exact congrFun
      ((triangleLeafE2Map (n := n) (b := b) (c := c) (d := d) hd).map_add H K) s
  map_smul' r H := by
    funext s
    apply Subtype.ext
    exact congrFun
      ((triangleLeafE2Map (n := n) (b := b) (c := c) (d := d) hd).map_smul r H) s

theorem triangleLeafE2RangeMap_surjective
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) (hd : 0 < d) :
    Function.Surjective
      (triangleLeafE2RangeMap
        (n := n) (b := b) (c := c) (d := d) hd) := by
  intro X
  let f : NonzeroI n → LeafScalarVisibleKernel n b c :=
    fun s => Classical.choose (X s).2
  have hf :
      ∀ s : NonzeroI n,
        triangleLeafE2Phi (f s) = (X s).1 :=
    fun s => Classical.choose_spec (X s).2
  let G : PassiveVisibleIndex n d hd → LeafScalarVisibleKernel n b c :=
    fun ω =>
      ∑ r : NonzeroI n,
        if ω = triangleLeafE2PassiveWitness hn hd2 hd r then f r else 0
  let H : LeafVisibleKernel n b c d :=
    (leafVisibleKernelEquivCoord hd).symm G
  refine ⟨H, ?_⟩
  funext s
  apply Subtype.ext
  change triangleLeafE2Phi (triangleLeafE2Aggregate hd H s) = (X s).1
  have hcoord : leafVisibleKernelEquivCoord hd H = G := by
    exact (leafVisibleKernelEquivCoord hd).apply_symm_apply G
  have hagg : triangleLeafE2Aggregate hd H s = f s := by
    unfold triangleLeafE2Aggregate
    rw [hcoord]
    rw [triangleLeafE2_sum_passiveWitness_nonzero_class hn hd2 hd f s]
    rw [triangleLeafE2_sum_passiveWitness_zero_class hn hd2 hd f]
    simp
  rw [hagg, hf]

theorem triangleLeafE2_finrank_RangeMap_range
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafE2RangeMap
            (n := n) (b := b) (c := c) (d := d) hd))
      =
    n * (n - 1) ^ 2 := by
  rw [LinearMap.range_eq_top.mpr
    (triangleLeafE2RangeMap_surjective
      (n := n) (b := b) (c := c) (d := d) hn hd2 hd)]
  rw [finrank_top, Module.finrank_pi_fintype,
    triangleLeafE2_finrank_Phi_range hn hb hc hdeg]
  simp
  ring

theorem triangleLeafE2RangeMap_eq_zero_iff_raw
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    triangleLeafE2RangeMap hd H = 0
      ↔
    triangleLeafE2Map hd H = 0 := by
  constructor
  · intro h
    funext s
    have hs := congrFun h s
    exact congrArg Subtype.val hs
  · intro h
    funext s
    apply Subtype.ext
    exact congrFun h s

theorem triangleLeafE2Map_eq_zero_iff_components
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    triangleLeafE2Map hd H = 0
      ↔
    (∀ s : NonzeroI n,
      Core3loop.TAdjScalar (b := b) (c := c) (n := n)
        ((leafScalarVisibleKernelEquivCore3
          (triangleLeafE2Aggregate hd H s)).bcoef) = 0)
      ∧
    (∀ s : NonzeroI n,
      Core3loop.TScalar (b := b) (c := c) (n := n)
        ((leafScalarVisibleKernelEquivCore3
          (triangleLeafE2Aggregate hd H s)).ccoef) = 0) := by
  constructor
  · intro h
    constructor
    · intro s
      have hs := congrFun h s
      exact congrArg Prod.fst hs
    · intro s
      have hs := congrFun h s
      exact congrArg Prod.snd hs
  · rintro ⟨hB, hC⟩
    funext s
    exact Prod.ext (hB s) (hC s)

theorem triangleLeafE2_card_XB_one
    {n c d : ℕ} [NeZero n] (hd : 0 < d) :
    (Fintype.card
        (LeafBProfileKernelIndexDiffCoord n 1 c d hd) : ℤ)
      =
    (2 : ℤ) ^ (n ^ (c + 1) * (n - 1)) := by
  norm_cast
  rw [card_LeafBProfileKernelIndexDiffCoord_one
    (n := n) (c := c) (d := d) hd]
  rw [← pow_mul, ← pow_mul]
  congr 1
  rw [pow_succ]
  ring

theorem triangleLeafE2_sum_XB_character
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hd2 : 2 ≤ d) (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (∑ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
      if TotalBCoeffCondition
          (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB then
        bitSign
          (qLeafProfileKernelTotalCvConst
            (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB)
      else 0)
      =
    if triangleLeafE2Map hd H = 0 then
      (2 : ℤ) ^ (n ^ (c + 1) * (n - 1))
    else 0 := by
  classical
  let L :=
    qLeafProfileKernelTotalCvConstLinearMap
      (n := n) (a := 1) (b := b) (c := c) (d := d) hd H
  let B : Prop :=
    ∀ s : NonzeroI n,
      Core3loop.TAdjScalar (b := b) (c := c) (n := n)
        ((leafScalarVisibleKernelEquivCore3
          (triangleLeafE2Aggregate hd H s)).bcoef) = 0
  let C : Prop :=
    ∀ s : NonzeroI n,
      Core3loop.TScalar (b := b) (c := c) (n := n)
        ((leafScalarVisibleKernelEquivCore3
          (triangleLeafE2Aggregate hd H s)).ccoef) = 0
  have hmapiff : triangleLeafE2Map hd H = 0 ↔ B ∧ C := by
    exact triangleLeafE2Map_eq_zero_iff_components hd H
  have hcard := triangleLeafE2_card_XB_one
    (n := n) (c := c) (d := d) hd
  by_cases hB : B
  · have hcondition :
        ∀ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
          TotalBCoeffCondition
            (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB := by
      intro XB
      exact
        (triangleLeafE2_totalBCoeffCondition_iff
          hn hd2 hd H XB).2 hB
    calc
      (∑ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
        if TotalBCoeffCondition
            (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB then
          bitSign
            (qLeafProfileKernelTotalCvConst
              (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB)
        else 0)
          =
        ∑ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
          bitSign (L XB) := by
            refine Finset.sum_congr rfl ?_
            intro XB _
            rw [if_pos (hcondition XB)]
            rw [qLeafProfileKernelTotalCvConst_eq_linear_add_visibleConst]
            rw [triangleLeafE2_visibleConst_eq_zero hn hb hc hd H]
            simp [L]
      _ =
        if L = 0 then
          (Fintype.card
            (LeafBProfileKernelIndexDiffCoord n 1 c d hd) : ℤ)
        else 0 := sum_bitSign_linearMap L
      _ =
        if triangleLeafE2Map hd H = 0 then
          (2 : ℤ) ^ (n ^ (c + 1) * (n - 1))
        else 0 := by
          by_cases hC : C
          · have hL : L = 0 := by
              dsimp [L]
              exact
                (triangleLeafE2_phaseLinearMap_eq_zero_iff hd H).2 hC
            have hMap : triangleLeafE2Map hd H = 0 :=
              hmapiff.2 ⟨hB, hC⟩
            rw [if_pos hL, if_pos hMap, hcard]
          · have hL : L ≠ 0 := by
              intro hL
              apply hC
              exact
                (triangleLeafE2_phaseLinearMap_eq_zero_iff hd H).1
                  (by simpa [L] using hL)
            have hMap : triangleLeafE2Map hd H ≠ 0 := by
              intro hMap
              exact hC (hmapiff.1 hMap).2
            rw [if_neg hL, if_neg hMap]
  · have hcondition :
        ∀ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
          ¬ TotalBCoeffCondition
            (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB := by
      intro XB hTotal
      exact hB
        ((triangleLeafE2_totalBCoeffCondition_iff
          hn hd2 hd H XB).1 hTotal)
    have hMap : triangleLeafE2Map hd H ≠ 0 := by
      intro hMap
      exact hB (hmapiff.1 hMap).1
    rw [if_neg hMap]
    apply Finset.sum_eq_zero
    intro XB _
    rw [if_neg (hcondition XB)]

theorem triangleLeafE2_finrank_visibleSource
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F (LeafVisibleKernel n b c d)
      =
    (n ^ d - (n - 1)) *
      (n ^ b + n ^ c + (n - 1) ^ 2) := by
  have hcard :=
    card_LeafVisibleKernel
      (n := n) (b := b) (c := c) (d := d) hb hc hd
  rw [Module.card_eq_pow_finrank
    (K := F) (V := LeafVisibleKernel n b c d)] at hcard
  simp only [F, ZMod.card] at hcard
  rw [← pow_mul] at hcard
  have hexponent :
      Module.finrank F (LeafVisibleKernel n b c d)
        =
      (n ^ b + n ^ c + (n - 1) ^ 2) *
        (n ^ d - (n - 1)) :=
    Nat.pow_right_injective (by omega : 1 < 2) hcard
  simpa [Nat.mul_comm] using hexponent

theorem triangleLeafE2_finrank_RangeMap_ker
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker
          (triangleLeafE2RangeMap
            (n := n) (b := b) (c := c) (d := d) hd))
      =
    (n ^ d - (n - 1)) *
        (n ^ b + n ^ c + (n - 1) ^ 2)
      -
    n * (n - 1) ^ 2 := by
  have hdim :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafE2RangeMap
        (n := n) (b := b) (c := c) (d := d) hd)
  rw [triangleLeafE2_finrank_RangeMap_range hn hb hc hdeg hd2 hd,
    triangleLeafE2_finrank_visibleSource hb hc hd] at hdim
  omega

theorem triangleLeafE2_card_RangeMap_ker
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) (hd : 0 < d) :
    Fintype.card
        (LinearMap.ker
          (triangleLeafE2RangeMap
            (n := n) (b := b) (c := c) (d := d) hd))
      =
    2 ^
      ((n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2)
        -
        n * (n - 1) ^ 2) := by
  rw [Module.card_eq_pow_finrank
    (K := F)
    (V := LinearMap.ker
      (triangleLeafE2RangeMap
        (n := n) (b := b) (c := c) (d := d) hd))]
  rw [triangleLeafE2_finrank_RangeMap_ker
    hn hb hc hdeg hd2 hd]
  simp [F, ZMod.card]

theorem triangleLeafE2_sum_if_map_eq_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) (A : ℤ) :
    (∑ H : LeafVisibleKernel n b c d,
      if triangleLeafE2Map hd H = 0 then A else 0)
      =
    (Fintype.card
      (LinearMap.ker
        (triangleLeafE2RangeMap
          (n := n) (b := b) (c := c) (d := d) hd)) : ℤ) * A := by
  classical
  let p : LeafVisibleKernel n b c d → Prop :=
    fun H => triangleLeafE2Map hd H = 0
  have hp :
      ∀ H : LeafVisibleKernel n b c d,
        p H ↔ triangleLeafE2RangeMap hd H = 0 := by
    intro H
    exact (triangleLeafE2RangeMap_eq_zero_iff_raw hd H).symm
  let e :
      {H : LeafVisibleKernel n b c d // p H} ≃
        LinearMap.ker
          (triangleLeafE2RangeMap
            (n := n) (b := b) (c := c) (d := d) hd) :=
    { toFun := fun H => ⟨H.1, (hp H.1).1 H.2⟩
      invFun := fun H => ⟨H.1, (hp H.1).2 H.2⟩
      left_inv := by intro H; apply Subtype.ext; rfl
      right_inv := by intro H; apply Subtype.ext; rfl }
  have hcardNat :
      ((Finset.univ : Finset (LeafVisibleKernel n b c d)).filter p).card
        =
      Fintype.card
        (LinearMap.ker
          (triangleLeafE2RangeMap
            (n := n) (b := b) (c := c) (d := d) hd)) := by
    calc
      ((Finset.univ : Finset (LeafVisibleKernel n b c d)).filter p).card
          = Fintype.card {H : LeafVisibleKernel n b c d // p H} :=
            (Fintype.card_subtype p).symm
      _ = Fintype.card
          (LinearMap.ker
            (triangleLeafE2RangeMap
              (n := n) (b := b) (c := c) (d := d) hd)) :=
            Fintype.card_congr e
  have hcard :
      (((Finset.univ :
          Finset (LeafVisibleKernel n b c d)).filter p).card : ℤ)
        =
      (Fintype.card
        (LinearMap.ker
          (triangleLeafE2RangeMap
            (n := n) (b := b) (c := c) (d := d) hd)) : ℤ) := by
    exact_mod_cast hcardNat
  calc
    (∑ H : LeafVisibleKernel n b c d,
      if triangleLeafE2Map hd H = 0 then A else 0)
        =
      ∑ H ∈
        ((Finset.univ : Finset (LeafVisibleKernel n b c d)).filter p),
        A := by
          rw [Finset.sum_filter]
    _ =
      (((Finset.univ :
        Finset (LeafVisibleKernel n b c d)).filter p).card : ℤ) * A := by
          simp
    _ =
      (Fintype.card
        (LinearMap.ker
          (triangleLeafE2RangeMap
            (n := n) (b := b) (c := c) (d := d) hd)) : ℤ) * A := by
          rw [hcard]

theorem triangleLeafE2_kCdCvElimExpNat_one
    (n b d : ℕ) :
    kCdCvElimExpNat n 1 b d = n ^ (b + 1) * (n - 1) := by
  simp [kCdCvElimExpNat, Nat.add_comm]

theorem leafCompatibleResidualSum_eq_pow_triangleLeafE2
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) :
    leafCompatibleResidualSum n 1 b c d
      =
    (2 : ℤ) ^
      ((n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2)
        +
        (n - 1) * (n ^ (b + 1) + n ^ (c + 1))
        -
        n * (n - 1) ^ 2) := by
  classical
  have hd : 0 < d := by omega
  rw [leafCompatibleResidualSum_eq_after_XB_totalCoeffCondition_closedCard
    (n := n) (a := 1) (b := b) (c := c) (d := d)
    (by omega) hd]
  have hdim :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafE2RangeMap
        (n := n) (b := b) (c := c) (d := d) hd)
  rw [triangleLeafE2_finrank_RangeMap_range hn hb hc hdeg hd2 hd,
    triangleLeafE2_finrank_visibleSource hb hc hd] at hdim
  have hle :
      n * (n - 1) ^ 2
        ≤
      (n ^ d - (n - 1)) *
        (n ^ b + n ^ c + (n - 1) ^ 2) := by
    omega
  have hKX :
      n ^ (b + 1) * (n - 1) + n ^ (c + 1) * (n - 1)
        =
      (n - 1) * (n ^ (b + 1) + n ^ (c + 1)) := by
    ring
  have hexponent :
      ((n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2)
        -
        n * (n - 1) ^ 2)
        +
      (kCdCvElimExpNat n 1 b d
        + n ^ (c + 1) * (n - 1))
        =
      (n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2)
        +
        (n - 1) * (n ^ (b + 1) + n ^ (c + 1))
        -
        n * (n - 1) ^ 2 := by
    rw [triangleLeafE2_kCdCvElimExpNat_one n b d, hKX]
    omega
  calc
    (∑ H : LeafVisibleKernel n b c d,
      ∑ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
        if TotalBCoeffCondition
            (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB then
          (2 : ℤ) ^ kCdCvElimExpNat n 1 b d *
            bitSign
              (qLeafProfileKernelTotalCvConst
                (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB)
        else 0)
        =
      ∑ H : LeafVisibleKernel n b c d,
        (2 : ℤ) ^ kCdCvElimExpNat n 1 b d *
          (∑ XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd,
            if TotalBCoeffCondition
                (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB then
              bitSign
                (qLeafProfileKernelTotalCvConst
                  (n := n) (a := 1) (b := b) (c := c) (d := d) hd H XB)
            else 0) := by
              refine Finset.sum_congr rfl ?_
              intro H _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro XB _
              by_cases hTotal :
                  TotalBCoeffCondition
                    (n := n) (a := 1) (b := b) (c := c) (d := d)
                    hd H XB
              · simp [hTotal]
              · simp [hTotal]
    _ =
      ∑ H : LeafVisibleKernel n b c d,
        (2 : ℤ) ^ kCdCvElimExpNat n 1 b d *
          (if triangleLeafE2Map hd H = 0 then
            (2 : ℤ) ^ (n ^ (c + 1) * (n - 1))
          else 0) := by
            refine Finset.sum_congr rfl ?_
            intro H _
            rw [triangleLeafE2_sum_XB_character hn hb hc hd2 hd H]
    _ =
      ∑ H : LeafVisibleKernel n b c d,
        if triangleLeafE2Map hd H = 0 then
          (2 : ℤ) ^
            (kCdCvElimExpNat n 1 b d
              + n ^ (c + 1) * (n - 1))
        else 0 := by
            refine Finset.sum_congr rfl ?_
            intro H _
            by_cases hGood : triangleLeafE2Map hd H = 0
            · simp [hGood, pow_add]
            · simp [hGood]
    _ =
      (Fintype.card
        (LinearMap.ker
          (triangleLeafE2RangeMap
            (n := n) (b := b) (c := c) (d := d) hd)) : ℤ)
        *
      (2 : ℤ) ^
        (kCdCvElimExpNat n 1 b d
          + n ^ (c + 1) * (n - 1)) := by
            exact triangleLeafE2_sum_if_map_eq_zero hd _
    _ =
      (2 : ℤ) ^
        (((n ^ d - (n - 1)) *
            (n ^ b + n ^ c + (n - 1) ^ 2)
          -
          n * (n - 1) ^ 2)
          +
        (kCdCvElimExpNat n 1 b d
          + n ^ (c + 1) * (n - 1))) := by
            rw [triangleLeafE2_card_RangeMap_ker
              hn hb hc hdeg hd2 hd]
            norm_cast
            rw [← pow_add]
    _ =
      (2 : ℤ) ^
        ((n ^ d - (n - 1)) *
            (n ^ b + n ^ c + (n - 1) ^ 2)
          +
          (n - 1) * (n ^ (b + 1) + n ^ (c + 1))
          -
          n * (n - 1) ^ 2) := by
            rw [hexponent]

def TriangleLeafE2ResidualExpNat (b c d n : ℕ) : ℕ :=
  (n ^ d - (n - 1)) *
      (n ^ b + n ^ c + (n - 1) ^ 2)
    +
    (n - 1) * (n ^ (b + 1) + n ^ (c + 1))
    -
    n * (n - 1) ^ 2

theorem TriangleLeafE2ResidualExpNat_cast
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) :
    (TriangleLeafE2ResidualExpNat b c d n : ℤ)
      =
    CompatibleResidualExpZ 1 b c d n := by
  have hn2 : 2 ≤ n := by
    rcases hn with ⟨k, hk⟩
    have hn0 : n ≠ 0 := NeZero.ne n
    omega
  have hn1 : 1 ≤ n := by omega
  have hd : 0 < d := by omega
  have hnpos : 0 < n := by omega
  have hpowD : n ^ 2 ≤ n ^ d :=
    Nat.pow_le_pow_right hnpos hd2
  have hsq : 2 * n - 1 ≤ n ^ 2 := by
    have h2 : 2 * n ≤ n * n := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hn2
    have hsq' : 2 * n - 1 ≤ n * n := by omega
    simpa [pow_two] using hsq'
  have hlarge : 2 * n - 1 ≤ n ^ d :=
    le_trans hsq hpowD
  have hVsub : n - 1 ≤ n ^ d := by omega
  have hVn : n ≤ n ^ d - (n - 1) := by omega
  have hP :
      (n - 1) ^ 2
        ≤ n ^ b + n ^ c + (n - 1) ^ 2 := by omega
  have hRsource :
      n * (n - 1) ^ 2
        ≤
      (n ^ d - (n - 1)) *
        (n ^ b + n ^ c + (n - 1) ^ 2) := by
    calc
      n * (n - 1) ^ 2
          ≤ (n ^ d - (n - 1)) * (n - 1) ^ 2 :=
            Nat.mul_le_mul_right ((n - 1) ^ 2) hVn
      _ ≤
        (n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2) :=
            Nat.mul_le_mul_left (n ^ d - (n - 1)) hP
  have hRtotal :
      n * (n - 1) ^ 2
        ≤
      (n ^ d - (n - 1)) *
          (n ^ b + n ^ c + (n - 1) ^ 2)
        +
        (n - 1) * (n ^ (b + 1) + n ^ (c + 1)) := by
    omega
  have hgeneric : ¬ (Even n ∧ 2 ≤ b ∧ 2 ≤ c) := by
    rintro ⟨_, hb2, hc2⟩
    rcases hdeg with rfl | rfl <;> omega
  unfold TriangleLeafE2ResidualExpNat CompatibleResidualExpZ
  rw [Nat.cast_sub hRtotal]
  rw [TriangleCore.ThetaZ_triangleLeaf_eq_of_not_even_or_small
    (a := 1) (b := b) (c := c) (d := d) (n := n)
    (by omega) hd hgeneric]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub hVsub, Nat.cast_sub hn1, nPowZ, mZ, pow_add, pow_one]
  ring

theorem leafCompatibleResidualSum_eq_pow_CompatibleResidualExpZ_triangleLeafE2
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) :
    leafCompatibleResidualSum n 1 b c d
      =
    (2 : ℤ) ^ Int.toNat (CompatibleResidualExpZ 1 b c d n) := by
  rw [leafCompatibleResidualSum_eq_pow_triangleLeafE2
    hn hb hc hdeg hd2]
  change
    (2 : ℤ) ^ TriangleLeafE2ResidualExpNat b c d n =
      (2 : ℤ) ^ Int.toNat (CompatibleResidualExpZ 1 b c d n)
  congr 1
  have hcast :=
    TriangleLeafE2ResidualExpNat_cast hn hb hc hdeg hd2
  have hnat := congrArg Int.toNat hcast
  simpa using hnat

theorem triangleLeafE2_finrank_ker_KWMap_one
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker
          (KWMap (n := n) (a := 1) (b := b) (c := c) (d := d)))
      =
    n ^ (b + c) := by
  have h :=
    finrank_ker_KWMap_add
      (n := n) (a := 1) (b := b) (c := c) (d := d)
      (by omega) hd
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  have hpow :
      n ^ (1 + b + c) = n * n ^ (b + c) := by
    rw [show 1 + b + c = 1 + (b + c) by omega, pow_add]
    simp
  have hmul :
      n * n ^ (b + c)
        =
      (n - 1) * n ^ (b + c) + n ^ (b + c) := by
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    nth_rw 1 [← hn']
    ring
  rw [hpow, hmul] at h
  omega

theorem triangleLeafE2_residual_plus_front_eq_X1Z
    {n b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) :
    ((n ^ (b + c + d) + n ^ (b + c)
        + TriangleLeafE2ResidualExpNat b c d n : ℕ) : ℤ)
      =
    X1Z 1 b c d n := by
  rw [X1Z_eq_afterW_plus_compatible]
  rw [← TriangleLeafE2ResidualExpNat_cast hn hb hc hdeg hd2]
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  unfold TriangleLeafAfterWKernelExpZ nPowZ mZ
  simp only [Nat.cast_add, Nat.cast_pow]
  rw [show 1 + b + c = 1 + (b + c) by omega, pow_add]
  ring

theorem DeltaNF_triangleLeaf_eq_pow_X1Z_triangleLeafE2
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha : a = 1)
    (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) :
    DeltaNF .triangleLeaf a b c d n
      =
    (2 : ℤ) ^ Int.toNat (X1Z a b c d n) := by
  subst a
  have hd : 0 < d := by omega
  calc
    DeltaNF .triangleLeaf 1 b c d n
        =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ((2 : ℤ) ^ Module.finrank F
          (LinearMap.ker
            (KWMap (n := n) (a := 1) (b := b) (c := c) (d := d))) *
          leafCompatibleResidualSum n 1 b c d) := by
            exact DeltaNF_triangleLeaf_after_WDiff
              (n := n) (a := 1) (b := b) (c := c) (d := d)
    _ =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ((2 : ℤ) ^ (n ^ (b + c)) *
          leafCompatibleResidualSum n 1 b c d) := by
            rw [triangleLeafE2_finrank_ker_KWMap_one
              (n := n) (b := b) (c := c) (d := d) hd]
    _ =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ((2 : ℤ) ^ (n ^ (b + c)) *
          (2 : ℤ) ^ TriangleLeafE2ResidualExpNat b c d n) := by
            rw [leafCompatibleResidualSum_eq_pow_triangleLeafE2
              hn hb hc hdeg hd2]
            rfl
    _ =
      (2 : ℤ) ^
        (n ^ (b + c + d) + n ^ (b + c)
          + TriangleLeafE2ResidualExpNat b c d n) := by
            rw [← pow_add, ← pow_add]
            congr 1
            omega
    _ =
      (2 : ℤ) ^ Int.toNat (X1Z 1 b c d n) := by
            congr 1
            have hbridge :=
              triangleLeafE2_residual_plus_front_eq_X1Z
                (n := n) (b := b) (c := c) (d := d)
                hn hb hc hdeg hd2
            have hnat := congrArg Int.toNat hbridge
            simpa using hnat

end

end TriangleLeaf
end Core4loop
