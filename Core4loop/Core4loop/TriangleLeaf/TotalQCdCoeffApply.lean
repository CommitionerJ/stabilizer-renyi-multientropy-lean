import Core4loop.TriangleLeaf.TotalQCdCoeff

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private theorem sum_y_sz_p_s_z_comm
    {Y SZ P S Z : Type*}
    [Fintype Y] [Fintype SZ] [Fintype P] [Fintype S] [Fintype Z]
    (f : Y → SZ → P → S → Z → F) :
    (∑ y : Y, ∑ sz : SZ, ∑ p : P, ∑ s : S, ∑ z : Z, f y sz p s z)
      =
      ∑ y : Y, ∑ z : Z, ∑ p : P, ∑ s : S, ∑ sz : SZ, f y sz p s z := by
  refine Finset.sum_congr rfl ?_
  intro y _
  calc
    (∑ sz : SZ, ∑ p : P, ∑ s : S, ∑ z : Z, f y sz p s z)
        =
        ∑ sz : SZ, ∑ z : Z, ∑ p : P, ∑ s : S, f y sz p s z := by
          refine Finset.sum_congr rfl ?_
          intro sz _
          calc
            (∑ p : P, ∑ s : S, ∑ z : Z, f y sz p s z)
                = ∑ p : P, ∑ z : Z, ∑ s : S, f y sz p s z := by
                  refine Finset.sum_congr rfl ?_
                  intro p _
                  rw [Finset.sum_comm]
            _ = ∑ z : Z, ∑ p : P, ∑ s : S, f y sz p s z := by
                  rw [Finset.sum_comm]
    _ =
        ∑ z : Z, ∑ sz : SZ, ∑ p : P, ∑ s : S, f y sz p s z := by
          rw [Finset.sum_comm]
    _ =
        ∑ z : Z, ∑ p : P, ∑ s : S, ∑ sz : SZ, f y sz p s z := by
          refine Finset.sum_congr rfl ?_
          intro z _
          calc
            (∑ sz : SZ, ∑ p : P, ∑ s : S, f y sz p s z)
                = ∑ p : P, ∑ sz : SZ, ∑ s : S, f y sz p s z := by
                  rw [Finset.sum_comm]
            _ = ∑ p : P, ∑ s : S, ∑ sz : SZ, f y sz p s z := by
                  refine Finset.sum_congr rfl ?_
                  intro p _
                  rw [Finset.sum_comm]

private theorem sum_i_p_s_omega_comm
    {ι P S Ω : Type*} [Fintype ι] [Fintype P] [Fintype S] [Fintype Ω]
    (f : ι → P → S → Ω → F) :
    (∑ i : ι, ∑ p : P, ∑ s : S, ∑ ω : Ω, f i p s ω)
      =
      ∑ ω : Ω, ∑ i : ι, ∑ p : P, ∑ s : S, f i p s ω := by
  calc
    (∑ i : ι, ∑ p : P, ∑ s : S, ∑ ω : Ω, f i p s ω)
        =
        ∑ i : ι, ∑ p : P, ∑ ω : Ω, ∑ s : S, f i p s ω := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [Finset.sum_comm]
    _ =
        ∑ i : ι, ∑ ω : Ω, ∑ p : P, ∑ s : S, f i p s ω := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_comm]
    _ =
        ∑ ω : Ω, ∑ i : ι, ∑ p : P, ∑ s : S, f i p s ω := by
          rw [Finset.sum_comm]

private def qLeafProfileKernelRemainderCdCoeffLeft
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n a) (s : I n) : F :=
  ∑ z : ZVec n c,
    if i.2 = vecSum z then
      (∑ ω : PassiveVisibleIndex n d hd,
        if s = vecSum ω.1 then
          (XB.1 ω (vecSum i.1) z).1 p
        else 0)
      +
      (Fintype.card (Vec n (d - 1)) : F) *
        (XB.2 (vecSum i.1) z p).1 s
    else 0

private def qLeafProfileKernelRemainderCdCoeffRight
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n a) (s : I n) : F :=
  ∑ z : ZVec n c,
    if i.2 = vecSum z + 1 then
      (∑ ω : PassiveVisibleIndex n d hd,
        if s = vecSum ω.1 then
          (XB.1 ω (vecSum i.1 + 1) z).1 p
        else 0)
      +
      (Fintype.card (Vec n (d - 1)) : F) *
        (XB.2 (vecSum i.1 + 1) z p).1 s
    else 0

private theorem qLeafProfileKernelRemainderCdCoeff_eq_left_add_right
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelRemainderCdCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB
      =
      fun i p s =>
        qLeafProfileKernelRemainderCdCoeffLeft
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p s
        +
        qLeafProfileKernelRemainderCdCoeffRight
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p s := by
  rfl

private theorem qLeafProfileKernelRemainderCdCoeffLeft_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    leafDiffFamilyCoeffApply
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
        (qLeafProfileKernelRemainderCdCoeffLeft
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
        (fun i => kCd i.1 i.2)
      =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
        ((∑ ω : PassiveVisibleIndex n d hd,
          (XB.1 ω (vecSum y) z).1 p *
            (kCd y (vecSum z) p).1 (vecSum ω.1))
        +
        (Fintype.card (Vec n (d - 1)) : F) *
          ∑ s : I n,
            (XB.2 (vecSum y) z p).1 s *
              (kCd y (vecSum z) p).1 s) := by
  unfold leafDiffFamilyCoeffApply leafDiffCoeffApply
    qLeafProfileKernelRemainderCdCoeffLeft
  rw [Fintype.sum_prod_type]
  conv =>
    lhs
    simp only [Finset.mul_sum]
  rw [sum_y_sz_p_s_z_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro z _
  refine Finset.sum_congr rfl ?_
  intro p _
  calc
    (∑ s : I n,
        ∑ sz : I n,
          (kCd y sz p).1 s *
            if sz = vecSum z then
              (∑ ω : PassiveVisibleIndex n d hd,
                if s = vecSum ω.1 then (XB.1 ω (vecSum y) z).1 p else 0)
              +
              (Fintype.card (Vec n (d - 1)) : F) *
                (XB.2 (vecSum y) z p).1 s
            else 0)
        =
        ∑ s : I n,
          (kCd y (vecSum z) p).1 s *
            ((∑ ω : PassiveVisibleIndex n d hd,
              if s = vecSum ω.1 then (XB.1 ω (vecSum y) z).1 p else 0)
            +
            (Fintype.card (Vec n (d - 1)) : F) *
              (XB.2 (vecSum y) z p).1 s) := by
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [sum_mul_ite_eq]
    _ =
        (∑ ω : PassiveVisibleIndex n d hd,
          (XB.1 ω (vecSum y) z).1 p *
            (kCd y (vecSum z) p).1 (vecSum ω.1))
        +
        (Fintype.card (Vec n (d - 1)) : F) *
          ∑ s : I n,
            (XB.2 (vecSum y) z p).1 s *
              (kCd y (vecSum z) p).1 s := by
          rw [sum_mul_add_selector_weight
            (K := fun s : I n => (kCd y (vecSum z) p).1 s)
            (B := fun s : I n => (XB.2 (vecSum y) z p).1 s)
            (A := fun ω : PassiveVisibleIndex n d hd =>
              (XB.1 ω (vecSum y) z).1 p)
            (target := fun ω : PassiveVisibleIndex n d hd => vecSum ω.1)
            (w := (Fintype.card (Vec n (d - 1)) : F))]

private theorem qLeafProfileKernelRemainderCdCoeffRight_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    leafDiffFamilyCoeffApply
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
        (qLeafProfileKernelRemainderCdCoeffRight
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
        (fun i => kCd i.1 i.2)
      =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
        ((∑ ω : PassiveVisibleIndex n d hd,
          (XB.1 ω (vecSum y + 1) z).1 p *
            (kCd y (vecSum z + 1) p).1 (vecSum ω.1))
        +
        (Fintype.card (Vec n (d - 1)) : F) *
          ∑ s : I n,
            (XB.2 (vecSum y + 1) z p).1 s *
              (kCd y (vecSum z + 1) p).1 s) := by
  unfold leafDiffFamilyCoeffApply leafDiffCoeffApply
    qLeafProfileKernelRemainderCdCoeffRight
  rw [Fintype.sum_prod_type]
  conv =>
    lhs
    simp only [Finset.mul_sum]
  rw [sum_y_sz_p_s_z_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro z _
  refine Finset.sum_congr rfl ?_
  intro p _
  calc
    (∑ s : I n,
        ∑ sz : I n,
          (kCd y sz p).1 s *
            if sz = vecSum z + 1 then
              (∑ ω : PassiveVisibleIndex n d hd,
                if s = vecSum ω.1 then (XB.1 ω (vecSum y + 1) z).1 p else 0)
              +
              (Fintype.card (Vec n (d - 1)) : F) *
                (XB.2 (vecSum y + 1) z p).1 s
            else 0)
        =
        ∑ s : I n,
          (kCd y (vecSum z + 1) p).1 s *
            ((∑ ω : PassiveVisibleIndex n d hd,
              if s = vecSum ω.1 then (XB.1 ω (vecSum y + 1) z).1 p else 0)
            +
            (Fintype.card (Vec n (d - 1)) : F) *
              (XB.2 (vecSum y + 1) z p).1 s) := by
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [sum_mul_ite_eq]
    _ =
        (∑ ω : PassiveVisibleIndex n d hd,
          (XB.1 ω (vecSum y + 1) z).1 p *
            (kCd y (vecSum z + 1) p).1 (vecSum ω.1))
        +
        (Fintype.card (Vec n (d - 1)) : F) *
          ∑ s : I n,
            (XB.2 (vecSum y + 1) z p).1 s *
              (kCd y (vecSum z + 1) p).1 s := by
          rw [sum_mul_add_selector_weight
            (K := fun s : I n => (kCd y (vecSum z + 1) p).1 s)
            (B := fun s : I n => (XB.2 (vecSum y + 1) z p).1 s)
            (A := fun ω : PassiveVisibleIndex n d hd =>
              (XB.1 ω (vecSum y + 1) z).1 p)
            (target := fun ω : PassiveVisibleIndex n d hd => vecSum ω.1)
            (w := (Fintype.card (Vec n (d - 1)) : F))]

theorem qLeafProfileKernelRemainderCdCoeff_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    leafDiffFamilyCoeffApply
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
        (qLeafProfileKernelRemainderCdCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
        (fun i => kCd i.1 i.2)
      =
      qLeafProfileKernelRemainderCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd := by
  calc
    leafDiffFamilyCoeffApply
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
        (qLeafProfileKernelRemainderCdCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
        (fun i => kCd i.1 i.2)
        =
        leafDiffFamilyCoeffApply
          (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
          (fun i p s =>
            qLeafProfileKernelRemainderCdCoeffLeft
              (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p s
            +
            qLeafProfileKernelRemainderCdCoeffRight
              (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p s)
          (fun i => kCd i.1 i.2) := by
          rw [qLeafProfileKernelRemainderCdCoeff_eq_left_add_right
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB]
    _ =
        leafDiffFamilyCoeffApply
          (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
          (qLeafProfileKernelRemainderCdCoeffLeft
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
          (fun i => kCd i.1 i.2)
        +
        leafDiffFamilyCoeffApply
          (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
          (qLeafProfileKernelRemainderCdCoeffRight
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
          (fun i => kCd i.1 i.2) := by
          unfold leafDiffFamilyCoeffApply leafDiffCoeffApply
          simp only [Finset.sum_add_distrib, mul_add]
    _ =
        (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
          ((∑ ω : PassiveVisibleIndex n d hd,
            (XB.1 ω (vecSum y) z).1 p *
              (kCd y (vecSum z) p).1 (vecSum ω.1))
          +
          (Fintype.card (Vec n (d - 1)) : F) *
            ∑ s : I n,
              (XB.2 (vecSum y) z p).1 s *
                (kCd y (vecSum z) p).1 s))
        +
        (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
          ((∑ ω : PassiveVisibleIndex n d hd,
            (XB.1 ω (vecSum y + 1) z).1 p *
              (kCd y (vecSum z + 1) p).1 (vecSum ω.1))
          +
          (Fintype.card (Vec n (d - 1)) : F) *
            ∑ s : I n,
              (XB.2 (vecSum y + 1) z p).1 s *
                (kCd y (vecSum z + 1) p).1 s)) := by
          rw [qLeafProfileKernelRemainderCdCoeffLeft_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd]
          rw [qLeafProfileKernelRemainderCdCoeffRight_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd]
    _ =
        qLeafProfileKernelRemainderCdPart
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd := by
          unfold qLeafProfileKernelRemainderCdPart
          rfl

private theorem core3_sumY_eq_vecSum {n b : ℕ} [NeZero n] (y : YVec n b) :
    Core3loop.sumY (b := b) (n := n) y = vecSum y := by
  rfl

private theorem core3_sumZ_eq_vecSum {n c : ℕ} [NeZero n] (z : ZVec n c) :
    Core3loop.sumZ (c := c) (n := n) z = vecSum z := by
  rfl

private def qLeafScalarCanonicalProfileBlockCdCoeffLeft
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n a) (s : I n) : F :=
  ∑ z : ZVec n c,
    if p = (zeroVec : PVec n a) then
      if s = vecSum ω.1 then
        if i.2 = vecSum z then
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
              (vecSum i.1) z
        else 0
      else 0
    else 0

private def qLeafScalarCanonicalProfileBlockCdCoeffRight
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n a) (s : I n) : F :=
  ∑ z : ZVec n c,
    if p = (zeroVec : PVec n a) then
      if s = vecSum ω.1 then
        if i.2 = vecSum z + 1 then
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
              (vecSum i.1 + 1) z
        else 0
      else 0
    else 0

private theorem qLeafScalarCanonicalProfileBlockCdCoeff_eq_left_add_right
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd) :
    qLeafScalarCanonicalProfileBlockCdCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω
      =
      fun i p s =>
        qLeafScalarCanonicalProfileBlockCdCoeffLeft
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω i p s
        +
        qLeafScalarCanonicalProfileBlockCdCoeffRight
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω i p s := by
  funext i p s
  by_cases hp : p = (zeroVec : PVec n a)
  · by_cases hs : s = vecSum ω.1
    · simp [qLeafScalarCanonicalProfileBlockCdCoeff,
        qLeafScalarCanonicalProfileBlockCdCoeffLeft,
        qLeafScalarCanonicalProfileBlockCdCoeffRight, hp, hs]
    · simp [qLeafScalarCanonicalProfileBlockCdCoeff,
        qLeafScalarCanonicalProfileBlockCdCoeffLeft,
        qLeafScalarCanonicalProfileBlockCdCoeffRight, hp, hs]
  · simp [qLeafScalarCanonicalProfileBlockCdCoeff,
      qLeafScalarCanonicalProfileBlockCdCoeffLeft,
      qLeafScalarCanonicalProfileBlockCdCoeffRight, hp]

private theorem qLeafScalarCanonicalProfileBlockCdCoeffLeft_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    leafDiffFamilyCoeffApply
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
        (qLeafScalarCanonicalProfileBlockCdCoeffLeft
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω)
        (fun i => kCd i.1 i.2)
      =
      ∑ y : YVec n b, ∑ z : ZVec n c,
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          (vecSum y) z *
        (kCd y (vecSum z) (zeroVec : PVec n a)).1 (vecSum ω.1) := by
  unfold leafDiffFamilyCoeffApply leafDiffCoeffApply
    qLeafScalarCanonicalProfileBlockCdCoeffLeft
  rw [Fintype.sum_prod_type]
  conv =>
    lhs
    simp only [Finset.mul_sum]
  rw [sum_y_sz_p_s_z_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [sum_mul_triple_ite_eq
    (K := fun sz p s => (kCd y sz p).1 s)
    (a₀ := vecSum z)
    (b₀ := (zeroVec : PVec n a))
    (c₀ := vecSum ω.1)
    (C := ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
      (vecSum y) z)]

private theorem qLeafScalarCanonicalProfileBlockCdCoeffRight_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    leafDiffFamilyCoeffApply
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
        (qLeafScalarCanonicalProfileBlockCdCoeffRight
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω)
        (fun i => kCd i.1 i.2)
      =
      ∑ y : YVec n b, ∑ z : ZVec n c,
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          (vecSum y + 1) z *
        (kCd y (vecSum z + 1) (zeroVec : PVec n a)).1 (vecSum ω.1) := by
  unfold leafDiffFamilyCoeffApply leafDiffCoeffApply
    qLeafScalarCanonicalProfileBlockCdCoeffRight
  rw [Fintype.sum_prod_type]
  conv =>
    lhs
    simp only [Finset.mul_sum]
  rw [sum_y_sz_p_s_z_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [sum_mul_triple_ite_eq
    (K := fun sz p s => (kCd y sz p).1 s)
    (a₀ := vecSum z + 1)
    (b₀ := (zeroVec : PVec n a))
    (c₀ := vecSum ω.1)
    (C := ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
      (vecSum y + 1) z)]

theorem qLeafScalarCanonicalProfileBlockCdCoeff_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    leafDiffFamilyCoeffApply
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
        (qLeafScalarCanonicalProfileBlockCdCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω)
        (fun i => kCd i.1 i.2)
      =
      qLeafScalarCanonicalProfileBlockCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H kCd ω := by
  let bcoef : Core3loop.ScalarBCoef c n :=
    ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
  calc
    leafDiffFamilyCoeffApply
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
        (qLeafScalarCanonicalProfileBlockCdCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω)
        (fun i => kCd i.1 i.2)
        =
        leafDiffFamilyCoeffApply
          (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
          (fun i p s =>
            qLeafScalarCanonicalProfileBlockCdCoeffLeft
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω i p s
            +
            qLeafScalarCanonicalProfileBlockCdCoeffRight
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω i p s)
          (fun i => kCd i.1 i.2) := by
          rw [qLeafScalarCanonicalProfileBlockCdCoeff_eq_left_add_right
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω]
    _ =
        leafDiffFamilyCoeffApply
          (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
          (qLeafScalarCanonicalProfileBlockCdCoeffLeft
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω)
          (fun i => kCd i.1 i.2)
        +
        leafDiffFamilyCoeffApply
          (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
          (qLeafScalarCanonicalProfileBlockCdCoeffRight
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω)
          (fun i => kCd i.1 i.2) := by
          unfold leafDiffFamilyCoeffApply leafDiffCoeffApply
          simp only [Finset.sum_add_distrib, mul_add]
    _ =
        (∑ y : YVec n b, ∑ z : ZVec n c,
          bcoef (vecSum y) z *
            (kCd y (vecSum z) (zeroVec : PVec n a)).1 (vecSum ω.1))
        +
        (∑ y : YVec n b, ∑ z : ZVec n c,
          bcoef (vecSum y + 1) z *
            (kCd y (vecSum z + 1) (zeroVec : PVec n a)).1 (vecSum ω.1)) := by
          dsimp [bcoef]
          rw [qLeafScalarCanonicalProfileBlockCdCoeffLeft_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω kCd]
          rw [qLeafScalarCanonicalProfileBlockCdCoeffRight_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω kCd]
    _ =
        qLeafScalarCanonicalProfileBlockCdPart
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H kCd ω := by
          unfold qLeafScalarCanonicalProfileBlockCdPart
            leafCDiffCanonicalScalarIndexDiff
          dsimp [bcoef]
          rw [Core3loop.qScalar]
          rw [Core3loop.qLeftScalar_eq_sum_yz]
          rw [Core3loop.qRightScalar_eq_sum_yz]
          simp [core3_sumY_eq_vecSum]

private theorem leafDiffFamilyCoeffApply_add_sum
    {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    {n a : ℕ} [NeZero n]
    (R : ι → PVec n a → I n → F)
    (S : Ω → ι → PVec n a → I n → F)
    (X : ι → LeafDiffProfileCoord n a) :
    leafDiffFamilyCoeffApply
        (n := n) (a := a)
        (fun i p s => R i p s + ∑ ω : Ω, S ω i p s) X
      =
      leafDiffFamilyCoeffApply (n := n) (a := a) R X
        +
      ∑ ω : Ω,
        leafDiffFamilyCoeffApply (n := n) (a := a) (S ω) X := by
  unfold leafDiffFamilyCoeffApply leafDiffCoeffApply
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [sum_i_p_s_omega_comm]

theorem qLeafProfileKernelTotalCdCoeff_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    leafDiffFamilyCoeffApply
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
        (qLeafProfileKernelTotalCdCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
        (fun i => kCd i.1 i.2)
      =
      qLeafProfileKernelTotalCdExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCd := by
  unfold qLeafProfileKernelTotalCdCoeff
    qLeafProfileKernelTotalCdExplicit
  rw [leafDiffFamilyCoeffApply_add_sum
    (n := n) (a := a)
    (R := qLeafProfileKernelRemainderCdCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
    (S := fun ω =>
      qLeafScalarCanonicalProfileBlockCdCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω)
    (X := fun i : LeafCdFamilyIndex n b => kCd i.1 i.2)]
  rw [qLeafProfileKernelRemainderCdCoeff_apply
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd]
  refine congrArg (fun t =>
    qLeafProfileKernelRemainderCdPart
      (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCd + t) ?_
  refine Finset.sum_congr rfl ?_
  intro ω _
  rw [qLeafScalarCanonicalProfileBlockCdCoeff_apply
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω kCd]

private noncomputable def qLeafProfileKernelTotalCdExplicitPairLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    (LeafCdFamilyIndex n b → LeafDiffProfileCoord n a) →ₗ[F] F where
  toFun X :=
    qLeafProfileKernelTotalCdExplicitLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      (fun y s => X (y, s))
  map_add' X Y := by
    let L :=
      qLeafProfileKernelTotalCdExplicitLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
    have hfun :
        (fun y s =>
            ((X + Y : LeafCdFamilyIndex n b → LeafDiffProfileCoord n a) (y, s)))
          =
          (fun y s => X (y, s)) + (fun y s => Y (y, s)) := by
      ext y s p
      rfl
    change L (fun y s =>
        ((X + Y : LeafCdFamilyIndex n b → LeafDiffProfileCoord n a) (y, s))) =
      L (fun y s => X (y, s)) + L (fun y s => Y (y, s))
    rw [hfun]
    exact map_add L (fun y s => X (y, s)) (fun y s => Y (y, s))
  map_smul' r X := by
    let L :=
      qLeafProfileKernelTotalCdExplicitLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
    have hfun :
        (fun y s =>
            ((r • X : LeafCdFamilyIndex n b → LeafDiffProfileCoord n a) (y, s)))
          =
          r • (fun y s => X (y, s)) := by
      ext y s p
      rfl
    change L (fun y s =>
        ((r • X : LeafCdFamilyIndex n b → LeafDiffProfileCoord n a) (y, s))) =
      r • L (fun y s => X (y, s))
    rw [hfun]
    exact map_smul L r (fun y s => X (y, s))

theorem qLeafProfileKernelTotalCdExplicitLinearMap_eq_zero_iff_coeffRead
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCdExplicitLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0
      ↔
      qLeafProfileKernelTotalCdCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0 := by
  let C :=
    qLeafProfileKernelTotalCdCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
  let Lorig :=
    qLeafProfileKernelTotalCdExplicitLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
  let Lpair :=
    qLeafProfileKernelTotalCdExplicitPairLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
  have hzeroDomain :
      Lorig = 0 ↔ Lpair = 0 := by
    constructor
    · intro h
      apply LinearMap.ext
      intro X
      change Lorig (fun y s => X (y, s)) = (0 : F)
      rw [h]
      rfl
    · intro h
      apply LinearMap.ext
      intro kCd
      have hx := LinearMap.congr_fun h
        (fun i : LeafCdFamilyIndex n b => kCd i.1 i.2)
      dsimp [Lpair, qLeafProfileKernelTotalCdExplicitPairLinearMap] at hx
      simpa [Lorig] using hx
  have hLpair :
      ∀ X : LeafCdFamilyIndex n b → LeafDiffProfileCoord n a,
        Lpair X =
          leafDiffFamilyCoeffApply
            (ι := LeafCdFamilyIndex n b) (n := n) (a := a) C X := by
    intro X
    dsimp [Lpair, qLeafProfileKernelTotalCdExplicitPairLinearMap, C]
    rw [qLeafProfileKernelTotalCdExplicitLinearMap_apply
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      (fun y s => X (y, s))]
    symm
    simpa using
      qLeafProfileKernelTotalCdCoeff_apply
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
        (fun y s => X (y, s))
  change Lorig = 0 ↔
    qLeafProfileKernelTotalCdCoeffRead
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0
  rw [hzeroDomain]
  simpa [qLeafProfileKernelTotalCdCoeffRead, C, Lpair] using
    linearMap_eq_zero_iff_of_apply_eq_leafDiffFamilyCoeffApply
      (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
      Lpair C hLpair

end

end TriangleLeaf
end Core4loop
