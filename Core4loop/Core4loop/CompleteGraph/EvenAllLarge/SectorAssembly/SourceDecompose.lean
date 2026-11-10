import Core4loop.CompleteGraph.EvenAllLarge.SectorAssembly.Cross

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.SectorAssembly

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

private local instance scalarSectorGroup
    {n : Nat} [NeZero n] :
    AddCommGroup (K4BaseMixedScalarSector n) :=
  inferInstance

private local instance yTailLeftGroup
    {n b : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEYTailLeft n b) :=
  (TotalEEEEYTailLeft n b).addCommGroup

private local instance wTailLeftGroup
    {n d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEWTailLeft n d) :=
  (TotalEEEEWTailLeft n d).addCommGroup

private local instance aggregateZTailLeftGroup
    {n c : Nat} [NeZero n] :
    AddCommGroup (K4AggregateEEEEZKernelTail n c) :=
  (K4AggregateEEEEZKernelTail n c).addCommGroup

private local instance matrixTailGroup
    {n c : Nat} [NeZero n] :
    AddCommGroup
      (DiamondEvenAxisValueTailZero n c (MatrixProfile n)) :=
  (DiamondEvenAxisValueTailZero n c (MatrixProfile n)).addCommGroup

private local instance pureZSectorGroup
    {n c : Nat} [NeZero n] :
    AddCommGroup (K4BaseMixedZSector n c) :=
  inferInstance

private local instance yzTailLeftGroup
    {n b c : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEYZTailLeft n b c) :=
  (TotalEEEEYZTailLeft n b c).addCommGroup

private local instance wzTailLeftGroup
    {n c d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEWZTailLeft n c d) :=
  (TotalEEEEWZTailLeft n c d).addCommGroup

private local instance wBottomTailGroup
    {n d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEWBottomTail n d) :=
  (TotalEEEEWBottomTail n d).addCommGroup

private local instance zwBottomTailGroup
    {n c d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEZWBottomTail n c d) :=
  (TotalEEEEZWBottomTail n c d).addCommGroup

private local instance ywTailLeftGroup
    {n b d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEYWLeftZero n b d) :=
  (TotalEEEEYWLeftZero n b d).addCommGroup

private local instance ywzTailLeftGroup
    {n b c d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEYWZLeftZero n b c d) :=
  (TotalEEEEYWZLeftZero n b c d).addCommGroup

private noncomputable abbrev SectorSource
    (n b c d : Nat) [NeZero n] :=
  K4BaseMixedOverlapSectorSource n b c d

private noncomputable abbrev SectorReachable
    (n b c d : Nat) [NeZero n] :=
  DiamondEvenPReachableA n b c d

noncomputable def k4BaseSectorDescendedCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    SectorSource n b c d →ₗ[F]
      Module.Dual F (SectorReachable n b c d) :=
  (k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2).comp
    (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2)

private theorem eightProdInjectionsSum
    {A B C D E G H I : Type*}
    [AddCommMonoid A] [AddCommMonoid B]
    [AddCommMonoid C] [AddCommMonoid D]
    [AddCommMonoid E] [AddCommMonoid G]
    [AddCommMonoid H] [AddCommMonoid I]
    (a : A) (b : B) (c : C) (d : D)
    (e : E) (g : G) (h : H) (i : I) :
    (a, (0, (0, (0, (0, (0, (0, 0))))))) +
      ((0, (b, (0, (0, (0, (0, (0, 0))))))) +
      ((0, (0, (c, (0, (0, (0, (0, 0))))))) +
      ((0, (0, (0, (d, (0, (0, (0, 0))))))) +
      ((0, (0, (0, (0, (e, (0, (0, 0))))))) +
      ((0, (0, (0, (0, (0, (g, (0, 0))))))) +
      ((0, (0, (0, (0, (0, (0, (h, 0))))))) +
        (0, (0, (0, (0, (0, (0, (0, i))))))))))))) =
      (a, (b, (c, (d, (e, (g, (h, i))))))) := by
  simp only [Prod.mk_add_mk, add_zero, zero_add]

private theorem k4BaseEightSectorSource_sum
    {n b c d : Nat} [NeZero n]
    (s : SectorSource n b c d) :
    Scalar.sectorSource (n := n) (b := b) (c := c) (d := d) s.1 +
      (PassiveY.sectorSource (n := n) (b := b) (c := c) (d := d) s.2.1 +
      (PassiveW.sectorSource (n := n) (b := b) (c := c) (d := d) s.2.2.1 +
      (PureZ.sectorSource (n := n) (b := b) (c := c) (d := d)
          s.2.2.2.1 +
      (PassiveYZ.sectorSource (n := n) (b := b) (c := c) (d := d)
          s.2.2.2.2.1 +
      (PassiveWZ.sectorSource (n := n) (b := b) (c := c) (d := d)
          s.2.2.2.2.2.1 +
      (PassiveYW.sectorSource (n := n) (b := b) (c := c) (d := d)
          s.2.2.2.2.2.2.1 +
        PassiveYWZ.sectorSource (n := n) (b := b) (c := c) (d := d)
          s.2.2.2.2.2.2.2)))))) = s := by
  rcases s with ⟨scalar, y, w, z, yz, wz, yw, ywz⟩
  change
    (scalar, (0, (0, (0, (0, (0, (0, 0))))))) +
      ((0, (y, (0, (0, (0, (0, (0, 0))))))) +
      ((0, (0, (w, (0, (0, (0, (0, 0))))))) +
      ((0, (0, (0, (z, (0, (0, (0, 0))))))) +
      ((0, (0, (0, (0, (yz, (0, (0, 0))))))) +
      ((0, (0, (0, (0, (0, (wz, (0, 0))))))) +
      ((0, (0, (0, (0, (0, (0, (yw, 0))))))) +
        (0, (0, (0, (0, (0, (0, (0, ywz))))))))))))) =
      (scalar, (y, (w, (z, (yz, (wz, (yw, ywz)))))))
  exact eightProdInjectionsSum scalar y w z yz wz yw ywz

private theorem map_eight_sum_apply
    {S R : Type*}
    [AddCommMonoid S] [Module F S]
    [AddCommMonoid R] [Module F R]
    (L : S →ₗ[F] Module.Dual F R)
    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : S) (r : R) :
    L (x₁ + (x₂ + (x₃ + (x₄ + (x₅ + (x₆ + (x₇ + x₈))))))) r =
      L x₁ r + (L x₂ r + (L x₃ r + (L x₄ r +
        (L x₅ r + (L x₆ r + (L x₇ r + L x₈ r)))))) := by
  simp only [map_add, LinearMap.add_apply]

theorem k4BaseSectorDescendedCross_decompose
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d)
    (A : SectorReachable n b c d) :
    k4BaseSectorDescendedCross hn2 hn hb2 hc2 hd2 s A =
      Scalar.descendedCross hn2 hn hb2 hc2 hd2 s.1 A +
      (PassiveY.descendedCross hn2 hn hb2 hc2 hd2 s.2.1 A +
      (PassiveW.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.1 A +
      (PureZ.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.2.1 A +
      (PassiveYZ.descendedCross hn2 hn hb2 hc2 hd2
          s.2.2.2.2.1 A +
      (PassiveWZ.descendedCross hn2 hn hb2 hc2 hd2
          s.2.2.2.2.2.1 A + 0))))) := by
  let L := k4BaseSectorDescendedCross hn2 hn hb2 hc2 hd2
  let x₁ := Scalar.sectorSource
    (n := n) (b := b) (c := c) (d := d) s.1
  let x₂ := PassiveY.sectorSource
    (n := n) (b := b) (c := c) (d := d) s.2.1
  let x₃ := PassiveW.sectorSource
    (n := n) (b := b) (c := c) (d := d) s.2.2.1
  let x₄ := PureZ.sectorSource
    (n := n) (b := b) (c := c) (d := d) s.2.2.2.1
  let x₅ := PassiveYZ.sectorSource
    (n := n) (b := b) (c := c) (d := d) s.2.2.2.2.1
  let x₆ := PassiveWZ.sectorSource
    (n := n) (b := b) (c := c) (d := d) s.2.2.2.2.2.1
  let x₇ := PassiveYW.sectorSource
    (n := n) (b := b) (c := c) (d := d) s.2.2.2.2.2.2.1
  let x₈ := PassiveYWZ.sectorSource
    (n := n) (b := b) (c := c) (d := d) s.2.2.2.2.2.2.2
  have hs : x₁ + (x₂ + (x₃ + (x₄ + (x₅ + (x₆ + (x₇ + x₈)))))) = s := by
    exact k4BaseEightSectorSource_sum s
  have h₁ : L x₁ A = Scalar.descendedCross hn2 hn hb2 hc2 hd2 s.1 A := by
    change k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
      (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₁) A = _
    rw [show k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₁ =
      Scalar.mixedOverlap hn hb2 hc2 hd2 s.1 by
        exact Scalar.sectorBuild_eq_mixedOverlap hn hb2 hc2 hd2 s.1]
    rfl
  have h₂ : L x₂ A = PassiveY.descendedCross hn2 hn hb2 hc2 hd2 s.2.1 A := by
    change k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
      (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₂) A = _
    rw [show k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₂ =
      PassiveY.mixedOverlap hn hb2 hc2 hd2 s.2.1 by
        exact PassiveY.sectorBuild_eq_mixedOverlap hn hb2 hc2 hd2 s.2.1]
    rfl
  have h₃ : L x₃ A = PassiveW.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.1 A := by
    change k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
      (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₃) A = _
    rw [show k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₃ =
      PassiveW.mixedOverlap hn hb2 hc2 hd2 s.2.2.1 by
        exact PassiveW.sectorBuild_eq_mixedOverlap hn hb2 hc2 hd2 s.2.2.1]
    rfl
  have h₄ : L x₄ A = PureZ.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.2.1 A := by
    change k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
      (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₄) A = _
    rw [show k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₄ =
      PureZ.mixedOverlap hn hb2 hc2 hd2 s.2.2.2.1 by
        exact PureZ.sectorBuild_eq_mixedOverlap hn hb2 hc2 hd2 s.2.2.2.1]
    rfl
  have h₅ : L x₅ A = PassiveYZ.descendedCross hn2 hn hb2 hc2 hd2
      s.2.2.2.2.1 A := by
    change k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
      (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₅) A = _
    rw [show k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₅ =
      PassiveYZ.mixedOverlap hn hb2 hc2 hd2 s.2.2.2.2.1 by
        exact PassiveYZ.sectorBuild_eq_mixedOverlap hn hb2 hc2 hd2
          s.2.2.2.2.1]
    rfl
  have h₆ : L x₆ A = PassiveWZ.descendedCross hn2 hn hb2 hc2 hd2
      s.2.2.2.2.2.1 A := by
    change k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
      (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₆) A = _
    rw [show k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₆ =
      PassiveWZ.mixedOverlap hn hb2 hc2 hd2 s.2.2.2.2.2.1 by
        exact PassiveWZ.sectorBuild_eq_mixedOverlap hn hb2 hc2 hd2
          s.2.2.2.2.2.1]
    rfl
  have h₇ : L x₇ A = PassiveYW.descendedCross hn2 hn hb2 hc2 hd2
      s.2.2.2.2.2.2.1 A := by
    change k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
      (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₇) A = _
    rw [show k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₇ =
      PassiveYW.mixedOverlap hn hb2 hc2 hd2 s.2.2.2.2.2.2.1 by
        exact PassiveYW.sectorBuild_eq_mixedOverlap hn hb2 hc2 hd2
          s.2.2.2.2.2.2.1]
    rfl
  have h₈ : L x₈ A = PassiveYWZ.descendedCross hn2 hn hb2 hc2 hd2
      s.2.2.2.2.2.2.2 A := by
    change k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
      (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₈) A = _
    rw [show k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x₈ =
      PassiveYWZ.mixedOverlap hn hb2 hc2 hd2 s.2.2.2.2.2.2.2 by
        exact PassiveYWZ.sectorBuild_eq_mixedOverlap hn hb2 hc2 hd2
          s.2.2.2.2.2.2.2]
    rfl
  calc
    k4BaseSectorDescendedCross hn2 hn hb2 hc2 hd2 s A = L s A := rfl
    _ = L (x₁ + (x₂ + (x₃ + (x₄ + (x₅ + (x₆ + (x₇ + x₈))))))) A :=
      congrArg (fun t => L t A) hs.symm
    _ = L x₁ A + (L x₂ A + (L x₃ A + (L x₄ A +
        (L x₅ A + (L x₆ A + (L x₇ A + L x₈ A)))))) :=
      map_eight_sum_apply L x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ A
    _ = _ := by
      have hz₇ : PassiveYW.descendedCross hn2 hn hb2 hc2 hd2
          s.2.2.2.2.2.2.1 A = 0 :=
        LinearMap.congr_fun
          (LinearMap.congr_fun
            (PassiveYW.descendedCross_eq_zero hn2 hn hb2 hc2 hd2)
            s.2.2.2.2.2.2.1) A
      have hz₈ : PassiveYWZ.descendedCross hn2 hn hb2 hc2 hd2
          s.2.2.2.2.2.2.2 A = 0 :=
        LinearMap.congr_fun
          (LinearMap.congr_fun
            (PassiveYWZ.descendedCross_eq_zero hn2 hn hb2 hc2 hd2)
            s.2.2.2.2.2.2.2) A
      have h₇' : L x₇ A = 0 := h₇.trans hz₇
      have h₈' : L x₈ A = 0 := h₈.trans hz₈
      have ht₇ : L x₇ A + L x₈ A = 0 := by
        exact (congrArg₂ (fun u v : F => u + v) h₇' h₈').trans
          (add_zero 0)
      have ht₆ : L x₆ A + (L x₇ A + L x₈ A) =
          PassiveWZ.descendedCross hn2 hn hb2 hc2 hd2
            s.2.2.2.2.2.1 A + 0 :=
        congrArg₂ (fun u v : F => u + v) h₆ ht₇
      have ht₅ : L x₅ A + (L x₆ A + (L x₇ A + L x₈ A)) =
          PassiveYZ.descendedCross hn2 hn hb2 hc2 hd2
            s.2.2.2.2.1 A +
          (PassiveWZ.descendedCross hn2 hn hb2 hc2 hd2
            s.2.2.2.2.2.1 A + 0) :=
        congrArg₂ (fun u v : F => u + v) h₅ ht₆
      have ht₄ : L x₄ A +
          (L x₅ A + (L x₆ A + (L x₇ A + L x₈ A))) =
          PureZ.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.2.1 A +
          (PassiveYZ.descendedCross hn2 hn hb2 hc2 hd2
            s.2.2.2.2.1 A +
          (PassiveWZ.descendedCross hn2 hn hb2 hc2 hd2
            s.2.2.2.2.2.1 A + 0)) :=
        congrArg₂ (fun u v : F => u + v) h₄ ht₅
      have ht₃ : L x₃ A + (L x₄ A +
          (L x₅ A + (L x₆ A + (L x₇ A + L x₈ A)))) =
          PassiveW.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.1 A +
          (PureZ.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.2.1 A +
          (PassiveYZ.descendedCross hn2 hn hb2 hc2 hd2
            s.2.2.2.2.1 A +
          (PassiveWZ.descendedCross hn2 hn hb2 hc2 hd2
            s.2.2.2.2.2.1 A + 0))) :=
        congrArg₂ (fun u v : F => u + v) h₃ ht₄
      have ht₂ : L x₂ A + (L x₃ A + (L x₄ A +
          (L x₅ A + (L x₆ A + (L x₇ A + L x₈ A))))) =
          PassiveY.descendedCross hn2 hn hb2 hc2 hd2 s.2.1 A +
          (PassiveW.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.1 A +
          (PureZ.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.2.1 A +
          (PassiveYZ.descendedCross hn2 hn hb2 hc2 hd2
            s.2.2.2.2.1 A +
          (PassiveWZ.descendedCross hn2 hn hb2 hc2 hd2
            s.2.2.2.2.2.1 A + 0)))) :=
        congrArg₂ (fun u v : F => u + v) h₂ ht₃
      exact congrArg₂ (fun u v : F => u + v) h₁ ht₂

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.SectorAssembly
