import Core4loop.CompleteGraph.EvenAllLarge.SectorAssembly.Transport
import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Rank
import Core4loop.CompleteGraph.EvenAllLarge.PassiveY.RangeRank
import Core4loop.CompleteGraph.EvenAllLarge.PassiveW.RangeRank
import Core4loop.CompleteGraph.EvenAllLarge.PureZ.Rank
import Core4loop.CompleteGraph.EvenAllLarge.PassiveYZ.RangeRank
import Core4loop.CompleteGraph.EvenAllLarge.PassiveWZ.RangeRank

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEERightInternal
open Core4loop.CompleteGraph.EvenP.BaseKKT
open Core4loop.CompleteGraph.EvenP.BaseKKT.SectorAssembly

noncomputable section

attribute [local instance] Fintype.ofFinite

private local instance scalarKernelGroup
    {n : Nat} [NeZero n] :
    AddCommGroup (K4AggregateEEEEScalarKernel n) :=
  (K4AggregateEEEEScalarKernel n).addCommGroup

private local instance bFreeHeadGroup
    {n : Nat} [NeZero n] : AddCommGroup (K4BFreeHeadRadical n) :=
  (K4BFreeHeadRadical n).addCommGroup

private local instance wFreeHeadGroup
    {n : Nat} [NeZero n] : AddCommGroup (K4WFreeHeadRadical n) :=
  (K4WFreeHeadRadical n).addCommGroup

private local instance scalarSectorGroup
    {n : Nat} [NeZero n] : AddCommGroup (K4BaseMixedScalarSector n) :=
  inferInstance

private local instance yTailLeftGroup
    {n b : Nat} [NeZero n] : AddCommGroup (TotalEEEEYTailLeft n b) :=
  (TotalEEEEYTailLeft n b).addCommGroup

private local instance wTailLeftGroup
    {n d : Nat} [NeZero n] : AddCommGroup (TotalEEEEWTailLeft n d) :=
  (TotalEEEEWTailLeft n d).addCommGroup

private local instance aggregateZTailLeftGroup
    {n c : Nat} [NeZero n] :
    AddCommGroup (K4AggregateEEEEZKernelTail n c) :=
  (K4AggregateEEEEZKernelTail n c).addCommGroup

private local instance matrixTailGroup
    {n c : Nat} [NeZero n] :
    AddCommGroup (DiamondEvenAxisValueTailZero n c (MatrixProfile n)) :=
  (DiamondEvenAxisValueTailZero n c (MatrixProfile n)).addCommGroup

private local instance pureZSectorGroup
    {n c : Nat} [NeZero n] : AddCommGroup (K4BaseMixedZSector n c) :=
  inferInstance

private local instance yzTailLeftGroup
    {n b c : Nat} [NeZero n] : AddCommGroup (TotalEEEEYZTailLeft n b c) :=
  (TotalEEEEYZTailLeft n b c).addCommGroup

private local instance wzTailLeftGroup
    {n c d : Nat} [NeZero n] : AddCommGroup (TotalEEEEWZTailLeft n c d) :=
  (TotalEEEEWZTailLeft n c d).addCommGroup

private local instance wBottomTailGroup
    {n d : Nat} [NeZero n] : AddCommGroup (TotalEEEEWBottomTail n d) :=
  (TotalEEEEWBottomTail n d).addCommGroup

private local instance zwBottomTailGroup
    {n c d : Nat} [NeZero n] : AddCommGroup (TotalEEEEZWBottomTail n c d) :=
  (TotalEEEEZWBottomTail n c d).addCommGroup

private local instance ywTailLeftGroup
    {n b d : Nat} [NeZero n] : AddCommGroup (TotalEEEEYWLeftZero n b d) :=
  (TotalEEEEYWLeftZero n b d).addCommGroup

private local instance ywzTailLeftGroup
    {n b c d : Nat} [NeZero n] :
    AddCommGroup (TotalEEEEYWZLeftZero n b c d) :=
  (TotalEEEEYWZLeftZero n b c d).addCommGroup

private local instance scalarRightGroup
    {n : Nat} [NeZero n] : AddCommGroup (DiamondEEEERightSource n) :=
  (DiamondEEEERightSource n).addCommGroup

private local instance yRightBaseGroup
    {n : Nat} [NeZero n] : AddCommGroup (YRightBase n) := inferInstance

private local instance wRightBaseGroup
    {n : Nat} [NeZero n] : AddCommGroup (WRightBase n) := inferInstance

private local instance ywRightBaseGroup
    {n : Nat} [NeZero n] : AddCommGroup (YWRightBase n) := inferInstance

private local instance yRightGroup
    {n b : Nat} [NeZero n] :
    AddCommGroup (DiamondEvenAxisValueTailZero n b (YRightBase n)) :=
  (DiamondEvenAxisValueTailZero n b (YRightBase n)).addCommGroup

private local instance wRightGroup
    {n d : Nat} [NeZero n] :
    AddCommGroup (DiamondEvenAxisValueTailZero n d (WRightBase n)) :=
  (DiamondEvenAxisValueTailZero n d (WRightBase n)).addCommGroup

private local instance zRightGroup
    {n c : Nat} [NeZero n] :
    AddCommGroup
      (DiamondEvenAxisValueTailZero n c (DiamondEEOERightAmbient n)) :=
  (DiamondEvenAxisValueTailZero n c (DiamondEEOERightAmbient n)).addCommGroup

private local instance yzRightGroup
    {n b c : Nat} [NeZero n] :
    AddCommGroup
      (DiamondMixedTailZero n b c (CyclicCube n × CyclicCube n)) :=
  (DiamondMixedTailZero n b c (CyclicCube n × CyclicCube n)).addCommGroup

private local instance wzRightGroup
    {n c d : Nat} [NeZero n] :
    AddCommGroup
      (DiamondMixedTailZero n c d (CyclicCube n × CyclicCube n)) :=
  (DiamondMixedTailZero n c d (CyclicCube n × CyclicCube n)).addCommGroup

private local instance ywRightGroup
    {n b d : Nat} [NeZero n] :
    AddCommGroup (DiamondMixedTailZero n b d (YWRightBase n)) :=
  (DiamondMixedTailZero n b d (YWRightBase n)).addCommGroup

private local instance dCubeTailGroup
    {n d : Nat} [NeZero n] :
    AddCommGroup (DiamondEvenAxisValueTailZero n d (CyclicCube n)) :=
  (DiamondEvenAxisValueTailZero n d (CyclicCube n)).addCommGroup

private local instance cdCubeTailGroup
    {n c d : Nat} [NeZero n] :
    AddCommGroup
      (DiamondEvenAxisValueTailZero n c
        (DiamondEvenAxisValueTailZero n d (CyclicCube n))) :=
  (DiamondEvenAxisValueTailZero n c
    (DiamondEvenAxisValueTailZero n d (CyclicCube n))).addCommGroup

private local instance ywzRightGroup
    {n b c d : Nat} [NeZero n] :
    AddCommGroup
      (DiamondEvenAxisValueTailZero n b
        (DiamondEvenAxisValueTailZero n c
          (DiamondEvenAxisValueTailZero n d (CyclicCube n)))) :=
  (DiamondEvenAxisValueTailZero n b
    (DiamondEvenAxisValueTailZero n c
      (DiamondEvenAxisValueTailZero n d (CyclicCube n)))).addCommGroup

private noncomputable def nestedDiamondCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedOverlapSectorSource n b c d →ₗ[F]
      Module.Dual F (TotalEEEERightReachableTarget n b c d) :=
  diamondCrossProd
    (Scalar.localScalarCross hn2 hn hb2 hc2 hd2)
    (diamondCrossProd
      (PassiveY.tailCross (n := n) (b := b))
      (diamondCrossProd
        (PassiveW.tailCross (n := n) (d := d))
        (diamondCrossProd
          (PureZ.tailCross (n := n) (c := c))
          (diamondCrossProd
            (PassiveYZ.tailCross (n := n) (b := b) (c := c))
            (diamondCrossProd
              (PassiveWZ.tailCross (n := n) (c := c) (d := d))
              (diamondCrossProd
                (0 : TotalEEEEYWLeftZero n b d →ₗ[F]
                  Module.Dual F (DiamondMixedTailZero n b d (YWRightBase n)))
                (0 : TotalEEEEYWZLeftZero n b c d →ₗ[F]
                  Module.Dual F
                    (DiamondEvenAxisValueTailZero n b
                      (DiamondEvenAxisValueTailZero n c
                        (DiamondEvenAxisValueTailZero n d
                          (CyclicCube n)))))))))))

private theorem productCross_eq_nestedDiamondCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2 =
      nestedDiamondCross hn2 hn hb2 hc2 hd2 := by
  apply LinearMap.ext
  intro s
  apply LinearMap.ext
  intro q
  rfl

private theorem rank_yTail
    {n b : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hb2 : 2 ≤ b) :
    Module.finrank F
        (LinearMap.range (PassiveY.tailCross (n := n) (b := b))) =
      (n ^ (b - 1) - 2) * (2 * n * (n - 1)) := by
  rw [PassiveY.tailCross,
    finrank_range_diamondTailAmplify hn2 hn hb2,
    finrank_diamondEvenAxisTailZero hn2 hn hb2,
    rank_totalEEEEYBaseCross]

private theorem rank_wTail
    {n d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range (PassiveW.tailCross (n := n) (d := d))) =
      (n ^ (d - 1) - 2) * (2 * n * (n - 1)) := by
  rw [PassiveW.tailCross,
    finrank_range_diamondTailAmplify hn2 hn hd2,
    finrank_diamondEvenAxisTailZero hn2 hn hd2,
    rank_totalEEEEWBaseCross]

private theorem rank_yzTail
    {n b c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    Module.finrank F
        (LinearMap.range
          (PassiveYZ.tailCross (n := n) (b := b) (c := c))) =
      (n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) *
        (n ^ 2 * (n - 1)) := by
  rw [PassiveYZ.tailCross,
    finrank_range_diamondMixedTailAmplify
      (n := n) (k := b) (l := c) hn2 hn hb2 hc2,
    finrank_diamondEvenAxisTailZero hn2 hn hb2,
    finrank_diamondEvenAxisTailZero hn2 hn hc2,
    rank_totalEEEEYZBaseCross]

private theorem rank_wzTail
    {n c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (PassiveWZ.tailCross (n := n) (c := c) (d := d))) =
      (n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
        (n ^ 2 * (n - 1)) := by
  rw [PassiveWZ.tailCross,
    finrank_range_diamondMixedTailAmplify
      (n := n) (k := c) (l := d) hn2 hn hc2 hd2,
    finrank_diamondEvenAxisTailZero hn2 hn hc2,
    finrank_diamondEvenAxisTailZero hn2 hn hd2,
    rank_totalEEEEWZBaseCross]

private theorem nestedDiamondCross_rank_components
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range (nestedDiamondCross hn2 hn hb2 hc2 hd2)) =
      Module.finrank F
          (LinearMap.range
            (Scalar.localScalarCross hn2 hn hb2 hc2 hd2)) +
      (Module.finrank F
          (LinearMap.range (PassiveY.tailCross (n := n) (b := b))) +
      (Module.finrank F
          (LinearMap.range (PassiveW.tailCross (n := n) (d := d))) +
      (Module.finrank F
          (LinearMap.range (PureZ.tailCross (n := n) (c := c))) +
      (Module.finrank F
          (LinearMap.range
            (PassiveYZ.tailCross (n := n) (b := b) (c := c))) +
      (Module.finrank F
          (LinearMap.range
            (PassiveWZ.tailCross (n := n) (c := c) (d := d))) +
        (0 + 0)))))) := by
  have hyw : Module.finrank F
      (LinearMap.range
        (0 : TotalEEEEYWLeftZero n b d →ₗ[F]
          Module.Dual F (DiamondMixedTailZero n b d (YWRightBase n)))) = 0 := by
    rw [LinearMap.range_zero]
    exact finrank_bot F _
  have hywz : Module.finrank F
      (LinearMap.range
        (0 : TotalEEEEYWZLeftZero n b c d →ₗ[F]
          Module.Dual F
            (DiamondEvenAxisValueTailZero n b
              (DiamondEvenAxisValueTailZero n c
                (DiamondEvenAxisValueTailZero n d (CyclicCube n)))))) = 0 := by
    rw [LinearMap.range_zero]
    exact finrank_bot F _
  unfold nestedDiamondCross
  simp only [finrank_range_diamondCrossProd]
  rw [hyw, hywz]

private theorem product_rank_addition_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2)) =
      (n - 1) * (3 * n ^ 2 - 4 * n + 6) +
      ((n ^ (b - 1) - 2) * (2 * n * (n - 1)) +
      ((n ^ (d - 1) - 2) * (2 * n * (n - 1)) +
      ((n ^ (c - 1) - 2) * ((n - 1) * (n ^ 2 + 3 * n)) +
      ((n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) *
          (n ^ 2 * (n - 1)) +
      ((n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
          (n ^ 2 * (n - 1)) + (0 + 0)))))) := by
  calc
    _ = Module.finrank F
        (LinearMap.range (nestedDiamondCross hn2 hn hb2 hc2 hd2)) :=
      congrArg (fun L => Module.finrank F (LinearMap.range L))
        (productCross_eq_nestedDiamondCross hn2 hn hb2 hc2 hd2)
    _ = _ := nestedDiamondCross_rank_components hn2 hn hb2 hc2 hd2
    _ = _ := by
      rw [Scalar.rank_localScalarCross hn2 hn hb2 hc2 hd2,
        rank_yTail hn2 hn hb2,
        rank_wTail hn2 hn hd2,
        PureZ.rank_tailCross hn2 hn hc2,
        rank_yzTail hn2 hn hb2 hc2,
        rank_wzTail hn2 hn hc2 hd2]

private theorem descended_rank_addition_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (k4BaseDescendedCross
            (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) * (3 * n ^ 2 - 4 * n + 6) +
      ((n ^ (b - 1) - 2) * (2 * n * (n - 1)) +
      ((n ^ (d - 1) - 2) * (2 * n * (n - 1)) +
      ((n ^ (c - 1) - 2) * ((n - 1) * (n ^ 2 + 3 * n)) +
      ((n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) *
          (n ^ 2 * (n - 1)) +
      ((n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
          (n ^ 2 * (n - 1)) + (0 + 0)))))) := by
  calc
    _ = Module.finrank F
        (LinearMap.range
          (k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2)) :=
      LinearEquiv.finrank_eq
        (k4BaseDescendedCross_eightSectorRangeEquiv
          hn2 hn hb2 hc2 hd2)
    _ = _ := product_rank_addition_first hn2 hn hb2 hc2 hd2

theorem finrank_range_k4BaseEightSectorProductCross_addition_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2)) =
      (n - 1) * (3 * n ^ 2 - 4 * n + 6) +
      ((n ^ (b - 1) - 2) * (2 * n * (n - 1)) +
      ((n ^ (d - 1) - 2) * (2 * n * (n - 1)) +
      ((n ^ (c - 1) - 2) * ((n - 1) * (n ^ 2 + 3 * n)) +
      ((n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) *
          (n ^ 2 * (n - 1)) +
      ((n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
          (n ^ 2 * (n - 1)) + (0 + 0)))))) :=
  product_rank_addition_first hn2 hn hb2 hc2 hd2

theorem finrank_range_k4BaseDescendedCross_addition_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (k4BaseDescendedCross
            (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) * (3 * n ^ 2 - 4 * n + 6) +
      ((n ^ (b - 1) - 2) * (2 * n * (n - 1)) +
      ((n ^ (d - 1) - 2) * (2 * n * (n - 1)) +
      ((n ^ (c - 1) - 2) * ((n - 1) * (n ^ 2 + 3 * n)) +
      ((n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) *
          (n ^ 2 * (n - 1)) +
      ((n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
          (n ^ 2 * (n - 1)) + (0 + 0)))))) :=
  descended_rank_addition_first hn2 hn hb2 hc2 hd2


end
end Core4loop.CompleteGraph.EvenP.BaseKKT
