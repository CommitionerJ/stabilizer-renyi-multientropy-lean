import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Factors.RowPrimitives

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.EEEEInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT
open Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

noncomputable section

noncomputable def baseBRow
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Profile n →ₗ[F] CyclicCube n :=
  (LinearMap.snd F _ _).comp
    ((LinearMap.snd F _ _).comp
      ((LinearMap.fst F _ _).comp
        ((scalarCoeffMap hn2 hn hb2 hc2 hd2).comp purePB)))

noncomputable def baseWRow
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Profile n →ₗ[F] CyclicCube n :=
  (LinearMap.fst F _ _).comp
    ((LinearMap.snd F _ _).comp
      ((LinearMap.snd F _ _).comp
        ((scalarCoeffMap hn2 hn hb2 hc2 hd2).comp purePW)))

noncomputable def linkedRow
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    LinkedSource n →ₗ[F] CyclicCube n :=
  (LinearMap.fst F _ _).comp
    ((LinearMap.snd F _ _).comp
      ((LinearMap.fst F _ _).comp
        ((scalarCoeffMap hn2 hn hb2 hc2 hd2).comp pureLinked)))

noncomputable def transportedBRow
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BFreeHeadRadical n →ₗ[F] CyclicCube n :=
  (LinearMap.snd F _ _).comp
    ((LinearMap.fst F _ _).comp
      ((LinearMap.fst F _ _).comp
        ((scalarCoeffMap hn2 hn hb2 hc2 hd2).comp pureBFree)))

noncomputable def transportedWRow
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4WFreeHeadRadical n →ₗ[F] CyclicCube n :=
  (LinearMap.fst F _ _).comp
    ((LinearMap.fst F _ _).comp
      ((LinearMap.snd F _ _).comp
        ((scalarCoeffMap hn2 hn hb2 hc2 hd2).comp pureWFree)))

noncomputable def starRow
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    (CyclicCube n × CyclicCube n) →ₗ[F] CyclicCube n :=
  (LinearMap.fst F _ _).comp
    ((LinearMap.fst F _ _).comp
      ((LinearMap.fst F _ _).comp
        ((scalarCoeffMap hn2 hn hb2 hc2 hd2).comp pureStar)))

theorem baseBRow_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (p : Profile n) :
    baseBRow hn2 hn hb2 hc2 hd2 p =
      (scalarCoeffMap hn2 hn hb2 hc2 hd2 (purePB p)).1.2.2 := rfl

theorem baseWRow_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (p : Profile n) :
    baseWRow hn2 hn hb2 hc2 hd2 p =
      (scalarCoeffMap hn2 hn hb2 hc2 hd2 (purePW p)).2.2.1 := rfl

theorem linkedRow_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : LinkedSource n) :
    linkedRow hn2 hn hb2 hc2 hd2 x =
      (scalarCoeffMap hn2 hn hb2 hc2 hd2 (pureLinked x)).1.2.1 := rfl

theorem transportedBRow_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BFreeHeadRadical n) :
    transportedBRow hn2 hn hb2 hc2 hd2 x =
      (scalarCoeffMap hn2 hn hb2 hc2 hd2 (pureBFree x)).1.1.2 := rfl

theorem transportedWRow_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4WFreeHeadRadical n) :
    transportedWRow hn2 hn hb2 hc2 hd2 x =
      (scalarCoeffMap hn2 hn hb2 hc2 hd2 (pureWFree x)).2.1.1 := rfl

theorem starRow_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : CyclicCube n × CyclicCube n) :
    starRow hn2 hn hb2 hc2 hd2 x =
      (scalarCoeffMap hn2 hn hb2 hc2 hd2 (pureStar x)).1.1.1 := rfl

theorem baseBRow_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (p : Profile n) :
    baseBRow hn2 hn hb2 hc2 hd2 p =
      cubeDiffI (k4PHeadScalarBuild p).1.1 := by
  rw [baseBRow_apply, row011_purePB_apply]

theorem baseWRow_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (p : Profile n) :
    baseWRow hn2 hn hb2 hc2 hd2 p =
      cubeDiffK (k4RHeadScalarBuild p).1.1 := by
  rw [baseWRow_apply, row110_purePW_apply]

theorem linkedRow_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : LinkedSource n) :
    linkedRow hn2 hn hb2 hc2 hd2 x =
      cubeDiffI x.1.1 + cubeDiffK x.1.2 := by
  rw [linkedRow_apply, row010_pureLinked_apply]

theorem transportedBRow_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BFreeHeadRadical n) :
    transportedBRow hn2 hn hb2 hc2 hd2 x =
      cubeDiffI x.1 +
        actualAddedBRead hn2 hn hb2 hc2 hd2 (pureBFree x) := by
  rw [transportedBRow_apply, row001_apply,
    ShallowProjectionProbe.scalarLeftCoordinate_B00,
    ShallowProjectionProbe.scalarLeftCoordinate_B10]
  change cubeDiffI (0 + x.1) +
    actualAddedBRead hn2 hn hb2 hc2 hd2 (pureBFree x) = _
  rw [zero_add]

theorem transportedWRow_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4WFreeHeadRadical n) :
    transportedWRow hn2 hn hb2 hc2 hd2 x =
      cubeDiffK x.1 +
        actualAddedWRead hn2 hn hb2 hc2 hd2 (pureWFree x) := by
  rw [transportedWRow_apply, row100_apply,
    ShallowProjectionProbe.scalarLeftCoordinate_Wsum]
  change cubeDiffK x.1 +
    actualAddedWRead hn2 hn hb2 hc2 hd2 (pureWFree x) = _
  rfl

theorem starRow_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : CyclicCube n × CyclicCube n) :
    starRow hn2 hn hb2 hc2 hd2 x =
      cubeDiffI x.1 + cubeDiffK x.2 := by
  rw [starRow_apply, row000_apply,
    ShallowProjectionProbe.scalarLeftCoordinate_B00,
    ShallowProjectionProbe.scalarLeftCoordinate_B10,
    ShallowProjectionProbe.scalarLeftCoordinate_Wsum,
    AllCoordinatesProbe.scalarLeftCoordinate_B01,
    AllCoordinatesProbe.scalarLeftCoordinate_B11,
    AllCoordinatesProbe.scalarLeftCoordinate_W10,
    AllCoordinatesProbe.scalarLeftCoordinate_W11]
  simp [pureStar, aggregateBuild]


end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.EEEEInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT
open Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

noncomputable section

private theorem add_pair_reassoc
    {V : Type*} [AddCommGroup V] (a b c d : V) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  ac_rfl

theorem row011_normal_form
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.2 =
      baseBRow hn2 hn hb2 hc2 hd2 s.2.1.1 := by
  change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.2 =
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 (purePB s.2.1.1)).1.2.2
  exact ShallowProjectionProbe.scalarCoeffMap_row011_depends_only_on_B_profile
    hn2 hn hb2 hc2 hd2 s

theorem row110_normal_form
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.2.1 =
      baseWRow hn2 hn hb2 hc2 hd2 s.2.2.2 := by
  change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.2.1 =
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 (purePW s.2.2.2)).2.2.1
  exact ShallowProjectionProbe.scalarCoeffMap_row110_depends_only_on_W_profile
    hn2 hn hb2 hc2 hd2 s

noncomputable def row010Canonical
    {n : Nat} [NeZero n]
    (s : K4BaseMixedScalarSector n) : CyclicCube n :=
  (cubeDiffI (k4PHeadScalarBuild s.2.1.1).1.1 +
      cubeDiffK (k4RHeadScalarBuild s.2.2.2).1.1) +
    (cubeDiffI (linkedRead s.1).1.1 +
      cubeDiffK (linkedRead s.1).1.2)

theorem row010_lhs_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.1 =
      row010Canonical s := by
  rw [row010Canonical]
  rw [row010_source_apply]
  rw [linkedRead_fst, linkedRead_snd]
  simp only [map_add]
  exact add_pair_reassoc _ _ _ _


theorem row010_rhs_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    baseBRow hn2 hn hb2 hc2 hd2 s.2.1.1 +
        baseWRow hn2 hn hb2 hc2 hd2 s.2.2.2 +
        linkedRow hn2 hn hb2 hc2 hd2 (linkedRead s.1) =
      row010Canonical s := by
  rw [row010Canonical]
  rw [baseBRow_normalized, baseWRow_normalized, linkedRow_normalized]

theorem row010_normal_form
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.1 =
      baseBRow hn2 hn hb2 hc2 hd2 s.2.1.1 +
        baseWRow hn2 hn hb2 hc2 hd2 s.2.2.2 +
        linkedRow hn2 hn hb2 hc2 hd2 (linkedRead s.1) := by
  exact (row010_lhs_normalized hn2 hn hb2 hc2 hd2 s).trans
    (row010_rhs_normalized hn2 hn hb2 hc2 hd2 s).symm

noncomputable def row001Canonical
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) : CyclicCube n :=
  cubeDiffI (k4PHeadScalarBuild s.2.1.1).1.1 +
    (cubeDiffI s.2.1.2.1 +
      actualAddedBRead hn2 hn hb2 hc2 hd2 (pureBFree s.2.1.2))

theorem row001_lhs_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.1.2 =
      row001Canonical hn2 hn hb2 hc2 hd2 s := by
  rw [row001Canonical, row001_apply,
    ShallowProjectionProbe.scalarLeftCoordinate_B00,
    ShallowProjectionProbe.scalarLeftCoordinate_B10]
  rw [map_add]
  nth_rewrite 1 [actualAddedBRead_depends_only_on_BFree
    hn2 hn hb2 hc2 hd2 s]
  rw [add_assoc]

theorem row001_rhs_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    baseBRow hn2 hn hb2 hc2 hd2 s.2.1.1 +
        transportedBRow hn2 hn hb2 hc2 hd2 s.2.1.2 =
      row001Canonical hn2 hn hb2 hc2 hd2 s := by
  rw [row001Canonical, baseBRow_normalized, transportedBRow_normalized]

theorem row001_normal_form
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.1.2 =
      baseBRow hn2 hn hb2 hc2 hd2 s.2.1.1 +
        transportedBRow hn2 hn hb2 hc2 hd2 s.2.1.2 :=
  (row001_lhs_normalized hn2 hn hb2 hc2 hd2 s).trans
    (row001_rhs_normalized hn2 hn hb2 hc2 hd2 s).symm

noncomputable def row100Canonical
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) : CyclicCube n :=
  cubeDiffK s.2.2.1.1 +
    actualAddedWRead hn2 hn hb2 hc2 hd2 (pureWFree s.2.2.1)

theorem row100_lhs_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.1.1 =
      row100Canonical hn2 hn hb2 hc2 hd2 s := by
  rw [row100Canonical, row100_apply,
    ShallowProjectionProbe.scalarLeftCoordinate_Wsum]
  nth_rewrite 1 [actualAddedWRead_depends_only_on_WFree
    hn2 hn hb2 hc2 hd2 s]
  rfl

theorem row100_rhs_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    transportedWRow hn2 hn hb2 hc2 hd2 s.2.2.1 =
      row100Canonical hn2 hn hb2 hc2 hd2 s := by
  rw [row100Canonical, transportedWRow_normalized]

theorem row100_normal_form
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.1.1 =
      transportedWRow hn2 hn hb2 hc2 hd2 s.2.2.1 :=
  (row100_lhs_normalized hn2 hn hb2 hc2 hd2 s).trans
    (row100_rhs_normalized hn2 hn hb2 hc2 hd2 s).symm


end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
