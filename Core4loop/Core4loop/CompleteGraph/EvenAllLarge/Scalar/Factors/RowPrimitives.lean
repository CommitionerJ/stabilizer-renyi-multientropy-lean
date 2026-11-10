import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Factors.Coordinates

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

noncomputable abbrev LinkedSource (n : Nat) [NeZero n] :=
  LinearMap.ker
    (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n)))

noncomputable def aggregateBuild
    {n : Nat} [NeZero n] :
    (LinkedSource n × (CyclicCube n × CyclicCube n)) →ₗ[F]
      K4AggregateEEEEScalarKernel n where
  toFun x :=
    ⟨⟨(((0, x.1.1.1), (0, x.2.1)),
        ((0, 0), (x.1.1.2, x.2.2))), by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · apply Prod.ext <;>
          simp only [diamondEEEELeftConstraintMap,
            LinearMap.coe_mk, AddHom.coe_mk, map_zero]
        all_goals simp
      · simpa only [diamondEEEELeftConstraintMap,
          LinearMap.coe_mk, AddHom.coe_mk,
          Prod.fst_zero, Prod.snd_zero, map_zero, zero_add]
          using LinearMap.mem_ker.mp x.1.2⟩, by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl
      · apply Prod.ext
        · rfl
        · apply Subtype.ext
          rfl⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def linkedRead
    {n : Nat} [NeZero n] :
    K4AggregateEEEEScalarKernel n →ₗ[F] LinkedSource n where
  toFun q :=
    ⟨(q.1.1.1.1.2, q.1.1.2.2.1), by
      apply LinearMap.mem_ker.mpr
      have h := congrArg (fun x => x.2)
        (LinearMap.mem_ker.mp q.1.2)
      simpa only [diamondEEEELeftConstraintMap,
        LinearMap.coe_mk, AddHom.coe_mk,
        Prod.fst_zero, Prod.snd_zero] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem linkedRead_fst
    {n : Nat} [NeZero n] (q : K4AggregateEEEEScalarKernel n) :
    (linkedRead q).1.1 = q.1.1.1.1.2 := rfl

theorem linkedRead_snd
    {n : Nat} [NeZero n] (q : K4AggregateEEEEScalarKernel n) :
    (linkedRead q).1.2 = q.1.1.2.2.1 := rfl

noncomputable def b11Read
    {n : Nat} [NeZero n] :
    K4AggregateEEEEScalarKernel n →ₗ[F] CyclicCube n where
  toFun q := q.1.1.1.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def w11Read
    {n : Nat} [NeZero n] :
    K4AggregateEEEEScalarKernel n →ₗ[F] CyclicCube n where
  toFun q := q.1.1.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def purePB
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] K4BaseMixedScalarSector n where
  toFun p := (0, ((p, 0), (0, 0)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def purePW
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] K4BaseMixedScalarSector n where
  toFun p := (0, ((0, 0), (0, p)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def pureLinked
    {n : Nat} [NeZero n] :
    LinkedSource n →ₗ[F] K4BaseMixedScalarSector n where
  toFun x := (aggregateBuild (x, (0, 0)), 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def pureBFree
    {n : Nat} [NeZero n] :
    K4BFreeHeadRadical n →ₗ[F] K4BaseMixedScalarSector n where
  toFun x := (0, ((0, x), (0, 0)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def pureWFree
    {n : Nat} [NeZero n] :
    K4WFreeHeadRadical n →ₗ[F] K4BaseMixedScalarSector n where
  toFun x := (0, ((0, 0), (x, 0)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def pureStar
    {n : Nat} [NeZero n] :
    (CyclicCube n × CyclicCube n) →ₗ[F]
      K4BaseMixedScalarSector n where
  toFun x := (aggregateBuild (0, x), 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def actualAddedOnly
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedScalarSector n →ₗ[F] DiamondEEEERightAmbient n :=
  scalarCoeffMap hn2 hn hb2 hc2 hd2 +
    diamondEEEECoeffMap.comp
      ((DiamondEEEELeftSource n).subtype.comp
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2))

noncomputable def actualAddedBRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedScalarSector n →ₗ[F] CyclicCube n where
  toFun s := (actualAddedOnly hn2 hn hb2 hc2 hd2 s).1.1.2
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

noncomputable def actualAddedWRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedScalarSector n →ₗ[F] CyclicCube n where
  toFun s := (actualAddedOnly hn2 hn hb2 hc2 hd2 s).2.1.1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private theorem f2_add_cancel_sandwich
    {V : Type*} [AddCommGroup V] [Module F V] (x y : V) :
    (x + y) + x = y := by
  calc
    (x + y) + x = y + (x + x) := by abel
    _ = y + 0 := by rw [EEEEInternal.module_add_self]
    _ = y := add_zero y

theorem actualAddedBRead_depends_only_on_BFree
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    actualAddedBRead hn2 hn hb2 hc2 hd2 s =
      actualAddedBRead hn2 hn hb2 hc2 hd2 (pureBFree s.2.1.2) := by
  simp only [actualAddedBRead, actualAddedOnly, scalarCoeffMap,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [f2_add_cancel_sandwich, f2_add_cancel_sandwich]
  rfl

theorem actualAddedWRead_depends_only_on_WFree
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    actualAddedWRead hn2 hn hb2 hc2 hd2 s =
      actualAddedWRead hn2 hn hb2 hc2 hd2 (pureWFree s.2.2.1) := by
  simp only [actualAddedWRead, actualAddedOnly, scalarCoeffMap,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [f2_add_cancel_sandwich, f2_add_cancel_sandwich]
  rfl

theorem row010_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.1 =
      cubeDiffI
          ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.2) +
        cubeDiffK
          ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.2.1) := by
  rw [scalarCoeffMap]
  change
    (cubeDiffI
          ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.2) +
        cubeDiffK
          ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.2.1)) + 0 = _
  simp

theorem row001_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.1.2 =
      cubeDiffI
          ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.2.1) +
        actualAddedBRead hn2 hn hb2 hc2 hd2 s := by
  simp [actualAddedBRead, actualAddedOnly, diamondEEEECoeffMap]
  abel_nf
  simp only [two_smul, EEEEInternal.module_add_self, zero_add]

theorem row100_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.1.1 =
      cubeDiffK
          ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.2) +
        actualAddedWRead hn2 hn hb2 hc2 hd2 s := by
  simp [actualAddedWRead, actualAddedOnly, diamondEEEECoeffMap]
  abel_nf
  simp only [two_smul, EEEEInternal.module_add_self, zero_add]

theorem row000_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.1.1 =
      cubeDiffI
          ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.2 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.2.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.2.2) +
        cubeDiffK
          ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.2 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.2.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.2.2) := by
  rw [scalarCoeffMap]
  change
    (cubeDiffI
          ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.2 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.2.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.2.2) +
        cubeDiffK
          ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.2 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.2.1 +
            (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.2.2)) + 0 = _
  simp

theorem row011_purePB_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (p : Profile n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 (purePB p)).1.2.2 =
      cubeDiffI (k4PHeadScalarBuild p).1.1 := by
  rw [ShallowProjectionProbe.scalarCoeffMap_row011,
    ShallowProjectionProbe.scalarLeftCoordinate_B00]
  rfl

theorem row110_purePW_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (p : Profile n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 (purePW p)).2.2.1 =
      cubeDiffK (k4RHeadScalarBuild p).1.1 := by
  rw [ShallowProjectionProbe.scalarCoeffMap_row110,
    ShallowProjectionProbe.scalarLeftCoordinate_W00]
  rfl

theorem row010_source_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.1 =
      cubeDiffI
          ((k4PHeadScalarBuild s.2.1.1).1.1 +
            s.1.1.1.1.1.2) +
        cubeDiffK
          ((k4RHeadScalarBuild s.2.2.2).1.1 +
            s.1.1.1.2.2.1) := by
  rw [row010_apply,
    ShallowProjectionProbe.scalarLeftCoordinate_B00,
    ShallowProjectionProbe.scalarLeftCoordinate_W00,
    AllCoordinatesProbe.scalarLeftCoordinate_B01,
    AllCoordinatesProbe.scalarLeftCoordinate_W10]

theorem row010_pureLinked_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : LinkedSource n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 (pureLinked x)).1.2.1 =
      cubeDiffI x.1.1 + cubeDiffK x.1.2 := by
  rw [row010_source_apply]
  simp [pureLinked, aggregateBuild]

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
