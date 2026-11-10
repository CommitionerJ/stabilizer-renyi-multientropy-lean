import Core4loop.CompleteGraph.EvenAllLarge.SectorAssembly.SourceDecompose

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
open Core4loop.SquareDiagonal.EvenP.TotalEEEERightInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

section PointwiseTransport

private local instance scalarKernelGroup
    {n : Nat} [NeZero n] :
    AddCommGroup (K4AggregateEEEEScalarKernel n) :=
  (K4AggregateEEEEScalarKernel n).addCommGroup

private local instance bFreeHeadGroup
    {n : Nat} [NeZero n] :
    AddCommGroup (K4BFreeHeadRadical n) :=
  (K4BFreeHeadRadical n).addCommGroup

private local instance wFreeHeadGroup
    {n : Nat} [NeZero n] :
    AddCommGroup (K4WFreeHeadRadical n) :=
  (K4WFreeHeadRadical n).addCommGroup

private local instance scalarSectorGroup
    {n : Nat} [NeZero n] :
    AddCommGroup (K4BaseMixedScalarSector n) :=
  inferInstance

private noncomputable abbrev SectorSource
    (n b c d : Nat) [NeZero n] :=
  K4BaseMixedOverlapSectorSource n b c d

private noncomputable abbrev SectorRight
    (n b c d : Nat) [NeZero n] :=
  TotalEEEERightReachableTarget n b c d

private noncomputable abbrev SectorReachable
    (n b c d : Nat) [NeZero n] :=
  DiamondEvenPReachableA n b c d

private theorem scalarProjection
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n b c d) :
    (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).1 =
      Scalar.rightRead hn hb2 hc2 hd2 A := by
  rfl

private theorem yProjection
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n b c d) :
    (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).2.1 =
      PassiveY.rightRead hn hb2 hc2 hd2 A := by
  rfl

private theorem wProjection
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n b c d) :
    (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).2.2.1 =
      PassiveW.rightRead hn hb2 hc2 hd2 A := by
  rfl

private theorem zProjection
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n b c d) :
    (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).2.2.2.1 =
      PureZ.rightRead hn hb2 hc2 hd2 A := by
  rfl

private theorem yzProjection
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n b c d) :
    (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).2.2.2.2.1 =
      PassiveYZ.rightRead hn hb2 hc2 hd2 A := by
  rfl

private theorem wzProjection
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n b c d) :
    (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).2.2.2.2.2.1 =
      PassiveWZ.rightRead hn hb2 hc2 hd2 A := by
  rfl

private noncomputable def rawWZTail
    {n b c d : Nat} [NeZero n]
    (s : SectorSource n b c d) (q : SectorRight n b c d) : F :=
  PassiveWZ.tailCross s.2.2.2.2.2.1 q.2.2.2.2.2.1 + (0 + 0)

private noncomputable def readWZTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  PassiveWZ.tailCross s.2.2.2.2.2.1
    (PassiveWZ.rightRead hn hb2 hc2 hd2 A) + (0 + 0)

private theorem rawWZTail_eq_readWZTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    rawWZTail s (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      readWZTail hn hb2 hc2 hd2 s A := by
  unfold rawWZTail readWZTail
  exact congrArg₂ (fun x y : F => x + y)
    (congrArg (fun x => PassiveWZ.tailCross s.2.2.2.2.2.1 x)
      (wzProjection hn hb2 hc2 hd2 A)) rfl

private noncomputable def rawYZTail
    {n b c d : Nat} [NeZero n]
    (s : SectorSource n b c d) (q : SectorRight n b c d) : F :=
  PassiveYZ.tailCross s.2.2.2.2.1 q.2.2.2.2.1 + rawWZTail s q

private noncomputable def readYZTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  PassiveYZ.tailCross s.2.2.2.2.1
      (PassiveYZ.rightRead hn hb2 hc2 hd2 A) +
    readWZTail hn hb2 hc2 hd2 s A

private theorem rawYZTail_eq_readYZTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    rawYZTail s (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      readYZTail hn hb2 hc2 hd2 s A := by
  unfold rawYZTail readYZTail
  exact congrArg₂ (fun x y : F => x + y)
    (congrArg (fun x => PassiveYZ.tailCross s.2.2.2.2.1 x)
      (yzProjection hn hb2 hc2 hd2 A))
    (rawWZTail_eq_readWZTail hn hb2 hc2 hd2 s A)

private noncomputable def rawZTail
    {n b c d : Nat} [NeZero n]
    (s : SectorSource n b c d) (q : SectorRight n b c d) : F :=
  PureZ.tailCross s.2.2.2.1 q.2.2.2.1 + rawYZTail s q

private noncomputable def readZTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  PureZ.tailCross s.2.2.2.1 (PureZ.rightRead hn hb2 hc2 hd2 A) +
    readYZTail hn hb2 hc2 hd2 s A

private theorem rawZTail_eq_readZTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    rawZTail s (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      readZTail hn hb2 hc2 hd2 s A := by
  unfold rawZTail readZTail
  exact congrArg₂ (fun x y : F => x + y)
    (congrArg (fun x => PureZ.tailCross s.2.2.2.1 x)
      (zProjection hn hb2 hc2 hd2 A))
    (rawYZTail_eq_readYZTail hn hb2 hc2 hd2 s A)

private noncomputable def rawWTail
    {n b c d : Nat} [NeZero n]
    (s : SectorSource n b c d) (q : SectorRight n b c d) : F :=
  PassiveW.tailCross s.2.2.1 q.2.2.1 + rawZTail s q

private noncomputable def readWTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  PassiveW.tailCross s.2.2.1 (PassiveW.rightRead hn hb2 hc2 hd2 A) +
    readZTail hn hb2 hc2 hd2 s A

private theorem rawWTail_eq_readWTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    rawWTail s (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      readWTail hn hb2 hc2 hd2 s A := by
  unfold rawWTail readWTail
  exact congrArg₂ (fun x y : F => x + y)
    (congrArg (fun x => PassiveW.tailCross s.2.2.1 x)
      (wProjection hn hb2 hc2 hd2 A))
    (rawZTail_eq_readZTail hn hb2 hc2 hd2 s A)

private noncomputable def rawYTail
    {n b c d : Nat} [NeZero n]
    (s : SectorSource n b c d) (q : SectorRight n b c d) : F :=
  PassiveY.tailCross s.2.1 q.2.1 + rawWTail s q

private noncomputable def readYTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  PassiveY.tailCross s.2.1 (PassiveY.rightRead hn hb2 hc2 hd2 A) +
    readWTail hn hb2 hc2 hd2 s A

private theorem rawYTail_eq_readYTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    rawYTail s (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      readYTail hn hb2 hc2 hd2 s A := by
  unfold rawYTail readYTail
  exact congrArg₂ (fun x y : F => x + y)
    (congrArg (fun x => PassiveY.tailCross s.2.1 x)
      (yProjection hn hb2 hc2 hd2 A))
    (rawWTail_eq_readWTail hn hb2 hc2 hd2 s A)

private noncomputable def rawRows
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (q : SectorRight n b c d) : F :=
  Scalar.localScalarCross hn2 hn hb2 hc2 hd2 s.1 q.1 + rawYTail s q

private noncomputable def readRows
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  Scalar.localScalarCross hn2 hn hb2 hc2 hd2 s.1
      (Scalar.rightRead hn hb2 hc2 hd2 A) +
    readYTail hn hb2 hc2 hd2 s A

private theorem rawRows_eq_readRows
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    rawRows hn2 hn hb2 hc2 hd2 s
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      readRows hn2 hn hb2 hc2 hd2 s A := by
  unfold rawRows readRows
  exact congrArg₂ (fun x y : F => x + y)
    (congrArg
      (fun x => Scalar.localScalarCross hn2 hn hb2 hc2 hd2 s.1 x)
      (scalarProjection hn hb2 hc2 hd2 A))
    (rawYTail_eq_readYTail hn hb2 hc2 hd2 s A)

private theorem readZeroTail_eq_descendedZeroTail :
    (0 : F) + 0 = 0 := by
  simp

private noncomputable def descendedWZTail
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  PassiveWZ.descendedCross hn2 hn hb2 hc2 hd2
      s.2.2.2.2.2.1 A + 0

private theorem readWZTail_eq_descendedWZTail
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    readWZTail hn hb2 hc2 hd2 s A =
      descendedWZTail hn2 hn hb2 hc2 hd2 s A := by
  unfold readWZTail descendedWZTail
  exact congrArg₂ (fun x y : F => x + y)
    (PassiveWZ.descendedCross_apply hn2 hn hb2 hc2 hd2
      s.2.2.2.2.2.1 A).symm
    readZeroTail_eq_descendedZeroTail

private noncomputable def descendedYZTail
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  PassiveYZ.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.2.2.1 A +
    descendedWZTail hn2 hn hb2 hc2 hd2 s A

private theorem readYZTail_eq_descendedYZTail
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    readYZTail hn hb2 hc2 hd2 s A =
      descendedYZTail hn2 hn hb2 hc2 hd2 s A := by
  unfold readYZTail descendedYZTail
  exact congrArg₂ (fun x y : F => x + y)
    (PassiveYZ.descendedCross_apply hn2 hn hb2 hc2 hd2
      s.2.2.2.2.1 A).symm
    (readWZTail_eq_descendedWZTail hn2 hn hb2 hc2 hd2 s A)

private noncomputable def descendedZTail
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  PureZ.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.2.1 A +
    descendedYZTail hn2 hn hb2 hc2 hd2 s A

private theorem readZTail_eq_descendedZTail
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    readZTail hn hb2 hc2 hd2 s A =
      descendedZTail hn2 hn hb2 hc2 hd2 s A := by
  unfold readZTail descendedZTail
  exact congrArg₂ (fun x y : F => x + y)
    (LinearMap.congr_fun
      (LinearMap.congr_fun
        (PureZ.descendedCross_eq_rightRead_dual_tailCross
          hn2 hn hb2 hc2 hd2) s.2.2.2.1) A).symm
    (readYZTail_eq_descendedYZTail hn2 hn hb2 hc2 hd2 s A)

private noncomputable def descendedWTail
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  PassiveW.descendedCross hn2 hn hb2 hc2 hd2 s.2.2.1 A +
    descendedZTail hn2 hn hb2 hc2 hd2 s A

private theorem readWTail_eq_descendedWTail
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    readWTail hn hb2 hc2 hd2 s A =
      descendedWTail hn2 hn hb2 hc2 hd2 s A := by
  unfold readWTail descendedWTail
  exact congrArg₂ (fun x y : F => x + y)
    (PassiveW.descendedCross_apply
      hn2 hn hb2 hc2 hd2 s.2.2.1 A).symm
    (readZTail_eq_descendedZTail hn2 hn hb2 hc2 hd2 s A)

private noncomputable def descendedYTail
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  PassiveY.descendedCross hn2 hn hb2 hc2 hd2 s.2.1 A +
    descendedWTail hn2 hn hb2 hc2 hd2 s A

private theorem readYTail_eq_descendedYTail
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    readYTail hn hb2 hc2 hd2 s A =
      descendedYTail hn2 hn hb2 hc2 hd2 s A := by
  unfold readYTail descendedYTail
  exact congrArg₂ (fun x y : F => x + y)
    (PassiveY.descendedCross_apply
      hn2 hn hb2 hc2 hd2 s.2.1 A).symm
    (readWTail_eq_descendedWTail hn2 hn hb2 hc2 hd2 s A)

private theorem scalarRead_eq_descended
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    Scalar.localScalarCross hn2 hn hb2 hc2 hd2 s.1
        (Scalar.rightRead hn hb2 hc2 hd2 A) =
      Scalar.descendedCross hn2 hn hb2 hc2 hd2 s.1 A := by
  rw [Scalar.localScalarCross_apply]
  exact (Scalar.scalarPhaseFullSupport hn2 hn hb2 hc2 hd2 s.1 A).symm

private noncomputable def descendedRows
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) : F :=
  Scalar.descendedCross hn2 hn hb2 hc2 hd2 s.1 A +
    descendedYTail hn2 hn hb2 hc2 hd2 s A

private theorem readRows_eq_descendedRows
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    readRows hn2 hn hb2 hc2 hd2 s A =
      descendedRows hn2 hn hb2 hc2 hd2 s A := by
  unfold readRows descendedRows
  rw [scalarRead_eq_descended hn2 hn hb2 hc2 hd2 s A,
    readYTail_eq_descendedYTail hn2 hn hb2 hc2 hd2 s A]

private theorem k4BaseEightSectorProductCross_eq_rawRows
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (q : SectorRight n b c d) :
    k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2 s q =
      rawRows hn2 hn hb2 hc2 hd2 s q := by
  rw [k4BaseEightSectorProductCross_apply]
  rfl

private theorem descendedRows_eq_k4BaseSectorDescendedCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d) (A : SectorReachable n b c d) :
    descendedRows hn2 hn hb2 hc2 hd2 s A =
      k4BaseSectorDescendedCross hn2 hn hb2 hc2 hd2 s A := by
  rw [k4BaseSectorDescendedCross_decompose]
  rfl

theorem k4BaseEightSectorProductCross_right_transport
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d)
    (A : SectorReachable n b c d) :
    k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2 s
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      k4BaseSectorDescendedCross hn2 hn hb2 hc2 hd2 s A := by
  calc
    k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2 s
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      rawRows hn2 hn hb2 hc2 hd2 s
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) :=
      k4BaseEightSectorProductCross_eq_rawRows hn2 hn hb2 hc2 hd2 s _
    _ = readRows hn2 hn hb2 hc2 hd2 s A :=
      rawRows_eq_readRows hn2 hn hb2 hc2 hd2 s A
    _ = descendedRows hn2 hn hb2 hc2 hd2 s A :=
      readRows_eq_descendedRows hn2 hn hb2 hc2 hd2 s A
    _ = k4BaseSectorDescendedCross hn2 hn hb2 hc2 hd2 s A :=
      descendedRows_eq_k4BaseSectorDescendedCross
        hn2 hn hb2 hc2 hd2 s A

private theorem sectorBuild_sectorEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4GPolarKernel n b c d) :
    k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2
        (k4GPolarKernelMixedOverlapSectorEquiv
          hn2 hn hb2 hc2 hd2 sigma) =
      k4GPolarKernelMixedOverlapRead hn2 hn hb2 hc2 hd2 sigma := by
  rw [k4GPolarKernelMixedOverlapSectorEquiv_intertwines]
  exact k4BaseMixedOverlapSectorBuild_read hn hb2 hc2 hd2 _

private theorem mixedBuild_sectorEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4GPolarKernel n b c d) :
    k4GPolarKernelMixedOverlapBuild hn2 hn hb2 hc2 hd2
        (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2
          (k4GPolarKernelMixedOverlapSectorEquiv
            hn2 hn hb2 hc2 hd2 sigma)) = sigma := by
  rw [sectorBuild_sectorEquiv hn2 hn hb2 hc2 hd2 sigma]
  exact k4GPolarKernelMixedOverlapBuild_read hn2 hn hb2 hc2 hd2 sigma

private theorem k4BaseSectorDescendedCross_sectorEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4GPolarKernel n b c d)
    (A : SectorReachable n b c d) :
    k4BaseSectorDescendedCross hn2 hn hb2 hc2 hd2
        (k4GPolarKernelMixedOverlapSectorEquiv
          hn2 hn hb2 hc2 hd2 sigma) A =
      k4BaseDescendedCross sigma A := by
  simp only [k4BaseSectorDescendedCross, LinearMap.comp_apply]
  simp only [k4BaseDescendedMixedOverlapCross, LinearMap.comp_apply]
  rw [mixedBuild_sectorEquiv hn2 hn hb2 hc2 hd2 sigma]

theorem k4BaseEightSectorProductCross_full_transport
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4GPolarKernel n b c d)
    (A : SectorReachable n b c d) :
    k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2
        (k4GPolarKernelMixedOverlapSectorEquiv
          hn2 hn hb2 hc2 hd2 sigma)
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      k4BaseDescendedCross sigma A := by
  rw [k4BaseEightSectorProductCross_right_transport]
  exact k4BaseSectorDescendedCross_sectorEquiv
    hn2 hn hb2 hc2 hd2 sigma A

end PointwiseTransport

section RangeTransport

variable {R R' : Type}
variable [AddCommMonoid R] [Module F R]
variable [AddCommMonoid R'] [Module F R']

private noncomputable def dualTransportMonoid
    (eR : R ≃ₗ[F] R') :
    Module.Dual F R ≃ₗ[F] Module.Dual F R' where
  toFun phi := phi.comp eR.symm.toLinearMap
  invFun phi := phi.comp eR.toLinearMap
  left_inv phi := by
    apply LinearMap.ext
    intro r
    simp
  right_inv phi := by
    apply LinearMap.ext
    intro r
    simp
  map_add' phi psi := by
    apply LinearMap.ext
    intro r
    rfl
  map_smul' s phi := by
    apply LinearMap.ext
    intro r
    rfl

end RangeTransport

private noncomputable def concreteRightDualTransport
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.Dual F (DiamondEvenPReachableA n b c d) ≃ₗ[F]
      Module.Dual F (TotalEEEERightReachableTarget n b c d) :=
  dualTransportMonoid
    (R := DiamondEvenPReachableA n b c d)
    (R' := TotalEEEERightReachableTarget n b c d)
    (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2)

private theorem concreteCrossComm
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4GPolarKernel n b c d) :
    k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2
        (k4GPolarKernelMixedOverlapSectorEquiv
          hn2 hn hb2 hc2 hd2 sigma) =
      concreteRightDualTransport hn hb2 hc2 hd2
        (k4BaseDescendedCross sigma) := by
  apply LinearMap.ext
  intro q
  let A := (diamondEvenPReachableAEEEEEquiv
    hn hb2 hc2 hd2).symm q
  have h := k4BaseEightSectorProductCross_full_transport
    hn2 hn hb2 hc2 hd2 sigma A
  simpa [concreteRightDualTransport, dualTransportMonoid, A] using h

private theorem concreteRangeForward_mem
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (y : LinearMap.range (k4BaseDescendedCross
      (n := n) (b := b) (c := c) (d := d))) :
    concreteRightDualTransport hn hb2 hc2 hd2 y.1 ∈
      LinearMap.range
        (k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2) := by
  rcases y with ⟨_, ⟨sigma, rfl⟩⟩
  exact ⟨k4GPolarKernelMixedOverlapSectorEquiv
    hn2 hn hb2 hc2 hd2 sigma,
    concreteCrossComm hn2 hn hb2 hc2 hd2 sigma⟩

private noncomputable def concreteRangeForwardFun
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (y : LinearMap.range (k4BaseDescendedCross
      (n := n) (b := b) (c := c) (d := d))) :
    LinearMap.range
        (k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2) :=
  ⟨concreteRightDualTransport hn hb2 hc2 hd2 y.1,
    concreteRangeForward_mem hn2 hn hb2 hc2 hd2 y⟩

private theorem concreteRangeForwardFun_add
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (y z : LinearMap.range (k4BaseDescendedCross
      (n := n) (b := b) (c := c) (d := d))) :
    concreteRangeForwardFun hn2 hn hb2 hc2 hd2 (y + z) =
      concreteRangeForwardFun hn2 hn hb2 hc2 hd2 y +
        concreteRangeForwardFun hn2 hn hb2 hc2 hd2 z := by
  apply Subtype.ext
  exact map_add (concreteRightDualTransport hn hb2 hc2 hd2) y.1 z.1

private theorem concreteRangeForwardFun_smul
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : F)
    (y : LinearMap.range (k4BaseDescendedCross
      (n := n) (b := b) (c := c) (d := d))) :
    concreteRangeForwardFun hn2 hn hb2 hc2 hd2 (s • y) =
      s • concreteRangeForwardFun hn2 hn hb2 hc2 hd2 y := by
  apply Subtype.ext
  exact map_smul (concreteRightDualTransport hn hb2 hc2 hd2) s y.1

private noncomputable def concreteRangeForward
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    LinearMap.range (k4BaseDescendedCross
      (n := n) (b := b) (c := c) (d := d)) →ₗ[F]
      LinearMap.range
        (k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2) where
  toFun := concreteRangeForwardFun hn2 hn hb2 hc2 hd2
  map_add' := concreteRangeForwardFun_add hn2 hn hb2 hc2 hd2
  map_smul' := concreteRangeForwardFun_smul hn2 hn hb2 hc2 hd2

private theorem concreteRangeBackward_mem
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (y : LinearMap.range
      (k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2)) :
    (concreteRightDualTransport hn hb2 hc2 hd2).symm y.1 ∈
      LinearMap.range (k4BaseDescendedCross
        (n := n) (b := b) (c := c) (d := d)) := by
  rcases y with ⟨_, ⟨s, rfl⟩⟩
  let sigma := (k4GPolarKernelMixedOverlapSectorEquiv
    hn2 hn hb2 hc2 hd2).symm s
  refine ⟨sigma, ?_⟩
  apply (concreteRightDualTransport hn hb2 hc2 hd2).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (concreteCrossComm hn2 hn hb2 hc2 hd2 sigma).symm.trans
    (congrArg (k4BaseEightSectorProductCross
      hn2 hn hb2 hc2 hd2)
      ((k4GPolarKernelMixedOverlapSectorEquiv
        hn2 hn hb2 hc2 hd2).apply_symm_apply s))

private noncomputable def concreteRangeBackwardFun
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (y : LinearMap.range
      (k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2)) :
    LinearMap.range (k4BaseDescendedCross
      (n := n) (b := b) (c := c) (d := d)) :=
  ⟨(concreteRightDualTransport hn hb2 hc2 hd2).symm y.1,
    concreteRangeBackward_mem hn2 hn hb2 hc2 hd2 y⟩

private theorem concreteRangeForward_injective
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Function.Injective (concreteRangeForward hn2 hn hb2 hc2 hd2) := by
  intro y z hyz
  apply Subtype.ext
  apply (concreteRightDualTransport hn hb2 hc2 hd2).injective
  exact congrArg Subtype.val hyz

private theorem concreteRangeForward_surjective
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Function.Surjective (concreteRangeForward hn2 hn hb2 hc2 hd2) := by
  intro y
  refine ⟨concreteRangeBackwardFun hn2 hn hb2 hc2 hd2 y, ?_⟩
  apply Subtype.ext
  exact (concreteRightDualTransport
    hn hb2 hc2 hd2).apply_symm_apply y.1

noncomputable def k4BaseDescendedCross_eightSectorRangeEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    LinearMap.range (k4BaseDescendedCross
      (n := n) (b := b) (c := c) (d := d)) ≃ₗ[F]
      LinearMap.range
        (k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2) :=
  LinearEquiv.ofBijective
    (concreteRangeForward hn2 hn hb2 hc2 hd2)
    ⟨concreteRangeForward_injective hn2 hn hb2 hc2 hd2,
      concreteRangeForward_surjective hn2 hn hb2 hc2 hd2⟩

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.SectorAssembly
