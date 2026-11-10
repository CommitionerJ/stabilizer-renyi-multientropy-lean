import Core4loop.CompleteGraph.EvenAllLarge.AggregateEEEETransport

/-! Explicit eight-sector coordinates for the kernel of the K4 aggregate map. -/

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.CompleteGraph.EvenP

noncomputable section

/- The nested eight-sector products make instance synthesis and the final
   product extensionality proofs substantially deeper than Lean's defaults. -/
set_option linter.style.setOption false in
section

set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-! Exact scalar and Z reads. -/

noncomputable def k4AggregateEEEEScalarHeadRead
    {n : Nat} [NeZero n] :
    DiamondEEEELeftSource n →ₗ[F]
      (((LinearMap.ker (cubeDiffP (n := n))) × CyclicCube n) ×
        (CyclicCube n × LinearMap.ker (cubeDiffR (n := n)))) where
  toFun q :=
    ((⟨q.1.1.1.1, by
        apply LinearMap.mem_ker.mpr
        have h := congrArg (fun x => x.1.1) (LinearMap.mem_ker.mp q.2)
        change cubeDiffP q.1.1.1.1 = 0 at h
        exact h⟩,
      q.1.1.2.1),
      (q.1.2.1.1 + q.1.2.1.2,
        ⟨q.1.2.1.1, by
          apply LinearMap.mem_ker.mpr
          have h := congrArg (fun x => x.1.2) (LinearMap.mem_ker.mp q.2)
          change cubeDiffR q.1.2.1.1 = 0 at h
          exact h⟩))
  map_add' q q' := by
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl
    · apply Prod.ext
      · change
          (q.1.2.1.1 + q'.1.2.1.1) +
              (q.1.2.1.2 + q'.1.2.1.2) =
            (q.1.2.1.1 + q.1.2.1.2) +
              (q'.1.2.1.1 + q'.1.2.1.2)
        abel
      · apply Subtype.ext
        rfl
  map_smul' r q := by
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl
    · apply Prod.ext
      · simp [smul_add]
      · apply Subtype.ext
        rfl

noncomputable abbrev K4AggregateEEEEScalarKernel
    (n : Nat) [NeZero n] :=
  LinearMap.ker (k4AggregateEEEEScalarHeadRead (n := n))

noncomputable def k4AggregateEEEEZSigmaRead
    {n : Nat} [NeZero n] :
    DiamondEEOELeftAmbient n →ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toFun q := (q.1.1, q.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable abbrev K4AggregateEEEEZKernel
    (n : Nat) [NeZero n] :=
  LinearMap.ker (k4AggregateEEEEZSigmaRead (n := n))

noncomputable abbrev K4AggregateEEEEZKernelTail
    (n c : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n c (K4AggregateEEEEZKernel n)

/-! Frozen eight-sector association. -/

noncomputable abbrev K4AggregateKernelEEEESource
    (n b c d : Nat) [NeZero n] :=
  K4AggregateEEEEScalarKernel n ×
    (TotalEEEEYTailLeft n b ×
      (TotalEEEEWTailLeft n d ×
        (K4AggregateEEEEZKernelTail n c ×
          (TotalEEEEYZTailLeft n b c ×
            (TotalEEEEWZTailLeft n c d ×
              (TotalEEEEYWLeftZero n b d ×
                TotalEEEEYWZLeftZero n b c d))))))

private theorem k4AggregateZKernelTail_forget_mem
    {n c : Nat} [NeZero n]
    (z : K4AggregateEEEEZKernelTail n c) :
    (fun t => (z.1 t).1) ∈ TotalEEEEZTailLeft n c := by
  apply LinearMap.mem_ker.mpr
  have h := pointedValueTailZero_sum z
  simpa only [Submodule.coe_sum, Submodule.coe_zero] using
    congrArg Subtype.val h

noncomputable def k4AggregateKernelEEEESourceEmbed
    {n b c d : Nat} [NeZero n] :
    K4AggregateKernelEEEESource n b c d →ₗ[F]
      SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d where
  toFun x :=
    (x.1.1,
      (x.2.1,
        (x.2.2.1,
          (⟨(fun t => (x.2.2.2.1.1 t).1),
              k4AggregateZKernelTail_forget_mem x.2.2.2.1⟩,
            (x.2.2.2.2.1,
              (x.2.2.2.2.2.1,
                (x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem k4AggregateKernelEEEESourceEmbed_injective
    {n b c d : Nat} [NeZero n] :
    Function.Injective
      (k4AggregateKernelEEEESourceEmbed
        (n := n) (b := b) (c := c) (d := d)) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun q => q.1) h
  · apply Prod.ext
    · exact congrArg (fun q => q.2.1) h
    · apply Prod.ext
      · exact congrArg (fun q => q.2.2.1) h
      · apply Prod.ext
        · apply Subtype.ext
          funext t
          apply Subtype.ext
          exact congrArg (fun q => q.2.2.2.1.1 t) h
        · apply Prod.ext
          · exact congrArg (fun q => q.2.2.2.2.1) h
          · apply Prod.ext
            · exact congrArg (fun q => q.2.2.2.2.2.1) h
            · apply Prod.ext
              · exact congrArg (fun q => q.2.2.2.2.2.2.1) h
              · exact congrArg (fun q => q.2.2.2.2.2.2.2) h

/-! The kernel of the actual AGG-EEEE read. -/

private noncomputable abbrev k4AggregateEEEEKernelInternal
    (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (k4AggregateEEEERead (n := n) (b := b) (c := c) (d := d))

private theorem scalar_mem_of_read_kernel
    {n b c d : Nat} [NeZero n]
    (q : k4AggregateEEEEKernelInternal n b c d) :
    q.1.1 ∈ K4AggregateEEEEScalarKernel n := by
  apply LinearMap.mem_ker.mpr
  have h := LinearMap.mem_ker.mp q.2
  have hs := congrArg (fun z => (z.1.1, z.2.1)) h
  simpa only [k4AggregateEEEEScalarHeadRead,
    k4AggregateEEEERead, LinearMap.coe_mk, AddHom.coe_mk,
    Prod.fst_zero, Prod.snd_zero] using hs

private theorem zsigma_mem_of_read_kernel
    {n b c d : Nat} [NeZero n]
    (q : k4AggregateEEEEKernelInternal n b c d)
    (t : PointedTail (PVec n c) zeroVec) :
    q.1.2.2.2.1.1 t ∈ K4AggregateEEEEZKernel n := by
  apply LinearMap.mem_ker.mpr
  have h := LinearMap.mem_ker.mp q.2
  have hz := congrArg (fun z => (z.1.2.1 t, z.2.2.1 t)) h
  simpa only [k4AggregateEEEEZSigmaRead,
    k4AggregateEEEERead, LinearMap.coe_mk, AddHom.coe_mk,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
    Submodule.coe_zero] using hz

private theorem zkernel_tail_mem_of_read_kernel
    {n b c d : Nat} [NeZero n]
    (q : k4AggregateEEEEKernelInternal n b c d) :
    (fun t =>
      ⟨q.1.2.2.2.1.1 t, zsigma_mem_of_read_kernel q t⟩) ∈
      K4AggregateEEEEZKernelTail n c := by
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  have h := LinearMap.mem_ker.mp q.1.2.2.2.1.2
  simpa only [fintypeSumLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_zero] using h

private noncomputable def k4AggregateEEEEKernelReadInternal
    {n b c d : Nat} [NeZero n] :
    k4AggregateEEEEKernelInternal n b c d →ₗ[F]
      K4AggregateKernelEEEESource n b c d where
  toFun q :=
    (⟨q.1.1, scalar_mem_of_read_kernel q⟩,
      (q.1.2.1,
        (q.1.2.2.1,
          (⟨(fun t =>
              ⟨q.1.2.2.2.1.1 t, zsigma_mem_of_read_kernel q t⟩),
              zkernel_tail_mem_of_read_kernel q⟩,
            (q.1.2.2.2.2.1,
              (q.1.2.2.2.2.2.1,
                (q.1.2.2.2.2.2.2.1,
                  q.1.2.2.2.2.2.2.2)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem source_embed_mem_read_kernel
    {n b c d : Nat} [NeZero n]
    (x : K4AggregateKernelEEEESource n b c d) :
    k4AggregateKernelEEEESourceEmbed
        (n := n) (b := b) (c := c) (d := d) x ∈
      k4AggregateEEEEKernelInternal n b c d := by
  apply LinearMap.mem_ker.mpr
  dsimp only [k4AggregateKernelEEEESourceEmbed,
    k4AggregateEEEERead]
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · simpa only [k4AggregateKernelEEEESourceEmbed,
          k4AggregateEEEERead, LinearMap.coe_mk, AddHom.coe_mk] using
          congrArg (fun z => z.1.1) (LinearMap.mem_ker.mp x.1.2)
      · change x.1.1.1.1.2.1 = 0
        exact congrArg (fun z => z.1.2) (LinearMap.mem_ker.mp x.1.2)
    · apply Subtype.ext
      funext t
      change (x.2.2.2.1.1 t).1.1.1 = 0
      exact congrArg Prod.fst (LinearMap.mem_ker.mp (x.2.2.2.1.1 t).2)
  · apply Prod.ext
    · apply Prod.ext
      · change x.1.1.1.2.1.1 + x.1.1.1.2.1.2 = 0
        exact congrArg (fun z => z.2.1) (LinearMap.mem_ker.mp x.1.2)
      · simpa only [k4AggregateKernelEEEESourceEmbed,
          k4AggregateEEEERead, LinearMap.coe_mk, AddHom.coe_mk] using
          congrArg (fun z => z.2.2) (LinearMap.mem_ker.mp x.1.2)
    · apply Subtype.ext
      funext t
      change (x.2.2.2.1.1 t).1.2.1 = 0
      exact congrArg Prod.snd (LinearMap.mem_ker.mp (x.2.2.2.1.1 t).2)

private noncomputable def k4AggregateEEEEKernelBuildInternal
    {n b c d : Nat} [NeZero n] :
    K4AggregateKernelEEEESource n b c d →ₗ[F]
      k4AggregateEEEEKernelInternal n b c d where
  toFun x :=
    ⟨k4AggregateKernelEEEESourceEmbed
        (n := n) (b := b) (c := c) (d := d) x,
      source_embed_mem_read_kernel x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] private theorem k4AggregateEEEEKernelReadInternal_build
    {n b c d : Nat} [NeZero n]
    (x : K4AggregateKernelEEEESource n b c d) :
    k4AggregateEEEEKernelReadInternal (n := n) (b := b) (c := c) (d := d)
        (k4AggregateEEEEKernelBuildInternal
          (n := n) (b := b) (c := c) (d := d) x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · apply Subtype.ext
          funext t
          apply Subtype.ext
          rfl
        · rfl

@[simp] private theorem k4AggregateEEEEKernelBuildInternal_read
    {n b c d : Nat} [NeZero n]
    (q : k4AggregateEEEEKernelInternal n b c d) :
    k4AggregateEEEEKernelBuildInternal (n := n) (b := b) (c := c) (d := d)
        (k4AggregateEEEEKernelReadInternal
          (n := n) (b := b) (c := c) (d := d) q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl

private noncomputable def k4AggregateEEEEKernelEquivInternal
    {n b c d : Nat} [NeZero n] :
    k4AggregateEEEEKernelInternal n b c d ≃ₗ[F]
      K4AggregateKernelEEEESource n b c d where
  toLinearMap := k4AggregateEEEEKernelReadInternal
    (n := n) (b := b) (c := c) (d := d)
  invFun := k4AggregateEEEEKernelBuildInternal
    (n := n) (b := b) (c := c) (d := d)
  left_inv := k4AggregateEEEEKernelBuildInternal_read
    (n := n) (b := b) (c := c) (d := d)
  right_inv := k4AggregateEEEEKernelReadInternal_build
    (n := n) (b := b) (c := c) (d := d)

/-! AGG-EEEE identifies the aggregate kernel with the read kernel. -/

private theorem eeee_mem_of_aggregate_kernel
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4AggregateKernel n b c d hn hb2 hc2 hd2) :
    diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma.1 ∈
      k4AggregateEEEEKernelInternal n b c d := by
  apply LinearMap.mem_ker.mpr
  rw [k4AggregateEEEERead_intertwines]
  have h := LinearMap.mem_ker.mp sigma.2
  rw [h]
  simp

private theorem aggregate_mem_of_eeee_kernel
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : k4AggregateEEEEKernelInternal n b c d) :
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).symm q.1 ∈
      K4AggregateKernel n b c d hn hb2 hc2 hd2 := by
  apply LinearMap.mem_ker.mpr
  let sigma := (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).symm q.1
  have hcoord :
      ((k4BAggregateCoordEquiv hn hc2)
          (k4EvenPAggregate hn hb2 (by omega) hd2 sigma).1,
        (k4WAggregateCoordEquiv hn hc2)
          (k4EvenPAggregate hn hb2 (by omega) hd2 sigma).2) = 0 := by
    calc
      _ = k4AggregateEEEERead
          (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma) :=
        (k4AggregateEEEERead_intertwines
          hn hb2 hc2 hd2 sigma).symm
      _ = k4AggregateEEEERead q.1 := by
        rw [(diamondEvenPLeftEEEEEquiv
          hn hb2 hc2 hd2).apply_symm_apply]
      _ = 0 := LinearMap.mem_ker.mp q.2
  apply Prod.ext
  · apply (k4BAggregateCoordEquiv hn hc2).injective
    simpa using congrArg Prod.fst hcoord
  · apply (k4WAggregateCoordEquiv hn hc2).injective
    simpa using congrArg Prod.snd hcoord

private noncomputable def k4AggregateKernelToEEEEKernelReadInternal
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4AggregateKernel n b c d hn hb2 hc2 hd2 →ₗ[F]
      k4AggregateEEEEKernelInternal n b c d where
  toFun sigma :=
    ⟨diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma.1,
      eeee_mem_of_aggregate_kernel hn hb2 hc2 hd2 sigma⟩
  map_add' sigma tau := by
    apply Subtype.ext
    exact (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).map_add sigma.1 tau.1
  map_smul' r sigma := by
    apply Subtype.ext
    exact (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).map_smul r sigma.1

private noncomputable def k4AggregateKernelToEEEEKernelBuildInternal
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    k4AggregateEEEEKernelInternal n b c d →ₗ[F]
      K4AggregateKernel n b c d hn hb2 hc2 hd2 where
  toFun q :=
    ⟨(diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).symm q.1,
      aggregate_mem_of_eeee_kernel hn hb2 hc2 hd2 q⟩
  map_add' q q' := by
    apply Subtype.ext
    exact (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).symm.map_add q.1 q'.1
  map_smul' r q := by
    apply Subtype.ext
    exact (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).symm.map_smul r q.1

@[simp] private theorem k4AggregateKernelToEEEEKernelReadInternal_build
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : k4AggregateEEEEKernelInternal n b c d) :
    k4AggregateKernelToEEEEKernelReadInternal hn hb2 hc2 hd2
        (k4AggregateKernelToEEEEKernelBuildInternal hn hb2 hc2 hd2 q) = q := by
  apply Subtype.ext
  exact (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).apply_symm_apply q.1

@[simp] private theorem k4AggregateKernelToEEEEKernelBuildInternal_read
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4AggregateKernel n b c d hn hb2 hc2 hd2) :
    k4AggregateKernelToEEEEKernelBuildInternal hn hb2 hc2 hd2
        (k4AggregateKernelToEEEEKernelReadInternal hn hb2 hc2 hd2 sigma) = sigma := by
  apply Subtype.ext
  exact (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).symm_apply_apply sigma.1

private noncomputable def k4AggregateKernelToEEEEKernelEquivInternal
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4AggregateKernel n b c d hn hb2 hc2 hd2 ≃ₗ[F]
      k4AggregateEEEEKernelInternal n b c d where
  toLinearMap := k4AggregateKernelToEEEEKernelReadInternal hn hb2 hc2 hd2
  invFun := k4AggregateKernelToEEEEKernelBuildInternal hn hb2 hc2 hd2
  left_inv := k4AggregateKernelToEEEEKernelBuildInternal_read hn hb2 hc2 hd2
  right_inv := k4AggregateKernelToEEEEKernelReadInternal_build hn hb2 hc2 hd2

noncomputable def k4AggregateKernelEEEERead
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4AggregateKernel n b c d hn hb2 hc2 hd2 →ₗ[F]
      K4AggregateKernelEEEESource n b c d :=
  (k4AggregateEEEEKernelReadInternal
    (n := n) (b := b) (c := c) (d := d)).comp
    (k4AggregateKernelToEEEEKernelReadInternal hn hb2 hc2 hd2)

noncomputable def k4AggregateKernelEEEEBuild
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4AggregateKernelEEEESource n b c d →ₗ[F]
      K4AggregateKernel n b c d hn hb2 hc2 hd2 :=
  (k4AggregateKernelToEEEEKernelBuildInternal hn hb2 hc2 hd2).comp
    (k4AggregateEEEEKernelBuildInternal
      (n := n) (b := b) (c := c) (d := d))

theorem k4AggregateKernelEEEERead_coordinates
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4AggregateKernel n b c d hn hb2 hc2 hd2) :
    k4AggregateKernelEEEESourceEmbed
        (n := n) (b := b) (c := c) (d := d)
        (k4AggregateKernelEEEERead hn hb2 hc2 hd2 sigma) =
      diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 sigma.1 := by
  let q :=
    k4AggregateKernelToEEEEKernelReadInternal hn hb2 hc2 hd2 sigma
  have h :=
    congrArg Subtype.val
      (k4AggregateEEEEKernelBuildInternal_read
        (n := n) (b := b) (c := c) (d := d) q)
  exact h

theorem k4AggregateKernelEEEEBuild_coordinates
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4AggregateKernelEEEESource n b c d) :
    diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
        (k4AggregateKernelEEEEBuild hn hb2 hc2 hd2 x).1 =
      k4AggregateKernelEEEESourceEmbed
        (n := n) (b := b) (c := c) (d := d) x := by
  exact (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).apply_symm_apply
    (k4AggregateKernelEEEESourceEmbed
      (n := n) (b := b) (c := c) (d := d) x)

@[simp] theorem k4AggregateKernelEEEERead_build
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4AggregateKernelEEEESource n b c d) :
    k4AggregateKernelEEEERead hn hb2 hc2 hd2
        (k4AggregateKernelEEEEBuild hn hb2 hc2 hd2 x) = x := by
  apply k4AggregateKernelEEEESourceEmbed_injective
  calc
    _ = diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
          (k4AggregateKernelEEEEBuild hn hb2 hc2 hd2 x).1 :=
      k4AggregateKernelEEEERead_coordinates
        (n := n) (b := b) (c := c) (d := d)
        hn hb2 hc2 hd2
        (k4AggregateKernelEEEEBuild hn hb2 hc2 hd2 x)
    _ = _ :=
      k4AggregateKernelEEEEBuild_coordinates
        (n := n) (b := b) (c := c) (d := d)
        hn hb2 hc2 hd2 x

@[simp] theorem k4AggregateKernelEEEEBuild_read
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4AggregateKernel n b c d hn hb2 hc2 hd2) :
    k4AggregateKernelEEEEBuild hn hb2 hc2 hd2
        (k4AggregateKernelEEEERead hn hb2 hc2 hd2 sigma) = sigma := by
  apply Subtype.ext
  apply (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).injective
  calc
    _ = k4AggregateKernelEEEESourceEmbed
          (n := n) (b := b) (c := c) (d := d)
          (k4AggregateKernelEEEERead hn hb2 hc2 hd2 sigma) :=
      k4AggregateKernelEEEEBuild_coordinates
        (n := n) (b := b) (c := c) (d := d)
        hn hb2 hc2 hd2
        (k4AggregateKernelEEEERead hn hb2 hc2 hd2 sigma)
    _ = _ :=
      k4AggregateKernelEEEERead_coordinates
        (n := n) (b := b) (c := c) (d := d)
        hn hb2 hc2 hd2 sigma

noncomputable def k4AggregateKernelEEEEEquiv
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4AggregateKernel n b c d hn hb2 hc2 hd2 ≃ₗ[F]
      K4AggregateKernelEEEESource n b c d where
  toLinearMap := k4AggregateKernelEEEERead hn hb2 hc2 hd2
  invFun := k4AggregateKernelEEEEBuild hn hb2 hc2 hd2
  left_inv := k4AggregateKernelEEEEBuild_read hn hb2 hc2 hd2
  right_inv := k4AggregateKernelEEEERead_build hn hb2 hc2 hd2

end

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
