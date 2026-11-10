import Core4loop.SquareDiagonal.DirectWitt.OddPointedChannels

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

noncomputable section

/-- Odd projection from the J-zero cube space onto the high-frequency kernel. -/
noncomputable def diamondOddHighFreqProjection
    {n : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddJZero n →ₗ[F] DiamondOddHighFreq n where
  toFun X :=
    ⟨X + oddOrbitLift (oddOrbitSumPiRestrict X), by
      apply LinearMap.mem_ker.mpr
      rw [map_add, oddOrbitSumPiRestrict_oddOrbitLift hn,
        F_module_add_self]⟩
  map_add' X Y := by
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
    abel
  map_smul' r X := by
    apply Subtype.ext
    change
      r • X +
          oddOrbitLift (oddOrbitSumPiRestrict (r • X)) =
        r • (X + oddOrbitLift (oddOrbitSumPiRestrict X))
    rw [map_smul, map_smul, smul_add]

@[simp] theorem diamondOddHighFreqProjection_apply
    {n : Nat} [NeZero n] (hn : Odd n)
    (X : DiamondOddJZero n) :
    (diamondOddHighFreqProjection hn X).1 =
      X + oddOrbitLift (oddOrbitSumPiRestrict X) :=
  rfl

theorem diamondOddHighFreqProjection_decomposition
    {n : Nat} [NeZero n] (hn : Odd n)
    (X : DiamondOddJZero n) :
    X =
      (diamondOddHighFreqProjection hn X).1 +
        oddOrbitLift (oddOrbitSumPiRestrict X) := by
  rw [diamondOddHighFreqProjection_apply]
  let L := oddOrbitLift (oddOrbitSumPiRestrict X)
  calc
    X = X + 0 := (add_zero X).symm
    _ = X + (L + L) := by rw [F_module_add_self L]
    _ = (X + L) + L := (add_assoc X L L).symm

private theorem cubeDot_eq_iterated_sum
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    Core4loop.SquareDiagonal.EvenP.cubeDot X Y =
      ∑ i : I n, ∑ j : I n, ∑ k : I n,
        X i j k * Y i j k := by
  simp only [Core4loop.SquareDiagonal.EvenP.cubeDot]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]

private theorem diamondOddJZero_cubeDot_oddOrbitLift
    {n : Nat} [NeZero n]
    (X : DiamondOddJZero n)
    (p : DiamondOddOrbitProfile n) :
    Core4loop.SquareDiagonal.EvenP.cubeDot X.1
        (oddOrbitLift p).1 =
      ∑ j : I n, ∑ s : I n,
        (oddOrbitSumPiRestrict X).1 j s * p.1 j s := by
  rw [cubeDot_eq_iterated_sum]
  simp only [oddOrbitLift_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  calc
    (∑ k : I n, ∑ i : I n, X.1 i j k * p.1 j (i + k)) =
        ∑ i : I n, ∑ k : I n, X.1 i j k * p.1 j (i + k) := by
          rw [Finset.sum_comm]
    _ = ∑ i : I n, ∑ s : I n,
          X.1 i j (s - i) * p.1 j s := by
          apply Finset.sum_congr rfl
          intro i _
          let f : I n → F :=
            fun s => X.1 i j (s - i) * p.1 j s
          have hsum := Equiv.sum_comp (Equiv.addRight i) f
          calc
            (∑ k : I n, X.1 i j k * p.1 j (i + k)) =
                ∑ k : I n,
                  X.1 i j ((k + i) - i) * p.1 j (k + i) := by
                    apply Finset.sum_congr rfl
                    intro k _
                    congr 2 <;> abel
            _ = ∑ s : I n, X.1 i j (s - i) * p.1 j s := by
                    simpa only [f] using hsum
    _ = ∑ s : I n, ∑ i : I n,
          X.1 i j (s - i) * p.1 j s := by
          rw [Finset.sum_comm]
    _ = ∑ s : I n,
          (oddOrbitSumPiRestrict X).1 j s * p.1 j s := by
          apply Finset.sum_congr rfl
          intro s _
          change
            (∑ i : I n, X.1 i j (s - i) * p.1 j s) =
              (∑ i : I n, X.1 i j (s - i)) * p.1 j s
          rw [Finset.sum_mul]

theorem diamondOddHighFreq_cubeDot_oddOrbitLift_eq_zero
    {n : Nat} [NeZero n]
    (H : DiamondOddHighFreq n)
    (p : DiamondOddOrbitProfile n) :
    Core4loop.SquareDiagonal.EvenP.cubeDot H.1.1
      (oddOrbitLift p).1 = 0 := by
  rw [diamondOddJZero_cubeDot_oddOrbitLift]
  have hpi : oddOrbitSumPiRestrict H.1 = 0 :=
    LinearMap.mem_ker.mp H.2
  rw [hpi]
  simp

private noncomputable def oddHighFreqCubeIncl
    {n : Nat} [NeZero n] :
    DiamondOddHighFreq n →ₗ[F] CyclicCube n where
  toFun X := X.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Historical public name retained for the direct cube-dot dual map. -/
noncomputable def oddHighFreqPairing
    {n : Nat} [NeZero n] :
    DiamondOddHighFreq n →ₗ[F]
      Module.Dual F (DiamondOddHighFreq n) where
  toFun X :=
    (diamondOddCubeDotBilin (oddHighFreqCubeIncl X)).comp
      oddHighFreqCubeIncl
  map_add' X Y := by
    apply LinearMap.ext
    intro Z
    change
      diamondOddCubeDotBilin
          (oddHighFreqCubeIncl (X + Y))
          (oddHighFreqCubeIncl Z) =
        diamondOddCubeDotBilin (oddHighFreqCubeIncl X)
            (oddHighFreqCubeIncl Z) +
          diamondOddCubeDotBilin (oddHighFreqCubeIncl Y)
            (oddHighFreqCubeIncl Z)
    rw [map_add, map_add]
    rfl
  map_smul' r X := by
    apply LinearMap.ext
    intro Y
    change
      diamondOddCubeDotBilin
          (oddHighFreqCubeIncl (r • X))
          (oddHighFreqCubeIncl Y) =
        r • diamondOddCubeDotBilin
          (oddHighFreqCubeIncl X) (oddHighFreqCubeIncl Y)
    rw [map_smul, map_smul]
    rfl

@[simp] theorem oddHighFreqPairing_apply
    {n : Nat} [NeZero n]
    (X Y : DiamondOddHighFreq n) :
    oddHighFreqPairing X Y =
      ∑ i : I n, ∑ j : I n, ∑ k : I n,
        X.1.1 i j k * Y.1.1 i j k := by
  simp only [oddHighFreqPairing, LinearMap.comp_apply,
    oddHighFreqCubeIncl, diamondOddCubeDotBilin,
    LinearMap.coe_mk, AddHom.coe_mk]
  exact cubeDot_eq_iterated_sum X.1.1 Y.1.1

private theorem diamondOddJZero_cubeDot_nondegenerate
    {n : Nat} [NeZero n] (hn : Odd n)
    (X : DiamondOddJZero n)
    (hX : ∀ Y : DiamondOddJZero n,
      Core4loop.SquareDiagonal.EvenP.cubeDot X.1 Y.1 = 0) :
    X = 0 := by
  apply Subtype.ext
  funext i j k
  let f : I n → F := fun u => X.1 i u k
  have hcard : Odd (Fintype.card (I n)) := by
    simpa [I, ZMod.card] using hn
  have hsum : (∑ u : I n, f u) = 0 := by
    exact congrFun (congrFun (LinearMap.mem_ker.mp X.2) i) k
  have hfst :
      (pointedSrcOddEquiv (I n) 0 hcard f).1 = 0 := by
    rw [pointedSrcOddEquiv_apply_fst]
    exact hsum
  have htail :
      (pointedSrcOddEquiv (I n) 0 hcard f).2 = 0 := by
    funext t
    let e : PointedTail (I n) 0 → F := Pi.single t (1 : F)
    let g : I n → F :=
      pointedDualOddBuild (I n) 0 (0, e)
    have hgsum : (∑ u : I n, g u) = 0 := by
      simpa only [g] using
        pointedDualOddBuild_sum 0 hcard (0, e)
    let Y : DiamondOddJZero n :=
      ⟨fun i' j' k' =>
          if i' = i ∧ k' = k then g j' else 0, by
        apply LinearMap.mem_ker.mpr
        funext i' k'
        change
          (∑ j' : I n,
            if i' = i ∧ k' = k then g j' else 0) = 0
        by_cases hi : i' = i
        · by_cases hk : k' = k
          · simpa [hi, hk] using hgsum
          · simp [hk]
        · simp [hi]⟩
    have hpair := hX Y
    have hselect :
        Core4loop.SquareDiagonal.EvenP.cubeDot X.1 Y.1 =
          ∑ u : I n, f u * g u := by
      rw [cubeDot_eq_iterated_sum]
      classical
      simp only [Y, f]
      rw [Finset.sum_eq_single i]
      · apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_eq_single k]
        · simp
        · intro k' _ hk'
          simp [hk']
        · simp
      · intro i' _ hi'
        simp [hi']
      · simp
    rw [hselect] at hpair
    rw [pointedOdd_pairing 0 hcard f g] at hpair
    have hdual :
        pointedDualOddEquiv (I n) 0 hcard g = (0, e) := by
      simpa only [g, pointedDualOddEquiv] using
        pointedDualOddRead_build 0 hcard (0, e)
    rw [hfst, hdual] at hpair
    simp only [zero_mul, zero_add] at hpair
    rw [Finset.sum_eq_single t] at hpair
    · simpa [e] using hpair
    · intro u _ hut
      simp [e, hut]
    · simp [e]
  have heq :
      pointedSrcOddEquiv (I n) 0 hcard f = 0 := by
    apply Prod.ext
    · exact hfst
    · exact htail
  have hf : f = 0 :=
    (pointedSrcOddEquiv (I n) 0 hcard).injective
      (by simpa using heq)
  exact congrFun hf j

theorem ker_oddHighFreqPairing
    {n : Nat} [NeZero n] (hn : Odd n) :
    LinearMap.ker (oddHighFreqPairing (n := n)) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro H hH
  have hpair : ∀ K : DiamondOddHighFreq n,
      Core4loop.SquareDiagonal.EvenP.cubeDot H.1.1 K.1.1 = 0 := by
    intro K
    have h := LinearMap.congr_fun hH K
    simpa [oddHighFreqPairing, oddHighFreqCubeIncl,
      diamondOddCubeDotBilin] using h
  have hJ : ∀ X : DiamondOddJZero n,
      Core4loop.SquareDiagonal.EvenP.cubeDot H.1.1 X.1 = 0 := by
    intro X
    rw [diamondOddHighFreqProjection_decomposition hn X]
    change
      diamondOddCubeDotBilin H.1.1
          ((diamondOddHighFreqProjection hn X).1.1 +
            (oddOrbitLift (oddOrbitSumPiRestrict X)).1) = 0
    rw [map_add]
    change
      Core4loop.SquareDiagonal.EvenP.cubeDot H.1.1
          (diamondOddHighFreqProjection hn X).1.1 +
        Core4loop.SquareDiagonal.EvenP.cubeDot H.1.1
          (oddOrbitLift (oddOrbitSumPiRestrict X)).1 = 0
    rw [hpair, diamondOddHighFreq_cubeDot_oddOrbitLift_eq_zero, add_zero]
  have hz : H.1 = 0 :=
    diamondOddJZero_cubeDot_nondegenerate hn H.1 hJ
  apply Subtype.ext
  exact hz

private theorem range_oddHighFreqPairing_eq_top
    {n : Nat} [NeZero n] (hn : Odd n) :
    LinearMap.range (oddHighFreqPairing (n := n)) = ⊤ :=
  (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
    Subspace.dual_finrank_eq.symm).mp
      (ker_oddHighFreqPairing hn)

/-- Historical public endpoint retained; range equality is an internal proof
bridge rather than a replacement for this API. -/
theorem oddHighFreqPairing_surjective
    {n : Nat} [NeZero n] (hn : Odd n) :
    Function.Surjective (oddHighFreqPairing (n := n)) :=
  LinearMap.range_eq_top.mp (range_oddHighFreqPairing_eq_top hn)

end

end Core4loop.SquareDiagonal.DirectWitt
