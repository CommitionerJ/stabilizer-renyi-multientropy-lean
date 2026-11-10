import Core4loop.SquareDiagonal.DirectWitt.OddChannelProduct

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

open Core4loop
open Core4loop.SquareDiagonal.EvenP

noncomputable section

attribute [local instance] Fintype.ofFinite

private noncomputable local instance diamondOddResidualCyclicCubeFintype
    {n : Nat} [NeZero n] : Fintype (CyclicCube n) :=
  Fintype.ofFinite _

private noncomputable local instance diamondOddResidualAxisChannelFintype
    {n k : Nat} [NeZero n] : Fintype (DiamondOddAxisChannel n k) :=
  Fintype.ofFinite _

private noncomputable local instance diamondOddResidualScalarSourceFintype
    {n : Nat} [NeZero n] : Fintype (DiamondOddScalarSource n) :=
  Fintype.ofInjective
    (fun x : DiamondOddScalarSource n => x.1)
    Subtype.val_injective

private noncomputable local instance diamondOddResidualPointedAmbientFintype
    {n a b c d : Nat} [NeZero n] :
    Fintype (DiamondOddPointedAmbient n a b c d) := by
  dsimp only [DiamondOddPointedAmbient, DiamondOddAChannels,
    DiamondOddBChannels, DiamondOddWChannels]
  infer_instance

private noncomputable local instance diamondOddResidualPointedSourceFintype
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    Fintype (DiamondOddPointedSource n a b c d hn) :=
  Fintype.ofInjective
    (fun x : DiamondOddPointedSource n a b c d hn => x.1)
    Subtype.val_injective

@[reducible] private noncomputable def diamondOddResidualRowFintype
    {n a b c d : Nat} [NeZero n] (r : DiamondOddChannelRow) :
    Fintype ↥(DiamondOddChannelRowSpace n a b c d r) := by
  cases r <;> simp only [DiamondOddChannelRowSpace] <;>
    infer_instance

attribute [local instance] diamondOddResidualRowFintype

private noncomputable local instance diamondOddResidualPreCSourceFintype
    {n a b c d : Nat} [NeZero n] :
    Fintype (DiamondPreCSource n a b c d) := by
  letI :
      Fintype
        (AFun4 n b c d × BFun4 n a c d × WFun4 n a b c) :=
    Fintype.ofFinite _
  exact Fintype.ofInjective
    (fun x : DiamondPreCSource n a b c d => x.1)
    Subtype.val_injective

noncomputable def diamondOddSSTSRowEquiv
    {n c : Nat} [NeZero n] :
    (DiamondOddAxisTail n c → DiamondOddScalarAmbient n) ≃ₗ[F]
      ((DiamondOddAxisTail n c → DiamondEOOOLeftAmbient n) ×
        (DiamondOddAxisTail n c → CyclicCube n)) where
  toFun x := (fun zt => (x zt).2, fun zt => (x zt).1)
  invFun x := fun zt => (x.2 zt, x.1 zt)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def diamondOddSSTTRowEquiv
    {n c d : Nat} [NeZero n] :
    (DiamondOddAxisTail n c →
        DiamondOddAxisTail n d → (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      ((DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n) ×
        (DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n)) where
  toFun x := (fun zt wt => (x zt wt).2, fun zt wt => (x zt wt).1)
  invFun x := fun zt wt => (x.2 zt wt, x.1 zt wt)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def diamondOddSTTSRowEquiv
    {n b c : Nat} [NeZero n] :
    (DiamondOddAxisTail n b →
        DiamondOddAxisTail n c → (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      ((DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → CyclicCube n) ×
        (DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → CyclicCube n)) where
  toFun x := (fun yt zt => (x yt zt).2, fun yt zt => (x yt zt).1)
  invFun x := fun yt zt => (x.2 yt zt, x.1 yt zt)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem diamondOddResidual_cubeDot_comm
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    cubeDot x y = cubeDot y x := by
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_comm]

private theorem diamondOddResidual_axisTailJ_fst
    {n k : Nat} [NeZero n]
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (u : DiamondOddAxisTail n k → U × V)
    (t : DiamondOddAxisTail n k) :
    (diamondOddAxisTailJ (U × V) u t).1 =
      diamondOddAxisTailJ U (fun s => (u s).1) t := by
  simp only [diamondOddAxisTailJ_apply, Prod.fst_add]
  change
    (u t).1 + (LinearMap.fst F U V) (∑ v, u v) =
      (u t).1 + ∑ s, (LinearMap.fst F U V) (u s)
  rw [map_sum]

private theorem diamondOddResidual_axisTailJ_snd
    {n k : Nat} [NeZero n]
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (u : DiamondOddAxisTail n k → U × V)
    (t : DiamondOddAxisTail n k) :
    (diamondOddAxisTailJ (U × V) u t).2 =
      diamondOddAxisTailJ V (fun s => (u s).2) t := by
  simp only [diamondOddAxisTailJ_apply, Prod.snd_add]
  change
    (u t).2 + (LinearMap.snd F U V) (∑ v, u v) =
      (u t).2 + ∑ s, (LinearMap.snd F U V) (u s)
  rw [map_sum]

theorem diamondOddChannelPhaseSSTS_eq_cross
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (rows : DiamondOddChannelProduct n a b c d) :
    diamondOddChannelPhaseSSTS rows =
      diamondOddSSTSCross hn
        (diamondOddSSTSRowEquiv (rows .ssts)).1
        (diamondOddSSTSRowEquiv (rows .ssts)).2 := by
  rw [diamondOddSSTSCross_apply]
  unfold diamondOddChannelPhaseSSTS
  apply Finset.sum_congr rfl
  intro zt _
  rw [diamondOddResidual_cubeDot_comm]
  change
    cubeDot
      (cubeDiffI
          (diamondOddAxisTailJ (CyclicCube n)
            (fun zt' => (rows .ssts zt').2.1) zt) +
        cubeDiffK
          (diamondOddAxisTailJ (CyclicCube n)
            (fun zt' => (rows .ssts zt').2.2) zt))
      (rows .ssts zt).1 =
    cubeDot
      (cubeDiffI
          (diamondOddAxisTailJ
            (DiamondEOOOLeftAmbient n)
            (fun zt' => (rows .ssts zt').2) zt).1 +
        cubeDiffK
          (diamondOddAxisTailJ
            (DiamondEOOOLeftAmbient n)
            (fun zt' => (rows .ssts zt').2) zt).2)
      (rows .ssts zt).1
  rw [diamondOddResidual_axisTailJ_fst,
    diamondOddResidual_axisTailJ_snd]

theorem diamondOddChannelPhaseSSTT_eq_cross
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (rows : DiamondOddChannelProduct n a b c d) :
    diamondOddChannelPhaseSSTT rows =
      diamondOddSSTTCross hn
        (diamondOddSSTTRowEquiv (rows .sstt)).1
        (diamondOddSSTTRowEquiv (rows .sstt)).2 := by
  rw [diamondOddSSTTCross_apply]
  unfold diamondOddChannelPhaseSSTT
  apply Finset.sum_congr rfl
  intro zt _
  apply Finset.sum_congr rfl
  intro wt _
  rw [diamondOddResidual_cubeDot_comm]
  rfl

theorem diamondOddChannelPhaseSTTS_eq_cross
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (rows : DiamondOddChannelProduct n a b c d) :
    diamondOddChannelPhaseSTTS rows =
      diamondOddSTTSCross hn
        (diamondOddSTTSRowEquiv (rows .stts)).1
        (diamondOddSTTSRowEquiv (rows .stts)).2 := by
  rw [diamondOddSTTSCross_apply]
  unfold diamondOddChannelPhaseSTTS
  apply Finset.sum_congr rfl
  intro yt _
  apply Finset.sum_congr rfl
  intro zt _
  rw [diamondOddResidual_cubeDot_comm]
  rfl

noncomputable def diamondOddChannelRowQ
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    (r : DiamondOddChannelRow) →
      ↥(DiamondOddChannelRowSpace n a b c d r) → F := by
  intro r
  cases r with
  | ssss => exact fun x => diamondOddScalarQ x
  | ssts =>
      exact fun x =>
        diamondOddSSTSCross hn
          (diamondOddSSTSRowEquiv x).1
          (diamondOddSSTSRowEquiv x).2
  | sstt =>
      exact fun x =>
        diamondOddSSTTCross hn
          (diamondOddSSTTRowEquiv x).1
          (diamondOddSSTTRowEquiv x).2
  | stts =>
      exact fun x =>
        diamondOddSTTSCross hn
          (diamondOddSTTSRowEquiv x).1
          (diamondOddSTTSRowEquiv x).2
  | _ => exact fun _ => 0

theorem diamondOddChannelReducedQ_eq_sum_rowQ
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (rows : DiamondOddChannelProduct n a b c d) :
    diamondOddChannelReducedQ rows =
      ∑ r : DiamondOddChannelRow,
        diamondOddChannelRowQ hn r (rows r) := by
  classical
  have hrows :
      (Finset.univ : Finset DiamondOddChannelRow) =
        {.ssss, .ssst, .ssts, .sstt,
         .stss, .stst, .stts, .sttt,
         .tsss, .tsst, .tsts, .tstt,
         .ttss, .ttst, .ttts, .tttt} := by
    ext r
    cases r <;> simp
  unfold diamondOddChannelReducedQ
  rw [diamondOddChannelPhaseSSTS_eq_cross hn rows,
    diamondOddChannelPhaseSSTT_eq_cross hn rows,
    diamondOddChannelPhaseSTTS_eq_cross hn rows]
  rw [hrows]
  simp [diamondOddChannelRowQ, diamondOddChannelPhaseSSSS]
  abel

noncomputable def diamondOddChannelRowHalfRank
    {n b c d : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddChannelRow → Nat
  | .ssss => Module.finrank F (DiamondOddHighFreq n)
  | .ssts =>
      Module.finrank F
        (LinearMap.range (diamondOddSSTSCross (c := c) hn))
  | .sstt =>
      Module.finrank F
        (LinearMap.range
          (diamondOddSSTTCross (c := c) (d := d) hn))
  | .stts =>
      Module.finrank F
        (LinearMap.range
          (diamondOddSTTSCross (b := b) (c := c) hn))
  | _ => 0

noncomputable def diamondOddChannelRowExponent
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    (r : DiamondOddChannelRow) → Nat
  | .ssss =>
      Module.finrank F
          (LinearMap.ker
            (diamondOddScalarWittMap (n := n) hn)) +
        Module.finrank F (DiamondOddHighFreq n)
  | .ssts =>
      Module.finrank F
          (LinearMap.ker
            (diamondOddSSTSCross (c := c) hn)) +
        Module.finrank F
          (DiamondOddAxisTail n c → CyclicCube n)
  | .sstt =>
      Module.finrank F
          (LinearMap.ker
            (diamondOddSSTTCross (c := c) (d := d) hn)) +
        Module.finrank F
          (DiamondOddAxisTail n c →
            DiamondOddAxisTail n d → CyclicCube n)
  | .stts =>
      Module.finrank F
          (LinearMap.ker
            (diamondOddSTTSCross (b := b) (c := c) hn)) +
        Module.finrank F
          (DiamondOddAxisTail n b →
            DiamondOddAxisTail n c → CyclicCube n)
  | r =>
      Module.finrank F
        ↥(DiamondOddChannelRowSpace n a b c d r)

def diamondOddHalfRank (n b c d : Nat) : Nat :=
  n * (n - 1) *
    ((n - 1) +
      (n ^ (c - 1) - 1) *
        (n * ((n ^ (b - 1) - 1) + (n ^ (d - 1) - 1) + 1) + 1))

noncomputable def diamondOddResidualExponent
    {n a b c d : Nat} [NeZero n] (hn : Odd n) : Nat :=
  ∑ r : DiamondOddChannelRow,
    diamondOddChannelRowExponent
      (a := a) (b := b) (c := c) (d := d) hn r

private theorem diamondOddResidual_bitSign_sum_eq_prod
    {ι : Type*} [Fintype ι] (q : ι → F) :
    bitSign (∑ i, q i) = ∏ i, bitSign (q i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp [bitSign_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, bitSign_add, ih]

private theorem diamondOddResidual_sum_pi_bitSign_eq_prod
    {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (q : ∀ i, X i → F) :
    (∑ x : ∀ i, X i, bitSign (∑ i, q i (x i))) =
      ∏ i, ∑ y : X i, bitSign (q i y) := by
  classical
  simp_rw [diamondOddResidual_bitSign_sum_eq_prod]
  convert
    (Fintype.prod_sum (fun i y => bitSign (q i y))).symm using 1
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _
    rfl

private theorem diamondOddResidual_actual_factorization
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    (∑ rows : DiamondOddChannelProduct n a b c d,
        bitSign
          (∑ r : DiamondOddChannelRow,
            diamondOddChannelRowQ hn r (rows r))) =
      ∏ r : DiamondOddChannelRow,
        ∑ x : ↥(DiamondOddChannelRowSpace n a b c d r),
          bitSign (diamondOddChannelRowQ hn r x) := by
  convert
    diamondOddResidual_sum_pi_bitSign_eq_prod
      (X := fun r =>
        ↥(DiamondOddChannelRowSpace n a b c d r))
      (diamondOddChannelRowQ hn) using 1
  apply Finset.sum_congr
  · ext rows
    simp
  · intro rows _
    rfl

private theorem diamondOddResidual_sum_zero_eq_pow_finrank
    {V : Type*}
    [AddCommGroup V] [Module F V] [Fintype V] :
    (∑ _x : V, bitSign 0) =
      (2 : Int) ^ Module.finrank F V := by
  simp only [bitSign_zero, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact_mod_cast (Module.card_eq_pow_finrank (K := F) (V := V))

private theorem diamondOddResidual_sum_bilinear_reindex
    {S U V : Type*}
    [AddCommGroup S] [Module F S] [Fintype S]
    [AddCommGroup U] [Module F U] [Finite U]
    [AddCommGroup V] [Module F V] [Finite V]
    (e : S ≃ₗ[F] U × V)
    (L : U →ₗ[F] Module.Dual F V) :
    (∑ x : S, bitSign (L (e x).1 (e x).2)) =
      (2 : Int) ^
        (Module.finrank F (LinearMap.ker L) +
          Module.finrank F V) := by
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype V := Fintype.ofFinite V
  calc
    (∑ x : S, bitSign (L (e x).1 (e x).2)) =
        ∑ z : U × V, bitSign (L z.1 z.2) := by
      exact Fintype.sum_equiv e.toEquiv
        (fun x : S => bitSign (L (e x).1 (e x).2))
        (fun z : U × V => bitSign (L z.1 z.2))
        (fun _ => rfl)
    _ = (2 : Int) ^
          (Module.finrank F (LinearMap.ker L) +
            Module.finrank F V) :=
      sum_bitSign_bilinear_eq_pow L

theorem diamondOddChannelRow_sum_eq_pow
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (r : DiamondOddChannelRow) :
    (∑ x : ↥(DiamondOddChannelRowSpace n a b c d r),
        bitSign (diamondOddChannelRowQ hn r x)) =
      (2 : Int) ^
        diamondOddChannelRowExponent
          (a := a) (b := b) (c := c) (d := d) hn r := by
  cases r <;>
    simp only [DiamondOddChannelRowSpace, diamondOddChannelRowQ,
      diamondOddChannelRowExponent]
  case ssss =>
      rw [finrank_DiamondOddHighFreq]
      convert (sum_bitSign_diamondOddScalarQ_eq_pow hn) using 1
      apply Finset.sum_congr
      · ext x
        simp
      · intro x _
        rfl
  case ssts =>
      exact
        (diamondOddResidual_sum_bilinear_reindex
          (diamondOddSSTSRowEquiv (n := n) (c := c))
          (diamondOddSSTSCross (c := c) hn))
  case sstt =>
      exact
        (diamondOddResidual_sum_bilinear_reindex
          (diamondOddSSTTRowEquiv (n := n) (c := c) (d := d))
          (diamondOddSSTTCross (c := c) (d := d) hn))
  case stts =>
      exact
        (diamondOddResidual_sum_bilinear_reindex
          (diamondOddSTTSRowEquiv (n := n) (b := b) (c := c))
          (diamondOddSTTSCross (b := b) (c := c) hn))
  all_goals
    exact diamondOddResidual_sum_zero_eq_pow_finrank

private theorem diamondOddResidual_bilinear_exponent_add_range
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    [FiniteDimensional F U] [FiniteDimensional F V]
    (L : U →ₗ[F] Module.Dual F V) :
    (Module.finrank F (LinearMap.ker L) +
        Module.finrank F V) +
      Module.finrank F (LinearMap.range L) =
      Module.finrank F (U × V) := by
  rw [Module.finrank_prod]
  have h := LinearMap.finrank_range_add_finrank_ker L
  omega

private theorem diamondOddResidual_scalar_exponent_add_halfRank
    {n : Nat} [NeZero n] (hn : Odd n) :
    (Module.finrank F
          (LinearMap.ker
            (diamondOddScalarWittMap (n := n) hn)) +
        Module.finrank F (DiamondOddHighFreq n)) +
      Module.finrank F (DiamondOddHighFreq n) =
      Module.finrank F (DiamondOddScalarSource n) := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondOddScalarWittMap (n := n) hn)
  have hrange :
      LinearMap.range
          (diamondOddScalarWittMap (n := n) hn) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (diamondOddScalarWittMap_surjective hn)
  rw [hrange, finrank_top, Module.finrank_prod,
    Subspace.dual_finrank_eq] at h
  omega

theorem diamondOddChannelRowExponent_add_halfRank
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (r : DiamondOddChannelRow) :
    diamondOddChannelRowExponent
          (a := a) (b := b) (c := c) (d := d) hn r +
        diamondOddChannelRowHalfRank
          (b := b) (c := c) (d := d) hn r =
      Module.finrank F
        ↥(DiamondOddChannelRowSpace n a b c d r) := by
  cases r <;>
    simp only [DiamondOddChannelRowSpace,
      diamondOddChannelRowExponent, diamondOddChannelRowHalfRank]
  case ssss =>
      exact diamondOddResidual_scalar_exponent_add_halfRank hn
  case ssts =>
      calc
        _ = Module.finrank F
              ((DiamondOddAxisTail n c → DiamondEOOOLeftAmbient n) ×
                (DiamondOddAxisTail n c → CyclicCube n)) :=
          diamondOddResidual_bilinear_exponent_add_range
            (diamondOddSSTSCross (c := c) hn)
        _ = Module.finrank F
              (DiamondOddAxisTail n c →
                DiamondOddScalarAmbient n) :=
          (LinearEquiv.finrank_eq
            (diamondOddSSTSRowEquiv (n := n) (c := c))).symm
  case sstt =>
      calc
        _ = Module.finrank F
              ((DiamondOddAxisTail n c →
                  DiamondOddAxisTail n d → CyclicCube n) ×
                (DiamondOddAxisTail n c →
                  DiamondOddAxisTail n d → CyclicCube n)) :=
          diamondOddResidual_bilinear_exponent_add_range
            (diamondOddSSTTCross (c := c) (d := d) hn)
        _ = Module.finrank F
              (DiamondOddAxisTail n c →
                DiamondOddAxisTail n d →
                  (CyclicCube n × CyclicCube n)) :=
          (LinearEquiv.finrank_eq
            (diamondOddSSTTRowEquiv
              (n := n) (c := c) (d := d))).symm
  case stts =>
      calc
        _ = Module.finrank F
              ((DiamondOddAxisTail n b →
                  DiamondOddAxisTail n c → CyclicCube n) ×
                (DiamondOddAxisTail n b →
                  DiamondOddAxisTail n c → CyclicCube n)) :=
          diamondOddResidual_bilinear_exponent_add_range
            (diamondOddSTTSCross (b := b) (c := c) hn)
        _ = Module.finrank F
              (DiamondOddAxisTail n b →
                DiamondOddAxisTail n c →
                  (CyclicCube n × CyclicCube n)) :=
          (LinearEquiv.finrank_eq
            (diamondOddSTTSRowEquiv
              (n := n) (b := b) (c := c))).symm
  all_goals omega

private theorem diamondOddHalfRank_eq_four_rows
    (n b c d : Nat) :
    diamondOddHalfRank n b c d =
      n * (n - 1) ^ 2 +
      (n ^ (c - 1) - 1) * (n * (n - 1) * (n + 1)) +
      (n ^ (c - 1) - 1) * (n ^ (d - 1) - 1) *
        (n ^ 2 * (n - 1)) +
      (n ^ (b - 1) - 1) * (n ^ (c - 1) - 1) *
        (n ^ 2 * (n - 1)) := by
  unfold diamondOddHalfRank
  ring

theorem diamondOddHalfRank_eq_sum_rowHalfRank
    {n b c d : Nat} [NeZero n] (hn : Odd n) :
    diamondOddHalfRank n b c d =
      ∑ r : DiamondOddChannelRow,
        diamondOddChannelRowHalfRank
          (b := b) (c := c) (d := d) hn r := by
  classical
  have hrows :
      (Finset.univ : Finset DiamondOddChannelRow) =
        {.ssss, .ssst, .ssts, .sstt,
         .stss, .stst, .stts, .sttt,
         .tsss, .tsst, .tsts, .tstt,
         .ttss, .ttst, .ttts, .tttt} := by
    ext r
    cases r <;> simp
  rw [hrows]
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton,
    or_self, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton]
  simp only [diamondOddChannelRowHalfRank, add_zero, zero_add]
  rw [finrank_DiamondOddHighFreq,
    rank_diamondOddSSTSCross,
    rank_diamondOddSSTTCross,
    rank_diamondOddSTTSCross]
  simpa only [add_assoc] using
    (diamondOddHalfRank_eq_four_rows n b c d)

private theorem diamondOddResidual_prod_pow_eq_pow_sum
    {ι : Type*} [Fintype ι] (e : ι → Nat) :
    ∏ i, (2 : Int) ^ e i = (2 : Int) ^ ∑ i, e i := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, pow_add]

private theorem diamondOddResidual_pointed_sum_transport
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    (∑ x : DiamondOddPointedSource n a b c d hn,
        bitSign (diamondOddPointedQ x)) =
      ∑ rows : DiamondOddChannelProduct n a b c d,
        bitSign (diamondOddChannelReducedQ rows) := by
  exact Fintype.sum_equiv
    (diamondOddChannelProductEquiv hn).toEquiv
    (fun x : DiamondOddPointedSource n a b c d hn =>
      bitSign (diamondOddPointedQ x))
    (fun rows : DiamondOddChannelProduct n a b c d =>
      bitSign (diamondOddChannelReducedQ rows))
    (fun x => by
      change
        bitSign (diamondOddPointedQ x) =
          bitSign
            (diamondOddChannelReducedQ
              (diamondOddChannelProductEquiv hn x))
      rw [diamondOddPointedQ_eq_channelReducedQ])

theorem sum_bitSign_diamondOddPointedQ_eq_pow
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    (∑ x : DiamondOddPointedSource n a b c d hn,
        bitSign (diamondOddPointedQ x)) =
      (2 : Int) ^
        diamondOddResidualExponent
          (a := a) (b := b) (c := c) (d := d) hn := by
  rw [diamondOddResidual_pointed_sum_transport hn]
  simp_rw [diamondOddChannelReducedQ_eq_sum_rowQ hn]
  rw [diamondOddResidual_actual_factorization hn]
  simp_rw [diamondOddChannelRow_sum_eq_pow hn]
  rw [diamondOddResidual_prod_pow_eq_pow_sum]
  rfl

private theorem
    diamondOddResidual_sum_exponent_add_sum_halfRank_eq_source_finrank
    {ι S : Type*} [Fintype ι]
    [AddCommGroup S] [Module F S]
    (X : ι → ModuleCat F)
    [∀ i, FiniteDimensional F (X i : Type)]
    (rowExponent rowHalfRank : ι → Nat)
    (hrow : ∀ i,
      rowExponent i + rowHalfRank i =
        Module.finrank F (X i : Type))
    (e : S ≃ₗ[F] ((i : ι) → (X i : Type))) :
    (∑ i, rowExponent i) + (∑ i, rowHalfRank i) =
      Module.finrank F S := by
  rw [LinearEquiv.finrank_eq e]
  rw [Module.finrank_pi_fintype, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]

theorem diamondOddResidualExponent_add_halfRank_eq_pointedSource
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    diamondOddResidualExponent
          (a := a) (b := b) (c := c) (d := d) hn +
        diamondOddHalfRank n b c d =
      Module.finrank F
        (DiamondOddPointedSource n a b c d hn) := by
  unfold diamondOddResidualExponent
  rw [diamondOddHalfRank_eq_sum_rowHalfRank hn]
  exact
    diamondOddResidual_sum_exponent_add_sum_halfRank_eq_source_finrank
      (X := DiamondOddChannelRowSpace n a b c d)
      (diamondOddChannelRowExponent
        (a := a) (b := b) (c := c) (d := d) hn)
      (diamondOddChannelRowHalfRank
        (b := b) (c := c) (d := d) hn)
      (diamondOddChannelRowExponent_add_halfRank hn)
      (diamondOddChannelProductEquiv hn)

private theorem diamondOddResidual_preC_sum_transport
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    (∑ x : DiamondPreCSource n a b c d,
        bitSign (diamondPreCQ x)) =
      ∑ y : DiamondOddPointedSource n a b c d hn,
        bitSign (diamondOddPointedQ y) := by
  exact Fintype.sum_equiv
    (diamondOddPreCPointedSourceEquiv hb hc hd hn).toEquiv
    (fun x : DiamondPreCSource n a b c d =>
      bitSign (diamondPreCQ x))
    (fun y : DiamondOddPointedSource n a b c d hn =>
      bitSign (diamondOddPointedQ y))
    (fun x => by
      change
        bitSign (diamondPreCQ x) =
          bitSign
            (diamondOddPointedQ
              (diamondOddPreCPointedSourceEquiv hb hc hd hn x))
      rw [diamondPreCQ_eq_oddPointedQ])

theorem sum_bitSign_diamondPreCQ_eq_pow_of_odd
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    (∑ x : DiamondPreCSource n a b c d,
        bitSign (diamondPreCQ x)) =
      (2 : Int) ^
        diamondOddResidualExponent
          (a := a) (b := b) (c := c) (d := d) hn := by
  rw [diamondOddResidual_preC_sum_transport hb hc hd hn]
  exact sum_bitSign_diamondOddPointedQ_eq_pow hn

private theorem diamondOddResidual_preC_pointed_finrank
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    Module.finrank F (DiamondPreCSource n a b c d) =
      Module.finrank F
        (DiamondOddPointedSource n a b c d hn) :=
  LinearEquiv.finrank_eq
    (diamondOddPreCPointedSourceEquiv hb hc hd hn)

theorem diamondOddResidualExponent_add_halfRank_eq_preCSource
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    diamondOddResidualExponent
          (a := a) (b := b) (c := c) (d := d) hn +
        diamondOddHalfRank n b c d =
      Module.finrank F (DiamondPreCSource n a b c d) := by
  rw [diamondOddResidualExponent_add_halfRank_eq_pointedSource hn]
  exact
    (diamondOddResidual_preC_pointed_finrank hb hc hd hn).symm

end

end Core4loop.SquareDiagonal.DirectWitt
