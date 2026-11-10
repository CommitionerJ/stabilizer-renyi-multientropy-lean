import Core4loop.SquareDiagonal.DirectWitt.OddLiteralReindex

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

open Core4loop.SquareDiagonal.EvenP

noncomputable section

local instance (S : Type*) : DecidableEq S := Classical.decEq S

/-! ## O0 — channel packaging and the genuine odd twist -/

abbrev DiamondOddAxisTail
    (n k : Nat) [NeZero n] :=
  PointedTail (PVec n k) (zeroVec : PVec n k)

abbrev DiamondOddAxisChannel
    (n k : Nat) [NeZero n] :=
  Option (DiamondOddAxisTail n k)

def diamondOddChannelS
    {n k : Nat} [NeZero n] :
    DiamondOddAxisChannel n k :=
  none

def diamondOddChannelT
    {n k : Nat} [NeZero n]
    (t : DiamondOddAxisTail n k) :
    DiamondOddAxisChannel n k :=
  some t

noncomputable def pointedOddValueChannelEquiv
    (S V : Type*) [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V] :
    PointedOddValueCoords S V s0 ≃ₗ[F]
      (Option (PointedTail S s0) → V) where
  toFun x
    | none => x.1
    | some t => x.2 t
  invFun f := (f none, fun t => f (some t))
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext t
      rfl
  right_inv f := by
    funext q
    cases q <;> rfl
  map_add' x y := by
    funext q
    cases q <;> rfl
  map_smul' r x := by
    funext q
    cases q <;> rfl

noncomputable def diamondOddAxisSrcChannelEquiv
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) :
    (PVec n k → V) ≃ₗ[F]
      (DiamondOddAxisChannel n k → V) :=
  (diamondOddAxisSrcCoordEquiv V hn).trans
    (pointedOddValueChannelEquiv
      (PVec n k) V (zeroVec : PVec n k))

noncomputable def diamondOddAxisDualChannelEquiv
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) :
    (PVec n k → V) ≃ₗ[F]
      (DiamondOddAxisChannel n k → V) :=
  (diamondOddAxisDualCoordEquiv V hn).trans
    (pointedOddValueChannelEquiv
      (PVec n k) V (zeroVec : PVec n k))

@[simp] theorem diamondOddAxisSrcChannelEquiv_apply_S
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (f : PVec n k → V) :
    diamondOddAxisSrcChannelEquiv V hn f diamondOddChannelS =
      ∑ s, f s := by
  rfl

@[simp] theorem diamondOddAxisSrcChannelEquiv_apply_T
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (f : PVec n k → V)
    (t : DiamondOddAxisTail n k) :
    diamondOddAxisSrcChannelEquiv V hn f (diamondOddChannelT t) =
      f t.1 + ∑ s, f s := by
  rfl

@[simp] theorem diamondOddAxisDualChannelEquiv_apply_S
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (f : PVec n k → V) :
    diamondOddAxisDualChannelEquiv V hn f diamondOddChannelS =
      ∑ s, f s := by
  rfl

@[simp] theorem diamondOddAxisDualChannelEquiv_apply_T
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (f : PVec n k → V)
    (t : DiamondOddAxisTail n k) :
    diamondOddAxisDualChannelEquiv V hn f (diamondOddChannelT t) =
      f t.1 + f (zeroVec : PVec n k) := by
  rfl

noncomputable def diamondOddAxisTailJ
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V] :
    (DiamondOddAxisTail n k → V) →ₗ[F]
      (DiamondOddAxisTail n k → V) :=
  oddValueTailJ (PVec n k) V (zeroVec : PVec n k)

@[simp] theorem diamondOddAxisTailJ_apply
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (u : DiamondOddAxisTail n k → V)
    (t : DiamondOddAxisTail n k) :
    diamondOddAxisTailJ V u t =
      u t + ∑ v, u v := by
  change
    oddValueTailJ (PVec n k) V (zeroVec : PVec n k) u t =
      u t + ∑ v, u v
  rw [oddValueTailJ_apply]
  congr 1
  apply Finset.sum_congr
  · ext v
    simp
  · intro v _
    rfl

@[simp] theorem diamondOddAxisTailJ_sq_apply
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (u : DiamondOddAxisTail n k → V) :
    diamondOddAxisTailJ V (diamondOddAxisTailJ V u) = u := by
  exact oddValueTailJ_sq_apply
    (zeroVec : PVec n k) (odd_card_PVec hn) u

noncomputable def diamondOddAxisChannelJ
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V] :
    (DiamondOddAxisChannel n k → V) →ₗ[F]
      (DiamondOddAxisChannel n k → V) where
  toFun u
    | none => u none
    | some t =>
        diamondOddAxisTailJ V (fun v => u (some v)) t
  map_add' u v := by
    funext q
    cases q with
    | none => rfl
    | some t =>
        simp only [Pi.add_apply, diamondOddAxisTailJ_apply,
          Finset.sum_add_distrib]
        abel
  map_smul' r u := by
    funext q
    cases q with
    | none => rfl
    | some t =>
        simp only [Pi.smul_apply, diamondOddAxisTailJ_apply,
          ← Finset.smul_sum, smul_add]
        rfl

@[simp] theorem diamondOddAxisChannelJ_apply_S
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (u : DiamondOddAxisChannel n k → V) :
    diamondOddAxisChannelJ V u diamondOddChannelS =
      u diamondOddChannelS := by
  rfl

@[simp] theorem diamondOddAxisChannelJ_apply_T
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (u : DiamondOddAxisChannel n k → V)
    (t : DiamondOddAxisTail n k) :
    diamondOddAxisChannelJ V u (diamondOddChannelT t) =
      diamondOddAxisTailJ V
        (fun v => u (diamondOddChannelT v)) t := by
  rfl

theorem diamondOddAxisDualChannel_eq_J_source
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (f : PVec n k → V) :
    diamondOddAxisDualChannelEquiv V hn f =
      diamondOddAxisChannelJ V
        (diamondOddAxisSrcChannelEquiv V hn f) := by
  funext q
  cases q with
  | none => rfl
  | some t =>
      change
        (pointedDualOddValueEquiv
          (PVec n k) V (zeroVec : PVec n k)
          (odd_card_PVec hn) f).2 t =
        oddValueTailJ
          (PVec n k) V (zeroVec : PVec n k)
          (pointedSrcOddValueEquiv
            (PVec n k) V (zeroVec : PVec n k)
            (odd_card_PVec hn) f).2 t
      exact congrFun
        (pointedDualOddValue_tail_eq_oddValueTailJ_source
          (zeroVec : PVec n k) (odd_card_PVec hn) f) t

noncomputable def diamondOddTensorTailJ
    {S T V : Type*} [Fintype S] [Fintype T]
    (s0 : S) (t0 : T)
    [AddCommGroup V] [Module F V]
    (f : PointedTail S s0 → PointedTail T t0 → V) :
    PointedTail S s0 → PointedTail T t0 → V :=
  oddValueTailJ S (PointedTail T t0 → V) s0
    (fun s => oddValueTailJ T V t0 (f s))

theorem diamondOddTensorTailJ_apply
    {S T V : Type*} [Fintype S] [Fintype T]
    (s0 : S) (t0 : T)
    [AddCommGroup V] [Module F V]
    (f : PointedTail S s0 → PointedTail T t0 → V)
    (s : PointedTail S s0) (t : PointedTail T t0) :
    diamondOddTensorTailJ s0 t0 f s t =
      f s t +
        (∑ t', f s t') +
        (∑ s', f s' t) +
        ∑ s', ∑ t', f s' t' := by
  simp only [diamondOddTensorTailJ, oddValueTailJ_apply,
    Finset.sum_apply, Pi.add_apply]
  rw [Finset.sum_add_distrib]
  abel

private theorem oddValueTailJ_commute
    {S T V : Type*} [Fintype S] [Fintype T]
    (s0 : S) (t0 : T)
    [AddCommGroup V] [Module F V]
    (f : PointedTail S s0 → PointedTail T t0 → V) :
    (fun s => oddValueTailJ T V t0
        (fun t =>
          oddValueTailJ S (PointedTail T t0 → V) s0 f s t)) =
      oddValueTailJ S (PointedTail T t0 → V) s0
        (fun s => oddValueTailJ T V t0 (f s)) := by
  funext s t
  simp only [oddValueTailJ_apply, Finset.sum_apply, Pi.add_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  abel

theorem diamondOddTensorTailJ_sq_apply
    {S T V : Type*} [Fintype S] [Fintype T]
    (s0 : S) (t0 : T)
    [AddCommGroup V] [Module F V]
    (hS : Odd (Fintype.card S))
    (hT : Odd (Fintype.card T))
    (f : PointedTail S s0 → PointedTail T t0 → V) :
    diamondOddTensorTailJ s0 t0
      (diamondOddTensorTailJ s0 t0 f) = f := by
  unfold diamondOddTensorTailJ
  rw [show
      (fun s =>
        oddValueTailJ T V t0
          (fun t =>
            oddValueTailJ S (PointedTail T t0 → V) s0
              (fun s' => oddValueTailJ T V t0 (f s')) s t)) =
        oddValueTailJ S (PointedTail T t0 → V) s0
          (fun s => oddValueTailJ T V t0
            (oddValueTailJ T V t0 (f s))) by
      exact oddValueTailJ_commute s0 t0
        (fun s => oddValueTailJ T V t0 (f s))]
  simp only [oddValueTailJ_sq_apply t0 hT]
  exact oddValueTailJ_sq_apply s0 hS f

/-! ## O1 — ambient and target transport -/

noncomputable def diamondOddTripleSrcChannelEquiv
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) :
    (PVec n k₁ → PVec n k₂ → PVec n k₃ → V) ≃ₗ[F]
      (DiamondOddAxisChannel n k₁ →
        DiamondOddAxisChannel n k₂ →
        DiamondOddAxisChannel n k₃ → V) :=
  (diamondOddAxisSrcChannelEquiv
      (PVec n k₂ → PVec n k₃ → V) hn).trans
    ((LinearEquiv.piCongrRight
        fun _ : DiamondOddAxisChannel n k₁ =>
          diamondOddAxisSrcChannelEquiv
            (PVec n k₃ → V) hn).trans
      (LinearEquiv.piCongrRight
        fun _ : DiamondOddAxisChannel n k₁ =>
          LinearEquiv.piCongrRight
            fun _ : DiamondOddAxisChannel n k₂ =>
              diamondOddAxisSrcChannelEquiv V hn))

abbrev DiamondOddAChannels
    (n b c d : Nat) [NeZero n] :=
  DiamondOddAxisChannel n b →
    DiamondOddAxisChannel n c →
      DiamondOddAxisChannel n d → CyclicCube n

abbrev DiamondOddBChannels
    (n a c d : Nat) [NeZero n] :=
  DiamondOddAxisChannel n a →
    DiamondOddAxisChannel n c →
      DiamondOddAxisChannel n d → CyclicCube n

abbrev DiamondOddWChannels
    (n a b c : Nat) [NeZero n] :=
  DiamondOddAxisChannel n a →
    DiamondOddAxisChannel n b →
      DiamondOddAxisChannel n c → CyclicCube n

abbrev DiamondOddPointedAmbient
    (n a b c d : Nat) [NeZero n] :=
  DiamondOddAChannels n b c d ×
    (DiamondOddBChannels n a c d ×
      DiamondOddWChannels n a b c)

abbrev DiamondOddPointedTarget
    (n a b d : Nat) [NeZero n] :=
  DiamondOddAxisChannel n a →
    DiamondOddAxisChannel n b →
      DiamondOddAxisChannel n d → CyclicCube n

noncomputable def diamondOddPointedAmbientEquiv
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddLiteralAmbient n a b c d ≃ₗ[F]
      DiamondOddPointedAmbient n a b c d :=
  LinearEquiv.prodCongr
    (diamondOddTripleSrcChannelEquiv
      (n := n) (CyclicCube n) hn)
    (LinearEquiv.prodCongr
      (diamondOddTripleSrcChannelEquiv
        (n := n) (CyclicCube n) hn)
      (diamondOddTripleSrcChannelEquiv
        (n := n) (CyclicCube n) hn))

@[simp] theorem diamondOddPointedAmbientEquiv_apply
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (u : DiamondOddLiteralAmbient n a b c d) :
    diamondOddPointedAmbientEquiv hn u =
      (diamondOddTripleSrcChannelEquiv
          (n := n) (CyclicCube n) hn u.1,
        diamondOddTripleSrcChannelEquiv
          (n := n) (CyclicCube n) hn u.2.1,
        diamondOddTripleSrcChannelEquiv
          (n := n) (CyclicCube n) hn u.2.2) := by
  rfl

@[simp] theorem diamondOddPointedAmbientEquiv_symm_apply
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedAmbient n a b c d) :
    (diamondOddPointedAmbientEquiv hn).symm v =
      ((diamondOddTripleSrcChannelEquiv
          (n := n) (CyclicCube n) hn).symm v.1,
        (diamondOddTripleSrcChannelEquiv
          (n := n) (CyclicCube n) hn).symm v.2.1,
        (diamondOddTripleSrcChannelEquiv
          (n := n) (CyclicCube n) hn).symm v.2.2) := by
  rfl

noncomputable def diamondOddPointedTargetEquiv
    {n a b d : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddLiteralTarget n a b d ≃ₗ[F]
      DiamondOddPointedTarget n a b d :=
  diamondOddTripleSrcChannelEquiv
    (n := n) (CyclicCube n) hn

/-! ## O2 — the single conjugated source map and its kernel -/

noncomputable def diamondOddPointedSourceMap
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddPointedAmbient n a b c d →ₗ[F]
      DiamondOddPointedTarget n a b d :=
  (diamondOddPointedTargetEquiv hn).toLinearMap.comp
    (diamondOddLiteralSourceMap.comp
      (diamondOddPointedAmbientEquiv hn).symm.toLinearMap)

@[simp] theorem diamondOddPointedSourceMap_conjugacy
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (u : DiamondOddLiteralAmbient n a b c d) :
    diamondOddPointedSourceMap hn
        (diamondOddPointedAmbientEquiv hn u) =
      diamondOddPointedTargetEquiv hn
        (diamondOddLiteralSourceMap u) := by
  simp [diamondOddPointedSourceMap]

private def diamondOddScalarOnly
    {T V : Type*} [Zero V] (r : Option T) (x : V) : V :=
  match r with
  | none => x
  | some _ => 0

private theorem oddValue_sum_const_eq_self
    {S V : Type*} [Fintype S]
    [AddCommGroup V] [Module F V]
    (hS : Odd (Fintype.card S)) (x : V) :
    (∑ _ : S, x) = x := by
  rcases hS with ⟨m, hm⟩
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F, hm]
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem diamondOddAxisSrcChannelEquiv_const
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (x : V) (q : DiamondOddAxisChannel n k) :
    diamondOddAxisSrcChannelEquiv V hn (fun _ => x) q =
      diamondOddScalarOnly q x := by
  cases q with
  | none =>
      change
        diamondOddAxisSrcChannelEquiv V hn (fun _ => x)
            diamondOddChannelS =
          diamondOddScalarOnly diamondOddChannelS x
      rw [diamondOddAxisSrcChannelEquiv_apply_S,
        oddValue_sum_const_eq_self (odd_card_PVec hn)]
      rfl
  | some t =>
      change
        diamondOddAxisSrcChannelEquiv V hn (fun _ => x)
            (diamondOddChannelT t) =
          diamondOddScalarOnly (diamondOddChannelT t) x
      rw [diamondOddAxisSrcChannelEquiv_apply_T,
        oddValue_sum_const_eq_self (odd_card_PVec hn)]
      change x + x = 0
      rw [← two_smul F x, show (2 : F) = 0 by decide, zero_smul]

private theorem diamondOddAxisSrcChannelEquiv_map
    {n k : Nat} [NeZero n]
    {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (hn : Odd n) (L : V →ₗ[F] W) (f : PVec n k → V)
    (q : DiamondOddAxisChannel n k) :
    diamondOddAxisSrcChannelEquiv W hn (fun s => L (f s)) q =
      L (diamondOddAxisSrcChannelEquiv V hn f q) := by
  cases q with
  | none =>
      change
        diamondOddAxisSrcChannelEquiv W hn (fun s => L (f s))
            diamondOddChannelS =
          L (diamondOddAxisSrcChannelEquiv V hn f
            diamondOddChannelS)
      rw [diamondOddAxisSrcChannelEquiv_apply_S,
        diamondOddAxisSrcChannelEquiv_apply_S, map_sum]
  | some t =>
      change
        diamondOddAxisSrcChannelEquiv W hn (fun s => L (f s))
            (diamondOddChannelT t) =
          L (diamondOddAxisSrcChannelEquiv V hn f
            (diamondOddChannelT t))
      rw [diamondOddAxisSrcChannelEquiv_apply_T,
        diamondOddAxisSrcChannelEquiv_apply_T, map_add, map_sum]

@[simp] private theorem diamondOddAxisSrcChannelEquiv_pi_apply
    {n k : Nat} [NeZero n]
    (X V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (f : PVec n k → X → V)
    (q : DiamondOddAxisChannel n k) (x : X) :
    diamondOddAxisSrcChannelEquiv (X → V) hn f q x =
      diamondOddAxisSrcChannelEquiv V hn (fun s => f s x) q := by
  cases q with
  | none =>
      change
        diamondOddAxisSrcChannelEquiv (X → V) hn f
            diamondOddChannelS x =
          diamondOddAxisSrcChannelEquiv V hn (fun s => f s x)
            diamondOddChannelS
      simp only [diamondOddAxisSrcChannelEquiv_apply_S,
        Finset.sum_apply]
  | some t =>
      change
        diamondOddAxisSrcChannelEquiv (X → V) hn f
            (diamondOddChannelT t) x =
          diamondOddAxisSrcChannelEquiv V hn (fun s => f s x)
            (diamondOddChannelT t)
      simp only [diamondOddAxisSrcChannelEquiv_apply_T,
        Pi.add_apply, Finset.sum_apply]

@[simp] private theorem diamondOddTripleSrcChannelEquiv_apply
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → PVec n k₃ → V)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₂ : DiamondOddAxisChannel n k₂)
    (q₃ : DiamondOddAxisChannel n k₃) :
    diamondOddTripleSrcChannelEquiv V hn f q₁ q₂ q₃ =
      diamondOddAxisSrcChannelEquiv V hn
        (diamondOddAxisSrcChannelEquiv
          (PVec n k₃ → V) hn
          (diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → PVec n k₃ → V) hn f q₁) q₂) q₃ := by
  rfl

private theorem diamondOddTriple_sum_middle
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → PVec n k₃ → V)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₃ : DiamondOddAxisChannel n k₃) :
    diamondOddTripleSrcChannelEquiv V hn f
        q₁ diamondOddChannelS q₃ =
      diamondOddAxisSrcChannelEquiv V hn
        (fun x₃ =>
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => ∑ x₂, f x₁ x₂ x₃) q₁) q₃ := by
  rw [diamondOddTripleSrcChannelEquiv_apply,
    diamondOddAxisSrcChannelEquiv_apply_S]
  apply congrArg
    (fun g : PVec n k₃ → V =>
      diamondOddAxisSrcChannelEquiv V hn g q₃)
  funext x₃
  cases q₁ with
  | none =>
      change
        (∑ x₂,
          diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → PVec n k₃ → V) hn f
              diamondOddChannelS x₂) x₃ =
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => ∑ x₂, f x₁ x₂ x₃)
              diamondOddChannelS
      simp only [diamondOddAxisSrcChannelEquiv_apply_S,
        Finset.sum_apply]
      rw [Finset.sum_comm]
  | some t =>
      change
        (∑ x₂,
          diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → PVec n k₃ → V) hn f
              (diamondOddChannelT t) x₂) x₃ =
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => ∑ x₂, f x₁ x₂ x₃)
              (diamondOddChannelT t)
      simp only [diamondOddAxisSrcChannelEquiv_apply_T,
        Finset.sum_apply, Pi.add_apply]
      rw [Finset.sum_add_distrib, Finset.sum_comm]

private theorem diamondOddDoubleSrcChannelEquiv_map
    {n k₁ k₂ : Nat} [NeZero n]
    {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (hn : Odd n) (L : V →ₗ[F] W)
    (f : PVec n k₁ → PVec n k₂ → V)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₂ : DiamondOddAxisChannel n k₂) :
    diamondOddAxisSrcChannelEquiv W hn
        (fun x₂ =>
          diamondOddAxisSrcChannelEquiv W hn
            (fun x₁ => L (f x₁ x₂)) q₁) q₂ =
      L (diamondOddAxisSrcChannelEquiv V hn
        (fun x₂ =>
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => f x₁ x₂) q₁) q₂) := by
  simp_rw [diamondOddAxisSrcChannelEquiv_map hn L]

private theorem diamondOddTriple_const_first
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (f : PVec n k₂ → PVec n k₃ → V)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₂ : DiamondOddAxisChannel n k₂)
    (q₃ : DiamondOddAxisChannel n k₃) :
    diamondOddTripleSrcChannelEquiv V hn
        (fun _ x₂ x₃ => f x₂ x₃) q₁ q₂ q₃ =
      diamondOddScalarOnly q₁
        (diamondOddAxisSrcChannelEquiv V hn
          (fun x₃ =>
            diamondOddAxisSrcChannelEquiv V hn
              (fun x₂ => f x₂ x₃) q₂) q₃) := by
  rw [diamondOddTripleSrcChannelEquiv_apply]
  rw [diamondOddAxisSrcChannelEquiv_const]
  have hpi :
      diamondOddAxisSrcChannelEquiv (PVec n k₃ → V) hn f q₂ =
        fun x₃ =>
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₂ => f x₂ x₃) q₂ := by
    funext x₃
    exact diamondOddAxisSrcChannelEquiv_pi_apply
      (PVec n k₃) V hn f q₂ x₃
  cases q₁ with
  | none =>
      change
        diamondOddAxisSrcChannelEquiv V hn
            (diamondOddAxisSrcChannelEquiv
              (PVec n k₃ → V) hn f q₂) q₃ =
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₃ =>
              diamondOddAxisSrcChannelEquiv V hn
                (fun x₂ => f x₂ x₃) q₂) q₃
      rw [hpi]
  | some t =>
      simp [diamondOddScalarOnly]

private theorem diamondOddTriple_const_middle
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (f : PVec n k₁ → PVec n k₃ → V)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₂ : DiamondOddAxisChannel n k₂)
    (q₃ : DiamondOddAxisChannel n k₃) :
    diamondOddTripleSrcChannelEquiv V hn
        (fun x₁ _ x₃ => f x₁ x₃) q₁ q₂ q₃ =
      diamondOddScalarOnly q₂
        (diamondOddAxisSrcChannelEquiv V hn
          (fun x₃ =>
            diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => f x₁ x₃) q₁) q₃) := by
  rw [diamondOddTripleSrcChannelEquiv_apply]
  have hconst :
      diamondOddAxisSrcChannelEquiv
          (PVec n k₃ → V) hn
          (diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → PVec n k₃ → V) hn
            (fun x₁ _ x₃ => f x₁ x₃) q₁) q₂ =
        diamondOddScalarOnly q₂
          (diamondOddAxisSrcChannelEquiv
            (PVec n k₃ → V) hn
            (fun x₁ x₃ => f x₁ x₃) q₁) := by
    have hfun :
        diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → PVec n k₃ → V) hn
            (fun x₁ _ x₃ => f x₁ x₃) q₁ =
          fun _ =>
            diamondOddAxisSrcChannelEquiv
              (PVec n k₃ → V) hn
              (fun x₁ x₃ => f x₁ x₃) q₁ := by
      funext x₂
      cases q₁ with
      | none =>
          change
            diamondOddAxisSrcChannelEquiv
                (PVec n k₂ → PVec n k₃ → V) hn
                (fun x₁ _ x₃ => f x₁ x₃) diamondOddChannelS x₂ =
              diamondOddAxisSrcChannelEquiv
                (PVec n k₃ → V) hn
                (fun x₁ x₃ => f x₁ x₃) diamondOddChannelS
          simp only [diamondOddAxisSrcChannelEquiv_apply_S,
            Finset.sum_apply]
      | some t =>
          change
            diamondOddAxisSrcChannelEquiv
                (PVec n k₂ → PVec n k₃ → V) hn
                (fun x₁ _ x₃ => f x₁ x₃)
                  (diamondOddChannelT t) x₂ =
              diamondOddAxisSrcChannelEquiv
                (PVec n k₃ → V) hn
                (fun x₁ x₃ => f x₁ x₃)
                  (diamondOddChannelT t)
          simp only [diamondOddAxisSrcChannelEquiv_apply_T,
            Pi.add_apply, Finset.sum_apply]
    rw [hfun, diamondOddAxisSrcChannelEquiv_const]
  rw [hconst]
  have hpi :
      diamondOddAxisSrcChannelEquiv
          (PVec n k₃ → V) hn
          (fun x₁ x₃ => f x₁ x₃) q₁ =
        fun x₃ =>
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => f x₁ x₃) q₁ := by
    funext x₃
    exact diamondOddAxisSrcChannelEquiv_pi_apply
      (PVec n k₃) V hn (fun x₁ x₃ => f x₁ x₃) q₁ x₃
  rw [hpi]
  cases q₂ <;> simp [diamondOddScalarOnly]

private theorem diamondOddTriple_const_last
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (f : PVec n k₁ → PVec n k₂ → V)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₂ : DiamondOddAxisChannel n k₂)
    (q₃ : DiamondOddAxisChannel n k₃) :
    diamondOddTripleSrcChannelEquiv V hn
        (fun x₁ x₂ _ => f x₁ x₂) q₁ q₂ q₃ =
      diamondOddScalarOnly q₃
        (diamondOddAxisSrcChannelEquiv V hn
          (fun x₂ =>
            diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => f x₁ x₂) q₁) q₂) := by
  rw [diamondOddTripleSrcChannelEquiv_apply]
  have hfun :
      diamondOddAxisSrcChannelEquiv
          (PVec n k₂ → PVec n k₃ → V) hn
          (fun x₁ x₂ _ => f x₁ x₂) q₁ =
        fun x₂ _ =>
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => f x₁ x₂) q₁ := by
    funext x₂ x₃
    cases q₁ with
    | none =>
        change
          diamondOddAxisSrcChannelEquiv
              (PVec n k₂ → PVec n k₃ → V) hn
              (fun x₁ x₂ _ => f x₁ x₂) diamondOddChannelS x₂ x₃ =
            diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => f x₁ x₂) diamondOddChannelS
        simp only [diamondOddAxisSrcChannelEquiv_apply_S,
          Finset.sum_apply]
    | some t =>
        change
          diamondOddAxisSrcChannelEquiv
              (PVec n k₂ → PVec n k₃ → V) hn
              (fun x₁ x₂ _ => f x₁ x₂)
                (diamondOddChannelT t) x₂ x₃ =
            diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => f x₁ x₂) (diamondOddChannelT t)
        simp only [diamondOddAxisSrcChannelEquiv_apply_T,
          Pi.add_apply, Finset.sum_apply]
  rw [hfun]
  have hfun₂ :
      diamondOddAxisSrcChannelEquiv
          (PVec n k₃ → V) hn
          (fun x₂ _ =>
            diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => f x₁ x₂) q₁) q₂ =
        fun _ =>
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₂ =>
              diamondOddAxisSrcChannelEquiv V hn
                (fun x₁ => f x₁ x₂) q₁) q₂ := by
    funext x₃
    cases q₂ with
    | none =>
        change
          diamondOddAxisSrcChannelEquiv
              (PVec n k₃ → V) hn _ diamondOddChannelS x₃ =
            diamondOddAxisSrcChannelEquiv V hn _
              diamondOddChannelS
        simp only [diamondOddAxisSrcChannelEquiv_apply_S,
          Finset.sum_apply]
    | some t =>
        change
          diamondOddAxisSrcChannelEquiv
              (PVec n k₃ → V) hn _ (diamondOddChannelT t) x₃ =
            diamondOddAxisSrcChannelEquiv V hn _
              (diamondOddChannelT t)
        simp only [diamondOddAxisSrcChannelEquiv_apply_T,
          Pi.add_apply, Finset.sum_apply]
  rw [hfun₂, diamondOddAxisSrcChannelEquiv_const]

private theorem diamondOddTriple_sum_last
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → PVec n k₃ → V)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₂ : DiamondOddAxisChannel n k₂) :
    diamondOddTripleSrcChannelEquiv V hn f
        q₁ q₂ diamondOddChannelS =
      diamondOddAxisSrcChannelEquiv V hn
        (fun x₂ =>
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => ∑ x₃, f x₁ x₂ x₃) q₁) q₂ := by
  rw [diamondOddTripleSrcChannelEquiv_apply,
    diamondOddAxisSrcChannelEquiv_apply_S]
  simp_rw [diamondOddAxisSrcChannelEquiv_pi_apply]
  cases q₂ with
  | none =>
      change
        (∑ x₃, ∑ x₂,
          diamondOddAxisSrcChannelEquiv V hn
            (fun x₁ => f x₁ x₂ x₃) q₁) =
          ∑ x₂,
            diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => ∑ x₃, f x₁ x₂ x₃) q₁
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x₂ _
      cases q₁ with
      | none =>
          change
            (∑ x₃, ∑ x₁, f x₁ x₂ x₃) =
              ∑ x₁, ∑ x₃, f x₁ x₂ x₃
          rw [Finset.sum_comm]
      | some t =>
          change
            (∑ x₃,
              (f t.1 x₂ x₃ + ∑ x₁, f x₁ x₂ x₃)) =
              (∑ x₃, f t.1 x₂ x₃) +
                ∑ x₁, ∑ x₃, f x₁ x₂ x₃
          rw [Finset.sum_add_distrib, Finset.sum_comm]
  | some t =>
      change
        (∑ x₃,
          (diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => f x₁ t.1 x₃) q₁ +
            ∑ x₂,
              diamondOddAxisSrcChannelEquiv V hn
                (fun x₁ => f x₁ x₂ x₃) q₁)) =
          diamondOddAxisSrcChannelEquiv V hn
              (fun x₁ => ∑ x₃, f x₁ t.1 x₃) q₁ +
            ∑ x₂,
              diamondOddAxisSrcChannelEquiv V hn
                (fun x₁ => ∑ x₃, f x₁ x₂ x₃) q₁
      rw [Finset.sum_add_distrib]
      congr 1
      · cases q₁ with
        | none =>
            change
              (∑ x₃, ∑ x₁, f x₁ t.1 x₃) =
                ∑ x₁, ∑ x₃, f x₁ t.1 x₃
            rw [Finset.sum_comm]
        | some u =>
            change
              (∑ x₃,
                (f u.1 t.1 x₃ + ∑ x₁, f x₁ t.1 x₃)) =
                (∑ x₃, f u.1 t.1 x₃) +
                  ∑ x₁, ∑ x₃, f x₁ t.1 x₃
            rw [Finset.sum_add_distrib, Finset.sum_comm]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x₂ _
        cases q₁ with
        | none =>
            change
              (∑ x₃, ∑ x₁, f x₁ x₂ x₃) =
                ∑ x₁, ∑ x₃, f x₁ x₂ x₃
            rw [Finset.sum_comm]
        | some u =>
            change
              (∑ x₃,
                (f u.1 x₂ x₃ + ∑ x₁, f x₁ x₂ x₃)) =
                (∑ x₃, f u.1 x₂ x₃) +
                  ∑ x₁, ∑ x₃, f x₁ x₂ x₃
            rw [Finset.sum_add_distrib, Finset.sum_comm]

private theorem diamondOddTriple_source_first
    {n k₀ k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (L : V →ₗ[F] V)
    (f : PVec n k₁ → PVec n k₂ → PVec n k₃ → V)
    (q₀ : DiamondOddAxisChannel n k₀)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₃ : DiamondOddAxisChannel n k₃) :
    diamondOddTripleSrcChannelEquiv V hn
        (fun _ x₁ x₃ => L (∑ x₂, f x₁ x₂ x₃))
        q₀ q₁ q₃ =
      diamondOddScalarOnly q₀
        (L (diamondOddTripleSrcChannelEquiv V hn f
          q₁ diamondOddChannelS q₃)) := by
  rw [diamondOddTriple_const_first]
  rw [diamondOddDoubleSrcChannelEquiv_map hn L]
  rw [← diamondOddTriple_sum_middle]

private theorem diamondOddTriple_source_middle
    {n k₀ k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (L : V →ₗ[F] V)
    (f : PVec n k₀ → PVec n k₂ → PVec n k₃ → V)
    (q₀ : DiamondOddAxisChannel n k₀)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₃ : DiamondOddAxisChannel n k₃) :
    diamondOddTripleSrcChannelEquiv V hn
        (fun x₀ _ x₃ => L (∑ x₂, f x₀ x₂ x₃))
        q₀ q₁ q₃ =
      diamondOddScalarOnly q₁
        (L (diamondOddTripleSrcChannelEquiv V hn f
          q₀ diamondOddChannelS q₃)) := by
  rw [diamondOddTriple_const_middle]
  rw [diamondOddDoubleSrcChannelEquiv_map hn L]
  rw [← diamondOddTriple_sum_middle]

private theorem diamondOddTriple_source_last
    {n k₀ k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) (L : V →ₗ[F] V)
    (f : PVec n k₀ → PVec n k₁ → PVec n k₂ → V)
    (q₀ : DiamondOddAxisChannel n k₀)
    (q₁ : DiamondOddAxisChannel n k₁)
    (q₃ : DiamondOddAxisChannel n k₃) :
    diamondOddTripleSrcChannelEquiv V hn
        (fun x₀ x₁ _ => L (∑ x₂, f x₀ x₁ x₂))
        q₀ q₁ q₃ =
      diamondOddScalarOnly q₃
        (L (diamondOddTripleSrcChannelEquiv V hn f
          q₀ q₁ diamondOddChannelS)) := by
  rw [diamondOddTriple_const_last]
  rw [diamondOddDoubleSrcChannelEquiv_map hn L]
  rw [← diamondOddTriple_sum_last]

theorem diamondOddPointedSourceMap_apply
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedAmbient n a b c d)
    (cp : DiamondOddAxisChannel n a)
    (cy : DiamondOddAxisChannel n b)
    (cw : DiamondOddAxisChannel n d) :
    diamondOddPointedSourceMap hn v cp cy cw =
      diamondOddScalarOnly cp
          (cubeDiffJInv
            (v.1 cy diamondOddChannelS cw)) +
        diamondOddScalarOnly cy
          (cubeDiffP
            (v.2.1 cp diamondOddChannelS cw)) +
        diamondOddScalarOnly cw
          (cubeDiffR
            (v.2.2 cp cy diamondOddChannelS)) := by
  let u := (diamondOddPointedAmbientEquiv hn).symm v
  have hv : diamondOddPointedAmbientEquiv hn u = v :=
    (diamondOddPointedAmbientEquiv hn).apply_symm_apply v
  rw [← hv, diamondOddPointedSourceMap_conjugacy,
    diamondOddPointedAmbientEquiv_apply]
  have hdecomp :
      diamondOddLiteralSourceMap u =
        (fun p y w =>
          cubeDiffJInv (∑ z, u.1 y z w)) +
        (fun p y w =>
          cubeDiffP (∑ z, u.2.1 p z w)) +
        (fun p y w =>
          cubeDiffR (∑ z, u.2.2 p y z)) := by
    funext p y w
    rw [diamondOddLiteralSourceMap_apply]
    rfl
  rw [hdecomp]
  change
    diamondOddTripleSrcChannelEquiv (CyclicCube n) hn
        (((fun p y w => cubeDiffJInv (∑ z, u.1 y z w)) +
          (fun p y w => cubeDiffP (∑ z, u.2.1 p z w))) +
          (fun p y w => cubeDiffR (∑ z, u.2.2 p y z)))
        cp cy cw = _
  rw [(diamondOddTripleSrcChannelEquiv
      (CyclicCube n) hn).map_add,
    (diamondOddTripleSrcChannelEquiv
      (CyclicCube n) hn).map_add]
  change
    diamondOddTripleSrcChannelEquiv (CyclicCube n) hn
          (fun p y w => cubeDiffJInv (∑ z, u.1 y z w)) cp cy cw +
        diamondOddTripleSrcChannelEquiv (CyclicCube n) hn
          (fun p y w => cubeDiffP (∑ z, u.2.1 p z w)) cp cy cw +
      diamondOddTripleSrcChannelEquiv (CyclicCube n) hn
          (fun p y w => cubeDiffR (∑ z, u.2.2 p y z)) cp cy cw = _
  rw [diamondOddTriple_source_first
      (CyclicCube n) hn cubeDiffJInv u.1 cp cy cw,
    diamondOddTriple_source_middle
      (CyclicCube n) hn cubeDiffP u.2.1 cp cy cw,
    diamondOddTriple_source_last
      (CyclicCube n) hn cubeDiffR u.2.2 cp cy cw]

theorem diamondOddPointedSourceMap_apply_SSSS
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedAmbient n a b c d) :
    diamondOddPointedSourceMap hn v
        diamondOddChannelS diamondOddChannelS diamondOddChannelS =
      cubeDiffJInv
          (v.1 diamondOddChannelS
            diamondOddChannelS diamondOddChannelS) +
        cubeDiffP
          (v.2.1 diamondOddChannelS
            diamondOddChannelS diamondOddChannelS) +
        cubeDiffR
          (v.2.2 diamondOddChannelS
            diamondOddChannelS diamondOddChannelS) := by
  rw [diamondOddPointedSourceMap_apply]
  dsimp only [diamondOddScalarOnly, diamondOddChannelS,
    diamondOddChannelT]

theorem diamondOddPointedSourceMap_apply_SSST
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedAmbient n a b c d)
    (wt : DiamondOddAxisTail n d) :
    diamondOddPointedSourceMap hn v
        diamondOddChannelS diamondOddChannelS (diamondOddChannelT wt) =
      cubeDiffJInv
          (v.1 diamondOddChannelS
            diamondOddChannelS (diamondOddChannelT wt)) +
        cubeDiffP
          (v.2.1 diamondOddChannelS
            diamondOddChannelS (diamondOddChannelT wt)) := by
  rw [diamondOddPointedSourceMap_apply]
  dsimp only [diamondOddScalarOnly, diamondOddChannelS,
    diamondOddChannelT]
  simp

theorem diamondOddPointedSourceMap_apply_STSS
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedAmbient n a b c d)
    (yt : DiamondOddAxisTail n b) :
    diamondOddPointedSourceMap hn v
        diamondOddChannelS (diamondOddChannelT yt) diamondOddChannelS =
      cubeDiffJInv
          (v.1 (diamondOddChannelT yt)
            diamondOddChannelS diamondOddChannelS) +
        cubeDiffR
          (v.2.2 diamondOddChannelS
            (diamondOddChannelT yt) diamondOddChannelS) := by
  rw [diamondOddPointedSourceMap_apply]
  dsimp only [diamondOddScalarOnly, diamondOddChannelS,
    diamondOddChannelT]
  simp

theorem diamondOddPointedSourceMap_apply_STST
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedAmbient n a b c d)
    (yt : DiamondOddAxisTail n b)
    (wt : DiamondOddAxisTail n d) :
    diamondOddPointedSourceMap hn v
        diamondOddChannelS (diamondOddChannelT yt)
          (diamondOddChannelT wt) =
      cubeDiffJInv
        (v.1 (diamondOddChannelT yt)
          diamondOddChannelS (diamondOddChannelT wt)) := by
  rw [diamondOddPointedSourceMap_apply]
  dsimp only [diamondOddScalarOnly, diamondOddChannelS,
    diamondOddChannelT]
  simp

theorem diamondOddPointedSourceMap_apply_TSSS
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedAmbient n a b c d)
    (pt : DiamondOddAxisTail n a) :
    diamondOddPointedSourceMap hn v
        (diamondOddChannelT pt) diamondOddChannelS diamondOddChannelS =
      cubeDiffP
          (v.2.1 (diamondOddChannelT pt)
            diamondOddChannelS diamondOddChannelS) +
        cubeDiffR
          (v.2.2 (diamondOddChannelT pt)
            diamondOddChannelS diamondOddChannelS) := by
  rw [diamondOddPointedSourceMap_apply]
  dsimp only [diamondOddScalarOnly, diamondOddChannelS,
    diamondOddChannelT]
  simp

theorem diamondOddPointedSourceMap_apply_TSST
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedAmbient n a b c d)
    (pt : DiamondOddAxisTail n a)
    (wt : DiamondOddAxisTail n d) :
    diamondOddPointedSourceMap hn v
        (diamondOddChannelT pt) diamondOddChannelS
          (diamondOddChannelT wt) =
      cubeDiffP
        (v.2.1 (diamondOddChannelT pt)
          diamondOddChannelS (diamondOddChannelT wt)) := by
  rw [diamondOddPointedSourceMap_apply]
  dsimp only [diamondOddScalarOnly, diamondOddChannelS,
    diamondOddChannelT]
  simp

theorem diamondOddPointedSourceMap_apply_TTSS
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedAmbient n a b c d)
    (pt : DiamondOddAxisTail n a)
    (yt : DiamondOddAxisTail n b) :
    diamondOddPointedSourceMap hn v
        (diamondOddChannelT pt) (diamondOddChannelT yt)
          diamondOddChannelS =
      cubeDiffR
        (v.2.2 (diamondOddChannelT pt)
          (diamondOddChannelT yt) diamondOddChannelS) := by
  rw [diamondOddPointedSourceMap_apply]
  dsimp only [diamondOddScalarOnly, diamondOddChannelS,
    diamondOddChannelT]
  simp

theorem diamondOddPointedSourceMap_apply_TTST
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedAmbient n a b c d)
    (pt : DiamondOddAxisTail n a)
    (yt : DiamondOddAxisTail n b)
    (wt : DiamondOddAxisTail n d) :
    diamondOddPointedSourceMap hn v
        (diamondOddChannelT pt) (diamondOddChannelT yt)
          (diamondOddChannelT wt) = 0 := by
  rw [diamondOddPointedSourceMap_apply]
  dsimp only [diamondOddScalarOnly, diamondOddChannelS,
    diamondOddChannelT]
  simp

noncomputable abbrev DiamondOddPointedSource
    (n a b c d : Nat) [NeZero n] (hn : Odd n) :=
  LinearMap.ker
    (diamondOddPointedSourceMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hn)

noncomputable def diamondOddLiteralPointedSourceEquiv
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddLiteralSource n a b c d ≃ₗ[F]
      DiamondOddPointedSource n a b c d hn where
  toFun u :=
    ⟨diamondOddPointedAmbientEquiv hn u.1,
      LinearMap.mem_ker.mpr (by
        rw [diamondOddPointedSourceMap_conjugacy]
        rw [LinearMap.mem_ker.mp u.2]
        exact (diamondOddPointedTargetEquiv hn).map_zero)⟩
  invFun v :=
    ⟨(diamondOddPointedAmbientEquiv hn).symm v.1,
      LinearMap.mem_ker.mpr (by
        apply (diamondOddPointedTargetEquiv hn).injective
        rw [(diamondOddPointedTargetEquiv hn).map_zero]
        rw [← diamondOddPointedSourceMap_conjugacy]
        rw [(diamondOddPointedAmbientEquiv hn).apply_symm_apply]
        exact LinearMap.mem_ker.mp v.2)⟩
  left_inv u := by
    apply Subtype.ext
    exact (diamondOddPointedAmbientEquiv hn).symm_apply_apply u.1
  right_inv v := by
    apply Subtype.ext
    exact (diamondOddPointedAmbientEquiv hn).apply_symm_apply v.1
  map_add' u v := by
    apply Subtype.ext
    exact (diamondOddPointedAmbientEquiv hn).map_add u.1 v.1
  map_smul' r u := by
    apply Subtype.ext
    exact (diamondOddPointedAmbientEquiv hn).map_smul r u.1

@[simp] theorem diamondOddLiteralPointedSourceEquiv_apply
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (u : DiamondOddLiteralSource n a b c d) :
    (diamondOddLiteralPointedSourceEquiv hn u).1 =
      diamondOddPointedAmbientEquiv hn u.1 := by
  rfl

@[simp] theorem diamondOddLiteralPointedSourceEquiv_symm_apply
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (v : DiamondOddPointedSource n a b c d hn) :
    ((diamondOddLiteralPointedSourceEquiv hn).symm v).1 =
      (diamondOddPointedAmbientEquiv hn).symm v.1 := by
  rfl

noncomputable def diamondOddPreCPointedSourceEquiv
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) :
    DiamondPreCSource n a b c d ≃ₗ[F]
      DiamondOddPointedSource n a b c d hn :=
  (diamondOddLiteralSourceEquiv hb hc hd).trans
    (diamondOddLiteralPointedSourceEquiv hn)

@[simp] theorem diamondOddPreCPointedSourceEquiv_apply
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) (x : DiamondPreCSource n a b c d) :
    diamondOddPreCPointedSourceEquiv hb hc hd hn x =
      diamondOddLiteralPointedSourceEquiv hn
        (diamondOddLiteralSourceEquiv hb hc hd x) := by
  rfl

/-! ## O3 — six direct-orientation phase blocks -/

noncomputable def diamondOddCubeDotBilin
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n →ₗ[F] F where
  toFun x :=
    { toFun := fun y => cubeDot x y
      map_add' := by
        intro y z
        simp only [cubeDot, Pi.add_apply, mul_add,
          Finset.sum_add_distrib]
      map_smul' := by
        intro r y
        simp only [cubeDot, Pi.smul_apply, smul_eq_mul]
        calc
          (∑ q : I n × I n × I n,
              x q.1 q.2.1 q.2.2 *
                (r * y q.1 q.2.1 q.2.2)) =
              ∑ q : I n × I n × I n,
                r * (x q.1 q.2.1 q.2.2 *
                  y q.1 q.2.1 q.2.2) := by
                    apply Finset.sum_congr rfl
                    intro q _
                    ring
          _ = r * ∑ q : I n × I n × I n,
                x q.1 q.2.1 q.2.2 *
                  y q.1 q.2.1 q.2.2 :=
            (Finset.mul_sum _ _ _).symm }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change cubeDot (x + y) z = cubeDot x z + cubeDot y z
    simp only [cubeDot, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    change cubeDot (r • x) y = r • cubeDot x y
    simp only [cubeDot, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ q : I n × I n × I n,
          r * x q.1 q.2.1 q.2.2 *
            y q.1 q.2.1 q.2.2) =
          ∑ q : I n × I n × I n,
            r * (x q.1 q.2.1 q.2.2 *
              y q.1 q.2.1 q.2.2) := by
                apply Finset.sum_congr rfl
                intro q _
                ring
      _ = r * ∑ q : I n × I n × I n,
            x q.1 q.2.1 q.2.2 *
              y q.1 q.2.1 q.2.2 :=
        (Finset.mul_sum _ _ _).symm

private theorem diamondOddAxis_pairing
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (beta : V →ₗ[F] V →ₗ[F] F)
    (f g : PVec n k → V) :
    (∑ s, beta (f s) (g s)) =
      beta
          (diamondOddAxisSrcChannelEquiv V hn f diamondOddChannelS)
          (diamondOddAxisSrcChannelEquiv V hn g diamondOddChannelS) +
        ∑ t : DiamondOddAxisTail n k,
          beta
            (diamondOddAxisSrcChannelEquiv V hn f
              (diamondOddChannelT t))
            (diamondOddAxisTailJ V
              (fun v =>
                diamondOddAxisSrcChannelEquiv V hn g
                  (diamondOddChannelT v)) t) := by
  rw [pointedOddValue_pairing_source_J
    (zeroVec : PVec n k) (odd_card_PVec hn) beta f g]
  congr 1
  refine @Fintype.sum_equiv
    (DiamondOddAxisTail n k) (DiamondOddAxisTail n k) F
    ?_ ?_ ?_ (Equiv.refl _) _ _ ?_
  intro t
  congr 1

private theorem diamondOddAxisSrc_tailJ_comm
    {n k₁ k₂ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (g : DiamondOddAxisTail n k₁ → PVec n k₂ → V)
    (t₁ : DiamondOddAxisTail n k₁)
    (c₂ : DiamondOddAxisChannel n k₂) :
    diamondOddAxisSrcChannelEquiv V hn
        (diamondOddAxisTailJ (PVec n k₂ → V) g t₁) c₂ =
      diamondOddAxisTailJ V
        (fun v =>
          diamondOddAxisSrcChannelEquiv V hn (g v) c₂) t₁ := by
  rw [diamondOddAxisTailJ_apply, diamondOddAxisTailJ_apply]
  simp only [map_add, map_sum, Pi.add_apply, Finset.sum_apply]

private noncomputable def diamondOddSumPiBilin
    (S V : Type*) [Fintype S]
    [AddCommGroup V] [Module F V]
    (beta : V →ₗ[F] V →ₗ[F] F) :
    (S → V) →ₗ[F] (S → V) →ₗ[F] F where
  toFun f :=
    { toFun := fun g => ∑ s, beta (f s) (g s)
      map_add' := by
        intro g h
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r g
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply,
          Finset.smul_sum] }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro h
    change
      (∑ s, beta (f s + g s) (h s)) =
        (∑ s, beta (f s) (h s)) + ∑ s, beta (g s) (h s)
    simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  map_smul' := by
    intro r f
    apply LinearMap.ext
    intro g
    change
      (∑ s, beta (r • f s) (g s)) =
        r • ∑ s, beta (f s) (g s)
    simp only [map_smul, LinearMap.smul_apply,
      Finset.smul_sum]

private noncomputable def diamondOddTwoSrc
    {n k₁ k₂ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → V)
    (c₁ : DiamondOddAxisChannel n k₁)
    (c₂ : DiamondOddAxisChannel n k₂) : V :=
  diamondOddAxisSrcChannelEquiv V hn
    (diamondOddAxisSrcChannelEquiv (PVec n k₂ → V) hn f c₁) c₂

private theorem diamondOddTailJ_commute
    {n k₁ k₂ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (f : DiamondOddAxisTail n k₁ → DiamondOddAxisTail n k₂ → V)
    (t₁ : DiamondOddAxisTail n k₁)
    (t₂ : DiamondOddAxisTail n k₂) :
    diamondOddAxisTailJ V
        (fun v₂ =>
          diamondOddAxisTailJ V (fun v₁ => f v₁ v₂) t₁) t₂ =
      diamondOddTensorTailJ
        (zeroVec : PVec n k₁) (zeroVec : PVec n k₂)
        f t₁ t₂ := by
  simp only [diamondOddAxisTailJ, diamondOddTensorTailJ,
    oddValueTailJ_apply, Pi.add_apply, Finset.sum_apply,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  abel_nf

private theorem diamondOddTwo_axis_pairing
    {n k₁ k₂ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (beta : V →ₗ[F] V →ₗ[F] F)
    (f g : PVec n k₁ → PVec n k₂ → V) :
    (∑ s₁, ∑ s₂, beta (f s₁ s₂) (g s₁ s₂)) =
      beta
          (diamondOddTwoSrc V hn f
            diamondOddChannelS diamondOddChannelS)
          (diamondOddTwoSrc V hn g
            diamondOddChannelS diamondOddChannelS) +
        (∑ t₂ : DiamondOddAxisTail n k₂,
          beta
            (diamondOddTwoSrc V hn f diamondOddChannelS
              (diamondOddChannelT t₂))
            (diamondOddAxisTailJ V
              (fun v =>
                diamondOddTwoSrc V hn g diamondOddChannelS
                  (diamondOddChannelT v)) t₂)) +
        (∑ t₁ : DiamondOddAxisTail n k₁,
          beta
            (diamondOddTwoSrc V hn f (diamondOddChannelT t₁)
              diamondOddChannelS)
            (diamondOddAxisTailJ V
              (fun v =>
                diamondOddTwoSrc V hn g (diamondOddChannelT v)
                  diamondOddChannelS) t₁)) +
        ∑ t₁ : DiamondOddAxisTail n k₁,
          ∑ t₂ : DiamondOddAxisTail n k₂,
            beta
              (diamondOddTwoSrc V hn f (diamondOddChannelT t₁)
                (diamondOddChannelT t₂))
              (diamondOddTensorTailJ
                (zeroVec : PVec n k₁) (zeroVec : PVec n k₂)
                (fun v₁ v₂ =>
                  diamondOddTwoSrc V hn g (diamondOddChannelT v₁)
                    (diamondOddChannelT v₂)) t₁ t₂) := by
  change
    (∑ s₁,
      (diamondOddSumPiBilin (PVec n k₂) V beta (f s₁)) (g s₁)) = _
  rw [diamondOddAxis_pairing
    (V := PVec n k₂ → V) hn
    (diamondOddSumPiBilin (PVec n k₂) V beta) f g]
  change
    (∑ s₂,
        beta
          ((diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → V) hn f diamondOddChannelS) s₂)
          ((diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → V) hn g diamondOddChannelS) s₂)) +
      (∑ t₁ : DiamondOddAxisTail n k₁,
        ∑ s₂,
          beta
            ((diamondOddAxisSrcChannelEquiv
              (PVec n k₂ → V) hn f
                (diamondOddChannelT t₁)) s₂)
            ((diamondOddAxisTailJ (PVec n k₂ → V)
              (fun v =>
                diamondOddAxisSrcChannelEquiv
                  (PVec n k₂ → V) hn g
                    (diamondOddChannelT v)) t₁) s₂)) = _
  rw [diamondOddAxis_pairing V hn beta
    (diamondOddAxisSrcChannelEquiv
      (PVec n k₂ → V) hn f diamondOddChannelS)
    (diamondOddAxisSrcChannelEquiv
      (PVec n k₂ → V) hn g diamondOddChannelS)]
  simp only [diamondOddTwoSrc]
  abel_nf
  rw [add_right_inj, add_right_inj]
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_equiv (Equiv.refl _) _ _ ?_
  intro t₁
  rw [diamondOddAxis_pairing V hn beta
    (diamondOddAxisSrcChannelEquiv
      (PVec n k₂ → V) hn f (diamondOddChannelT t₁))
    (diamondOddAxisTailJ (PVec n k₂ → V)
      (fun v =>
        diamondOddAxisSrcChannelEquiv
          (PVec n k₂ → V) hn g (diamondOddChannelT v)) t₁)]
  rw [diamondOddAxisSrc_tailJ_comm]
  congr 1
  apply Fintype.sum_equiv (Equiv.refl _) _ _ ?_
  intro t₂
  congr 1
  have hfun :
      (fun v₂ =>
        diamondOddAxisSrcChannelEquiv V hn
          (diamondOddAxisTailJ (PVec n k₂ → V)
            (fun v₁ =>
              diamondOddAxisSrcChannelEquiv
                (PVec n k₂ → V) hn g (diamondOddChannelT v₁)) t₁)
          (diamondOddChannelT v₂)) =
        (fun v₂ =>
          diamondOddAxisTailJ V
            (fun v₁ =>
              diamondOddTwoSrc V hn g (diamondOddChannelT v₁)
                (diamondOddChannelT v₂)) t₁) := by
    funext v₂
    simpa only [diamondOddTwoSrc] using
      diamondOddAxisSrc_tailJ_comm V hn
        (fun v₁ =>
          diamondOddAxisSrcChannelEquiv
            (PVec n k₂ → V) hn g (diamondOddChannelT v₁))
        t₁ (diamondOddChannelT v₂)
  rw [hfun]
  exact diamondOddTailJ_commute V
    (fun v₁ v₂ =>
      diamondOddTwoSrc V hn g (diamondOddChannelT v₁)
        (diamondOddChannelT v₂)) t₁ t₂

private theorem diamondOddTwoSrc_sum_first
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → PVec n k₃ → V)
    (c₂ : DiamondOddAxisChannel n k₂)
    (c₃ : DiamondOddAxisChannel n k₃) :
    diamondOddTwoSrc V hn
        (fun x₂ x₃ => ∑ x₁, f x₁ x₂ x₃) c₂ c₃ =
      diamondOddTripleSrcChannelEquiv V hn f
        diamondOddChannelS c₂ c₃ := by
  rw [diamondOddTripleSrcChannelEquiv_apply,
    diamondOddAxisSrcChannelEquiv_apply_S]
  unfold diamondOddTwoSrc
  apply congrArg
    (fun g : PVec n k₃ → V =>
      diamondOddAxisSrcChannelEquiv V hn g c₃)
  apply congrArg
    (fun g : PVec n k₂ → PVec n k₃ → V =>
      diamondOddAxisSrcChannelEquiv (PVec n k₃ → V) hn g c₂)
  funext x₂ x₃
  simp only [Finset.sum_apply]

private theorem diamondOddTwoSrc_sum_last
    {n k₁ k₂ k₃ : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n)
    (f : PVec n k₁ → PVec n k₂ → PVec n k₃ → V)
    (c₁ : DiamondOddAxisChannel n k₁)
    (c₂ : DiamondOddAxisChannel n k₂) :
    diamondOddTwoSrc V hn
        (fun x₁ x₂ => ∑ x₃, f x₁ x₂ x₃) c₁ c₂ =
      diamondOddTripleSrcChannelEquiv V hn f
        c₁ c₂ diamondOddChannelS := by
  rw [diamondOddTriple_sum_last]
  unfold diamondOddTwoSrc
  apply congrArg
    (fun g : PVec n k₂ → V =>
      diamondOddAxisSrcChannelEquiv V hn g c₂)
  funext x₂
  exact diamondOddAxisSrcChannelEquiv_pi_apply
    (PVec n k₂) V hn
      (fun x₁ x₂ => ∑ x₃, f x₁ x₂ x₃) c₁ x₂

private noncomputable def diamondOddCubeDotDiffIBilin
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n →ₗ[F] F where
  toFun x := (diamondOddCubeDotBilin x).comp cubeDiffI
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change cubeDot (x + y) (cubeDiffI z) =
      cubeDot x (cubeDiffI z) + cubeDot y (cubeDiffI z)
    simp only [cubeDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro z
    change cubeDot (r • x) (cubeDiffI z) =
      r • cubeDot x (cubeDiffI z)
    simp only [cubeDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]

@[simp] private theorem diamondOddCubeDotDiffIBilin_apply
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    diamondOddCubeDotDiffIBilin x y =
      cubeDot x (cubeDiffI y) := by
  rfl

private noncomputable def diamondOddCubeDotDiffKBilin
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n →ₗ[F] F where
  toFun x := (diamondOddCubeDotBilin x).comp cubeDiffK
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change cubeDot (x + y) (cubeDiffK z) =
      cubeDot x (cubeDiffK z) + cubeDot y (cubeDiffK z)
    simp only [cubeDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro z
    change cubeDot (r • x) (cubeDiffK z) =
      r • cubeDot x (cubeDiffK z)
    simp only [cubeDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]

@[simp] private theorem diamondOddCubeDotDiffKBilin_apply
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    diamondOddCubeDotDiffKBilin x y =
      cubeDot x (cubeDiffK y) := by
  rfl

private theorem diamondOddLiteralB_pairing
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (u : DiamondOddLiteralAmbient n a b c d) :
    (∑ z : PVec n c, ∑ w : PVec n d,
      cubeDot (∑ y : PVec n b, u.1 y z w)
        (cubeDiffI (∑ p : PVec n a, u.2.1 p z w))) =
      cubeDot
          (diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.1
            diamondOddChannelS diamondOddChannelS diamondOddChannelS)
          (cubeDiffI
            (diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.1
              diamondOddChannelS diamondOddChannelS diamondOddChannelS)) +
        (∑ wt : DiamondOddAxisTail n d,
          cubeDot
            (diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.1
              diamondOddChannelS diamondOddChannelS
                (diamondOddChannelT wt))
            (cubeDiffI
              (diamondOddAxisTailJ (CyclicCube n)
                (fun wt' =>
                  diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.1
                    diamondOddChannelS diamondOddChannelS
                      (diamondOddChannelT wt')) wt))) +
        (∑ zt : DiamondOddAxisTail n c,
          cubeDot
            (diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.1
              diamondOddChannelS (diamondOddChannelT zt)
                diamondOddChannelS)
            (cubeDiffI
              (diamondOddAxisTailJ (CyclicCube n)
                (fun zt' =>
                  diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.1
                    diamondOddChannelS (diamondOddChannelT zt')
                      diamondOddChannelS) zt))) +
        ∑ zt : DiamondOddAxisTail n c,
          ∑ wt : DiamondOddAxisTail n d,
            cubeDot
              (diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.1
                diamondOddChannelS (diamondOddChannelT zt)
                  (diamondOddChannelT wt))
              (cubeDiffI
                (diamondOddTensorTailJ
                  (zeroVec : PVec n c) (zeroVec : PVec n d)
                  (fun zt' wt' =>
                    diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.1
                      diamondOddChannelS (diamondOddChannelT zt')
                        (diamondOddChannelT wt')) zt wt)) := by
  change
    (∑ z : PVec n c, ∑ w : PVec n d,
      diamondOddCubeDotDiffIBilin
        (∑ y : PVec n b, u.1 y z w)
        (∑ p : PVec n a, u.2.1 p z w)) = _
  rw [diamondOddTwo_axis_pairing
    (CyclicCube n) hn diamondOddCubeDotDiffIBilin
    (fun z w => ∑ y, u.1 y z w)
    (fun z w => ∑ p, u.2.1 p z w)]
  simp only [diamondOddCubeDotDiffIBilin_apply]
  simp_rw [diamondOddTwoSrc_sum_first]

private theorem diamondOddLiteralW_pairing
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (u : DiamondOddLiteralAmbient n a b c d) :
    (∑ y : PVec n b, ∑ z : PVec n c,
      cubeDot (∑ w : PVec n d, u.1 y z w)
        (cubeDiffK (∑ p : PVec n a, u.2.2 p y z))) =
      cubeDot
          (diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.1
            diamondOddChannelS diamondOddChannelS diamondOddChannelS)
          (cubeDiffK
            (diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.2
              diamondOddChannelS diamondOddChannelS diamondOddChannelS)) +
        (∑ zt : DiamondOddAxisTail n c,
          cubeDot
            (diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.1
              diamondOddChannelS (diamondOddChannelT zt)
                diamondOddChannelS)
            (cubeDiffK
              (diamondOddAxisTailJ (CyclicCube n)
                (fun zt' =>
                  diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.2
                    diamondOddChannelS diamondOddChannelS
                      (diamondOddChannelT zt')) zt))) +
        (∑ yt : DiamondOddAxisTail n b,
          cubeDot
            (diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.1
              (diamondOddChannelT yt) diamondOddChannelS
                diamondOddChannelS)
            (cubeDiffK
              (diamondOddAxisTailJ (CyclicCube n)
                (fun yt' =>
                  diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.2
                    diamondOddChannelS (diamondOddChannelT yt')
                      diamondOddChannelS) yt))) +
        ∑ yt : DiamondOddAxisTail n b,
          ∑ zt : DiamondOddAxisTail n c,
            cubeDot
              (diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.1
                (diamondOddChannelT yt) (diamondOddChannelT zt)
                  diamondOddChannelS)
              (cubeDiffK
                (diamondOddTensorTailJ
                  (zeroVec : PVec n b) (zeroVec : PVec n c)
                  (fun yt' zt' =>
                    diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.2
                      diamondOddChannelS (diamondOddChannelT yt')
                        (diamondOddChannelT zt')) yt zt)) := by
  change
    (∑ y : PVec n b, ∑ z : PVec n c,
      diamondOddCubeDotDiffKBilin
        (∑ w : PVec n d, u.1 y z w)
        (∑ p : PVec n a, u.2.2 p y z)) = _
  rw [diamondOddTwo_axis_pairing
    (CyclicCube n) hn diamondOddCubeDotDiffKBilin
    (fun y z => ∑ w, u.1 y z w)
    (fun y z => ∑ p, u.2.2 p y z)]
  simp only [diamondOddCubeDotDiffKBilin_apply]
  have hU
      (c₁ : DiamondOddAxisChannel n b)
      (c₂ : DiamondOddAxisChannel n c) :
      diamondOddTwoSrc (CyclicCube n) hn
          (fun y z => ∑ w, u.1 y z w) c₁ c₂ =
        diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.1
          c₁ c₂ diamondOddChannelS :=
    diamondOddTwoSrc_sum_last (CyclicCube n) hn u.1 c₁ c₂
  have hV
      (c₁ : DiamondOddAxisChannel n b)
      (c₂ : DiamondOddAxisChannel n c) :
      diamondOddTwoSrc (CyclicCube n) hn
          (fun y z => ∑ p, u.2.2 p y z) c₁ c₂ =
        diamondOddTripleSrcChannelEquiv (CyclicCube n) hn u.2.2
          diamondOddChannelS c₁ c₂ :=
    diamondOddTwoSrc_sum_first (CyclicCube n) hn u.2.2 c₁ c₂
  simp_rw [hU, hV]

noncomputable def diamondOddPointedPhaseSSSS
    {n a b c d : Nat} [NeZero n]
    (v : DiamondOddPointedAmbient n a b c d) : F :=
  cubeDot
    (v.1 diamondOddChannelS diamondOddChannelS diamondOddChannelS)
    (cubeDiffI
        (v.2.1 diamondOddChannelS
          diamondOddChannelS diamondOddChannelS) +
      cubeDiffK
        (v.2.2 diamondOddChannelS
          diamondOddChannelS diamondOddChannelS))

noncomputable def diamondOddPointedPhaseSSST
    {n a b c d : Nat} [NeZero n]
    (v : DiamondOddPointedAmbient n a b c d) : F :=
  ∑ wt : DiamondOddAxisTail n d,
    cubeDot
      (v.1 diamondOddChannelS diamondOddChannelS
        (diamondOddChannelT wt))
      (cubeDiffI
        (diamondOddAxisTailJ (CyclicCube n)
          (fun wt' =>
            v.2.1 diamondOddChannelS diamondOddChannelS
              (diamondOddChannelT wt')) wt))

noncomputable def diamondOddPointedPhaseSSTS
    {n a b c d : Nat} [NeZero n]
    (v : DiamondOddPointedAmbient n a b c d) : F :=
  ∑ zt : DiamondOddAxisTail n c,
    cubeDot
      (v.1 diamondOddChannelS (diamondOddChannelT zt)
        diamondOddChannelS)
      (cubeDiffI
          (diamondOddAxisTailJ (CyclicCube n)
            (fun zt' =>
              v.2.1 diamondOddChannelS (diamondOddChannelT zt')
                diamondOddChannelS) zt) +
        cubeDiffK
          (diamondOddAxisTailJ (CyclicCube n)
            (fun zt' =>
              v.2.2 diamondOddChannelS diamondOddChannelS
                (diamondOddChannelT zt')) zt))

noncomputable def diamondOddPointedPhaseSSTT
    {n a b c d : Nat} [NeZero n]
    (v : DiamondOddPointedAmbient n a b c d) : F :=
  ∑ zt : DiamondOddAxisTail n c,
    ∑ wt : DiamondOddAxisTail n d,
      cubeDot
        (v.1 diamondOddChannelS (diamondOddChannelT zt)
          (diamondOddChannelT wt))
        (cubeDiffI
          (diamondOddTensorTailJ
            (zeroVec : PVec n c) (zeroVec : PVec n d)
            (fun zt' wt' =>
              v.2.1 diamondOddChannelS (diamondOddChannelT zt')
                (diamondOddChannelT wt')) zt wt))

noncomputable def diamondOddPointedPhaseSTSS
    {n a b c d : Nat} [NeZero n]
    (v : DiamondOddPointedAmbient n a b c d) : F :=
  ∑ yt : DiamondOddAxisTail n b,
    cubeDot
      (v.1 (diamondOddChannelT yt) diamondOddChannelS
        diamondOddChannelS)
      (cubeDiffK
        (diamondOddAxisTailJ (CyclicCube n)
          (fun yt' =>
            v.2.2 diamondOddChannelS (diamondOddChannelT yt')
              diamondOddChannelS) yt))

noncomputable def diamondOddPointedPhaseSTTS
    {n a b c d : Nat} [NeZero n]
    (v : DiamondOddPointedAmbient n a b c d) : F :=
  ∑ yt : DiamondOddAxisTail n b,
    ∑ zt : DiamondOddAxisTail n c,
      cubeDot
        (v.1 (diamondOddChannelT yt) (diamondOddChannelT zt)
          diamondOddChannelS)
        (cubeDiffK
          (diamondOddTensorTailJ
            (zeroVec : PVec n b) (zeroVec : PVec n c)
            (fun yt' zt' =>
              v.2.2 diamondOddChannelS (diamondOddChannelT yt')
                (diamondOddChannelT zt')) yt zt))

noncomputable def diamondOddPointedAmbientQ
    {n a b c d : Nat} [NeZero n]
    (v : DiamondOddPointedAmbient n a b c d) : F :=
  diamondOddPointedPhaseSSSS v +
    diamondOddPointedPhaseSSST v +
    diamondOddPointedPhaseSSTS v +
    diamondOddPointedPhaseSSTT v +
    diamondOddPointedPhaseSTSS v +
    diamondOddPointedPhaseSTTS v

@[simp] theorem diamondOddPointedAmbientQ_apply
    {n a b c d : Nat} [NeZero n]
    (v : DiamondOddPointedAmbient n a b c d) :
    diamondOddPointedAmbientQ v =
      diamondOddPointedPhaseSSSS v +
        diamondOddPointedPhaseSSST v +
        diamondOddPointedPhaseSSTS v +
        diamondOddPointedPhaseSSTT v +
        diamondOddPointedPhaseSTSS v +
        diamondOddPointedPhaseSTTS v := by
  rfl

private theorem diamondOddCubeDot_add_right
    {n : Nat} [NeZero n] (x y z : CyclicCube n) :
    cubeDot x (y + z) = cubeDot x y + cubeDot x z :=
  (diamondOddCubeDotBilin x).map_add y z

private theorem diamondOddCubeDot_sum_left
    {n : Nat} [NeZero n] {S : Type*} [Fintype S]
    (f : S → CyclicCube n) (g : CyclicCube n) :
    cubeDot (∑ s, f s) g = ∑ s, cubeDot (f s) g := by
  simp only [cubeDot, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem diamondOddLiteralAmbientQ_split
    {n a b c d : Nat} [NeZero n]
    (u : DiamondOddLiteralAmbient n a b c d) :
    diamondOddLiteralAmbientQ u =
      (∑ z : PVec n c, ∑ w : PVec n d,
        cubeDot (∑ y : PVec n b, u.1 y z w)
          (cubeDiffI (∑ p : PVec n a, u.2.1 p z w))) +
      ∑ y : PVec n b, ∑ z : PVec n c,
        cubeDot (∑ w : PVec n d, u.1 y z w)
          (cubeDiffK (∑ p : PVec n a, u.2.2 p y z)) := by
  unfold diamondOddLiteralAmbientQ
  simp_rw [Finset.sum_add_distrib]
  simp_rw [diamondOddCubeDot_add_right]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [map_sum]
    exact (diamondOddCubeDot_sum_left
      (fun y : PVec n b => u.1 y z w)
      (∑ p : PVec n a, cubeDiffI (u.2.1 p z w))).symm
  · apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    rw [map_sum]
    exact (diamondOddCubeDot_sum_left
      (fun w : PVec n d => u.1 y z w)
      (∑ p : PVec n a, cubeDiffK (u.2.2 p y z))).symm

theorem diamondOddLiteralAmbientQ_eq_pointedAmbientQ
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (u : DiamondOddLiteralAmbient n a b c d) :
    diamondOddLiteralAmbientQ u =
      diamondOddPointedAmbientQ
        (diamondOddPointedAmbientEquiv hn u) := by
  rw [diamondOddLiteralAmbientQ_split,
    diamondOddLiteralB_pairing hn u,
    diamondOddLiteralW_pairing hn u,
    diamondOddPointedAmbientEquiv_apply]
  unfold diamondOddPointedAmbientQ
  unfold diamondOddPointedPhaseSSSS
    diamondOddPointedPhaseSSST
    diamondOddPointedPhaseSSTS
    diamondOddPointedPhaseSSTT
    diamondOddPointedPhaseSTSS
    diamondOddPointedPhaseSTTS
  simp only [diamondOddCubeDot_add_right,
    Finset.sum_add_distrib]
  abel

noncomputable def diamondOddPointedQ
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn) : F :=
  diamondOddPointedAmbientQ x.1

@[simp] theorem diamondOddPointedQ_apply
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn) :
    diamondOddPointedQ x =
      diamondOddPointedAmbientQ x.1 := by
  rfl

theorem diamondOddLiteralQ_eq_pointedQ
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (x : DiamondOddLiteralSource n a b c d) :
    diamondOddLiteralQ x =
      diamondOddPointedQ
        (diamondOddLiteralPointedSourceEquiv hn x) := by
  change
    diamondOddLiteralAmbientQ x.1 =
      diamondOddPointedAmbientQ
        (diamondOddLiteralPointedSourceEquiv hn x).1
  rw [diamondOddLiteralPointedSourceEquiv_apply]
  exact diamondOddLiteralAmbientQ_eq_pointedAmbientQ hn x.1

theorem diamondPreCQ_eq_oddPointedQ
    {n a b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : Odd n) (x : DiamondPreCSource n a b c d) :
    diamondPreCQ x =
      diamondOddPointedQ
        (diamondOddPreCPointedSourceEquiv hb hc hd hn x) := by
  rw [diamondPreCQ_eq_oddLiteralQ hb hc hd x,
    diamondOddLiteralQ_eq_pointedQ hn]
  rfl

end

end Core4loop.SquareDiagonal.DirectWitt
