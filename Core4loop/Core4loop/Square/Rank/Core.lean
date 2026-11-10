import Core4loop.Square.Rank.Pair

namespace Core4loop

noncomputable abbrev SquareRootCore (n : ℕ) [NeZero n] := I n → MatrixZeroSum n

noncomputable abbrev SquareCompatCore (n : ℕ) [NeZero n] := I n → MatrixZeroSum n

noncomputable def rootCoreEval {n : ℕ} [NeZero n]
    (R : SquareRootCore n) (sy sz sw : I n) : F :=
  (R sz).1 sy sw

noncomputable def compatCoreEval {n : ℕ} [NeZero n]
    (S : SquareCompatCore n) (sy sz sw : I n) : F :=
  (S (sy + sz + sw)).1 sy sw

theorem finrank_SquareRootCore {n : ℕ} [NeZero n] :
    Module.finrank F (SquareRootCore n) = n * (n - 1) ^ 2 := by
  calc
    Module.finrank F (SquareRootCore n)
        = ∑ _ : I n, Module.finrank F (MatrixZeroSum n) := by
            simp [SquareRootCore, Module.finrank_pi_fintype
              (R := F) (M := fun _ : I n => MatrixZeroSum n)]
    _ = Fintype.card (I n) * (n - 1) ^ 2 := by
            simp [finrank_MatrixZeroSum]
    _ = n * (n - 1) ^ 2 := by
            simp [I, ZMod.card]

theorem finrank_SquareCompatCore {n : ℕ} [NeZero n] :
    Module.finrank F (SquareCompatCore n) = n * (n - 1) ^ 2 :=
  finrank_SquareRootCore

theorem finrank_SquareCoreDomain {n : ℕ} [NeZero n] :
    Module.finrank F (SquareRootCore n × SquareCompatCore n) =
      2 * (n * (n - 1) ^ 2) := by
  rw [Module.finrank_prod, finrank_SquareRootCore]
  ring

noncomputable def squareCoreCurlB {n : ℕ} [NeZero n]
    (R : SquareRootCore n) (S : SquareCompatCore n)
    (sy sz sw : I n) : F :=
  rootCoreEval R sy sz sw + rootCoreEval R (sy + 1) (sz - 1) sw
    + compatCoreEval S sy sz sw + compatCoreEval S (sy + 1) sz sw

noncomputable def squareCoreCurlW {n : ℕ} [NeZero n]
    (R : SquareRootCore n) (S : SquareCompatCore n)
    (sy sz sw : I n) : F :=
  rootCoreEval R sy sz sw + rootCoreEval R sy (sz - 1) (sw + 1)
    + compatCoreEval S sy sz sw + compatCoreEval S sy sz (sw + 1)

abbrev SquareCoreTarget (n : ℕ) [NeZero n] :=
  I n × I n × I n → F

abbrev SquareCoreTarget3 (n : ℕ) [NeZero n] :=
  I n → I n → I n → F

def SquareCoreAllowedProp {n : ℕ} [NeZero n]
    (R : SquareRootCore n) (S : SquareCompatCore n) : Prop :=
  ∀ sy sz sw,
    squareCoreCurlB R S sy sz sw = 0 ∧
      squareCoreCurlW R S sy sz sw = 0

noncomputable def SquareCoreCurlBMap {n : ℕ} [NeZero n] :
    (SquareRootCore n × SquareCompatCore n) →ₗ[F] SquareCoreTarget3 n where
  toFun x := fun sy sz sw => squareCoreCurlB x.1 x.2 sy sz sw
  map_add' x y := by
    funext sy sz sw
    unfold squareCoreCurlB rootCoreEval compatCoreEval
    simp [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring_nf
  map_smul' r x := by
    funext sy sz sw
    unfold squareCoreCurlB rootCoreEval compatCoreEval
    simp [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring_nf

noncomputable def SquareCoreCurlWMap {n : ℕ} [NeZero n] :
    (SquareRootCore n × SquareCompatCore n) →ₗ[F] SquareCoreTarget3 n where
  toFun x := fun sy sz sw => squareCoreCurlW x.1 x.2 sy sz sw
  map_add' x y := by
    funext sy sz sw
    unfold squareCoreCurlW rootCoreEval compatCoreEval
    simp [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring_nf
  map_smul' r x := by
    funext sy sz sw
    unfold squareCoreCurlW rootCoreEval compatCoreEval
    simp [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring_nf

noncomputable def SquareCoreCurlMap {n : ℕ} [NeZero n] :
    (SquareRootCore n × SquareCompatCore n) →ₗ[F]
      (SquareCoreTarget3 n × SquareCoreTarget3 n) :=
  LinearMap.prod (SquareCoreCurlBMap (n := n)) (SquareCoreCurlWMap (n := n))

noncomputable def SquareCoreAllowed (n : ℕ) [NeZero n] :
    Submodule F (SquareRootCore n × SquareCompatCore n) :=
  LinearMap.ker (SquareCoreCurlMap (n := n))

theorem mem_SquareCoreAllowed_iff {n : ℕ} [NeZero n]
    (x : SquareRootCore n × SquareCompatCore n) :
    x ∈ SquareCoreAllowed n ↔ SquareCoreAllowedProp x.1 x.2 := by
  constructor
  · intro hx sy sz sw
    have h := LinearMap.mem_ker.mp hx
    exact ⟨congrFun (congrFun (congrFun (congrArg Prod.fst h) sy) sz) sw,
      congrFun (congrFun (congrFun (congrArg Prod.snd h) sy) sz) sw⟩
  · intro hx
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · funext sy sz sw
      exact (hx sy sz sw).1
    · funext sy sz sw
      exact (hx sy sz sw).2

end Core4loop
