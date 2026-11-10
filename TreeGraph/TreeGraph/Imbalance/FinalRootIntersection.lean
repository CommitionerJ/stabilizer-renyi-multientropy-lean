import TreeGraph.Imbalance.MessageSpace

namespace TreeGraph
namespace Imbalance

noncomputable def rowsIn (A B : Type)
    (KB : Submodule F2 (B → F2)) :
    Submodule F2 (A × B → F2) where
  carrier := { h | ∀ a : A, (fun b : B => h (a, b)) ∈ KB }
  zero_mem' := by
    intro a
    change (0 : B → F2) ∈ KB
    exact KB.zero_mem
  add_mem' := by
    intro h k hh hk a
    exact KB.add_mem (hh a) (hk a)
  smul_mem' := by
    intro r h hh a
    exact KB.smul_mem r (hh a)

@[simp] theorem mem_rowsIn_iff {A B : Type}
    (KB : Submodule F2 (B → F2)) (h : A × B → F2) :
    h ∈ rowsIn A B KB ↔
      ∀ a : A, (fun b : B => h (a, b)) ∈ KB := by
  rfl

noncomputable def colsIn (A B : Type)
    (KA : Submodule F2 (A → F2)) :
    Submodule F2 (A × B → F2) where
  carrier := { h | ∀ b : B, (fun a : A => h (a, b)) ∈ KA }
  zero_mem' := by
    intro b
    change (0 : A → F2) ∈ KA
    exact KA.zero_mem
  add_mem' := by
    intro h k hh hk b
    exact KA.add_mem (hh b) (hk b)
  smul_mem' := by
    intro r h hh b
    exact KA.smul_mem r (hh b)

@[simp] theorem mem_colsIn_iff {A B : Type}
    (KA : Submodule F2 (A → F2)) (h : A × B → F2) :
    h ∈ colsIn A B KA ↔
      ∀ b : B, (fun a : A => h (a, b)) ∈ KA := by
  rfl

noncomputable def sliceIntersection (A B : Type)
    (KA : Submodule F2 (A → F2))
    (KB : Submodule F2 (B → F2)) :
    Submodule F2 (A × B → F2) :=
  rowsIn A B KB ⊓ colsIn A B KA

theorem mem_sliceIntersection_iff {A B : Type}
    (KA : Submodule F2 (A → F2))
    (KB : Submodule F2 (B → F2)) (h : A × B → F2) :
    h ∈ sliceIntersection A B KA KB ↔
      (∀ a : A, (fun b : B => h (a, b)) ∈ KB) ∧
        ∀ b : B, (fun a : A => h (a, b)) ∈ KA := by
  rfl

noncomputable def rowsInLinearEquiv (A B : Type)
    (KB : Submodule F2 (B → F2)) :
    rowsIn A B KB ≃ₗ[F2] (A → KB) where
  toFun h := fun a => ⟨fun b => h.1 (a, b), h.2 a⟩
  invFun g := ⟨fun p => (g p.1).1 p.2, by
    intro a
    exact (g a).2⟩
  left_inv h := by
    ext p
    rfl
  right_inv g := by
    ext a b
    rfl
  map_add' h k := by
    ext a b
    rfl
  map_smul' r h := by
    ext a b
    rfl

@[simp] theorem rowsInLinearEquiv_apply (A B : Type)
    (KB : Submodule F2 (B → F2)) (h : rowsIn A B KB)
    (a : A) (b : B) :
    (rowsInLinearEquiv A B KB h a : B → F2) b = h.1 (a, b) := rfl

noncomputable def colsInLinearEquiv (A B : Type)
    (KA : Submodule F2 (A → F2)) :
    colsIn A B KA ≃ₗ[F2] (B → KA) where
  toFun h := fun b => ⟨fun a => h.1 (a, b), h.2 b⟩
  invFun g := ⟨fun p => (g p.2).1 p.1, by
    intro b
    exact (g b).2⟩
  left_inv h := by
    ext p
    rfl
  right_inv g := by
    ext b a
    rfl
  map_add' h k := by
    ext b a
    rfl
  map_smul' r h := by
    ext b a
    rfl

@[simp] theorem colsInLinearEquiv_apply (A B : Type)
    (KA : Submodule F2 (A → F2)) (h : colsIn A B KA)
    (b : B) (a : A) :
    (colsInLinearEquiv A B KA h b : A → F2) a = h.1 (a, b) := rfl

theorem finrank_rowsIn (A B : Type) [Fintype A]
    (KB : Submodule F2 (B → F2)) [FiniteDimensional F2 KB] :
    Module.finrank F2 (rowsIn A B KB) =
      Fintype.card A * Module.finrank F2 KB := by
  classical
  calc
    Module.finrank F2 (rowsIn A B KB) =
        Module.finrank F2 (A → KB) := by
      exact LinearEquiv.finrank_eq (rowsInLinearEquiv A B KB)
    _ = ∑ _ : A, Module.finrank F2 KB := by
      simpa using
        (Module.finrank_pi_fintype
          (R := F2) (M := fun _ : A => KB))
    _ = Fintype.card A * Module.finrank F2 KB := by
      simp [Finset.sum_const]

theorem finrank_colsIn (A B : Type) [Fintype B]
    (KA : Submodule F2 (A → F2)) [FiniteDimensional F2 KA] :
    Module.finrank F2 (colsIn A B KA) =
      Fintype.card B * Module.finrank F2 KA := by
  classical
  calc
    Module.finrank F2 (colsIn A B KA) =
        Module.finrank F2 (B → KA) := by
      exact LinearEquiv.finrank_eq (colsInLinearEquiv A B KA)
    _ = ∑ _ : B, Module.finrank F2 KA := by
      simpa using
        (Module.finrank_pi_fintype
          (R := F2) (M := fun _ : B => KA))
    _ = Fintype.card B * Module.finrank F2 KA := by
      simp [Finset.sum_const]

noncomputable def rowQuotientMap (A B : Type)
    (KB : Submodule F2 (B → F2)) :
    (A × B → F2) →ₗ[F2] (A → (B → F2) ⧸ KB) where
  toFun h := fun a => KB.mkQ (fun b : B => h (a, b))
  map_add' h k := by
    ext a
    rfl
  map_smul' r h := by
    ext a
    rfl

@[simp] theorem rowQuotientMap_apply (A B : Type)
    (KB : Submodule F2 (B → F2))
    (h : A × B → F2) (a : A) :
    rowQuotientMap A B KB h a =
      KB.mkQ (fun b : B => h (a, b)) := rfl

theorem rowsIn_eq_ker_rowQuotientMap (A B : Type)
    (KB : Submodule F2 (B → F2)) :
    rowsIn A B KB = LinearMap.ker (rowQuotientMap A B KB) := by
  ext h
  constructor
  · intro hh
    ext a
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := KB) (x := fun b : B => h (a, b))).2 (hh a)
  · intro hh a
    have ha := congrFun hh a
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := KB) (x := fun b : B => h (a, b))).1 ha

noncomputable def colQuotientMap (A B : Type)
    (KA : Submodule F2 (A → F2)) :
    (A × B → F2) →ₗ[F2] (B → (A → F2) ⧸ KA) where
  toFun h := fun b => KA.mkQ (fun a : A => h (a, b))
  map_add' h k := by
    ext b
    rfl
  map_smul' r h := by
    ext b
    rfl

@[simp] theorem colQuotientMap_apply (A B : Type)
    (KA : Submodule F2 (A → F2))
    (h : A × B → F2) (b : B) :
    colQuotientMap A B KA h b =
      KA.mkQ (fun a : A => h (a, b)) := rfl

theorem colsIn_eq_ker_colQuotientMap (A B : Type)
    (KA : Submodule F2 (A → F2)) :
    colsIn A B KA = LinearMap.ker (colQuotientMap A B KA) := by
  ext h
  constructor
  · intro hh
    ext b
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := KA) (x := fun a : A => h (a, b))).2 (hh b)
  · intro hh b
    have hb := congrFun hh b
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := KA) (x := fun a : A => h (a, b))).1 hb

noncomputable def allDualSlicesIn (A M : Type)
    [AddCommGroup M] [Module F2 M]
    (KA : Submodule F2 (A → F2)) :
    Submodule F2 (A → M) where
  carrier := { f | ∀ ℓ : Module.Dual F2 M,
    (fun a : A => ℓ (f a)) ∈ KA }
  zero_mem' := by
    intro ℓ
    have hzero : (fun a : A => ℓ ((0 : A → M) a)) = (0 : A → F2) := by
      ext a
      simp
    rw [hzero]
    exact KA.zero_mem
  add_mem' := by
    intro f g hf hg ℓ
    have hsum :
        (fun a : A => ℓ ((f + g) a)) =
          (fun a : A => ℓ (f a)) + (fun a : A => ℓ (g a)) := by
      ext a
      simp
    rw [hsum]
    exact KA.add_mem (hf ℓ) (hg ℓ)
  smul_mem' := by
    intro r f hf ℓ
    have hsmul :
        (fun a : A => ℓ ((r • f) a)) =
          r • (fun a : A => ℓ (f a)) := by
      ext a
      simp
    rw [hsmul]
    exact KA.smul_mem r (hf ℓ)

@[simp] theorem mem_allDualSlicesIn_iff {A M : Type}
    [AddCommGroup M] [Module F2 M]
    (KA : Submodule F2 (A → F2)) (f : A → M) :
    f ∈ allDualSlicesIn A M KA ↔
      ∀ ℓ : Module.Dual F2 M, (fun a : A => ℓ (f a)) ∈ KA := by
  rfl

noncomputable def allDualSlicesBasisEquiv (A M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (KA : Submodule F2 (A → F2)) :
    allDualSlicesIn A M KA ≃ₗ[F2]
      (Module.Basis.ofVectorSpaceIndex F2 M → KA) := by
  classical
  let b := Module.Basis.ofVectorSpace F2 M
  exact
  { toFun := fun f i =>
      ⟨fun a : A => b.repr (f.1 a) i, f.2 (b.coord i)⟩
    invFun := fun g =>
      ⟨fun a : A => ∑ i : Module.Basis.ofVectorSpaceIndex F2 M,
          (g i : A → F2) a • b i, by
        intro ℓ
        have hfun :
            (fun a : A =>
              ℓ (∑ i : Module.Basis.ofVectorSpaceIndex F2 M,
                (g i : A → F2) a • b i)) =
              ∑ i : Module.Basis.ofVectorSpaceIndex F2 M,
                (ℓ (b i)) • (g i : A → F2) := by
          ext a
          simp [Finset.sum_apply, map_sum, map_smul, smul_eq_mul,
            mul_comm]
        rw [hfun]
        exact KA.sum_mem (fun i _ => KA.smul_mem (ℓ (b i)) (g i).2)⟩
    left_inv := by
      intro f
      ext a
      exact b.sum_repr (f.1 a)
    right_inv := by
      intro g
      ext i a
      change b.repr
        (∑ j : Module.Basis.ofVectorSpaceIndex F2 M,
          (g j : A → F2) a • b j) i = (g i : A → F2) a
      rw [b.repr_sum_self]
    map_add' := by
      intro f g
      ext i a
      simp
    map_smul' := by
      intro r f
      ext i a
      simp }

theorem finrank_allDualSlicesIn (A M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (KA : Submodule F2 (A → F2)) [FiniteDimensional F2 KA] :
    Module.finrank F2 (allDualSlicesIn A M KA) =
      Module.finrank F2 M * Module.finrank F2 KA := by
  classical
  let b := Module.Basis.ofVectorSpace F2 M
  calc
    Module.finrank F2 (allDualSlicesIn A M KA) =
        Module.finrank F2 (Module.Basis.ofVectorSpaceIndex F2 M → KA) := by
      exact LinearEquiv.finrank_eq (allDualSlicesBasisEquiv A M KA)
    _ = ∑ _ : Module.Basis.ofVectorSpaceIndex F2 M, Module.finrank F2 KA := by
      simpa using
        (Module.finrank_pi_fintype
          (R := F2)
          (M := fun _ : Module.Basis.ofVectorSpaceIndex F2 M => KA))
    _ = Fintype.card (Module.Basis.ofVectorSpaceIndex F2 M) *
        Module.finrank F2 KA := by
      simp [Finset.sum_const]
    _ = Module.finrank F2 M * Module.finrank F2 KA := by
      rw [← Module.finrank_eq_card_basis b]

noncomputable def evalDualSubmodule {B : Type}
    (KB : Submodule F2 (B → F2)) (b : B) :
    Module.Dual F2 KB where
  toFun f := (f : B → F2) b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evalDualSubmodule_apply {B : Type}
    (KB : Submodule F2 (B → F2)) (b : B) (f : KB) :
    evalDualSubmodule KB b f = (f : B → F2) b := rfl

theorem allDualSlicesIn_of_eval_slices
    (A B : Type) [Finite B]
    (KA : Submodule F2 (A → F2))
    (KB : Submodule F2 (B → F2))
    (f : A → KB)
    (hcols : ∀ b : B, (fun a : A => (f a : B → F2) b) ∈ KA) :
    f ∈ allDualSlicesIn A KB KA := by
  classical
  haveI := Fintype.ofFinite B
  intro ℓ
  rcases dual_restrict_surjective KB ℓ with ⟨ℓfull, hℓfull⟩
  let c := linearFunctionalCoeff B ℓfull
  have hfun :
      (fun a : A => ℓ (f a)) =
        ∑ b : B, c b • (fun a : A => (f a : B → F2) b) := by
    ext a
    have hrestr :=
      congrArg (fun φ : Module.Dual F2 KB => φ (f a)) hℓfull
    calc
      ℓ (f a) = ℓfull (f a : B → F2) := by
        simpa [restrictDual_apply] using hrestr.symm
      _ = dotLinear B c (f a : B → F2) := by
        have hdot :=
          congrArg (fun φ : Module.Dual F2 (B → F2) =>
            φ (f a : B → F2))
            (linearFunctional_eq_dotLinear_coeff B ℓfull)
        simpa [c] using hdot
      _ = (∑ b : B, c b • (fun a : A => (f a : B → F2) b)) a := by
        simp [dotLinear, Finset.sum_apply, smul_eq_mul, mul_comm]
  rw [hfun]
  exact KA.sum_mem (fun b _ => KA.smul_mem (c b) (hcols b))

noncomputable def sliceIntersectionAllDualEquiv
    (A B : Type) [Finite B]
    (KA : Submodule F2 (A → F2))
    (KB : Submodule F2 (B → F2)) :
    sliceIntersection A B KA KB ≃ₗ[F2]
      allDualSlicesIn A KB KA where
  toFun h :=
    ⟨fun a : A => ⟨fun b : B => h.1 (a, b), h.2.1 a⟩,
      allDualSlicesIn_of_eval_slices A B KA KB
        (fun a : A => ⟨fun b : B => h.1 (a, b), h.2.1 a⟩)
        (by
          intro b
          exact h.2.2 b)⟩
  invFun f :=
    ⟨fun p : A × B => (f.1 p.1 : B → F2) p.2,
      ⟨by
        intro a
        exact (f.1 a).2,
      by
        intro b
        simpa using f.2 (evalDualSubmodule KB b)⟩⟩
  left_inv h := by
    ext p
    rfl
  right_inv f := by
    ext a b
    rfl
  map_add' h k := by
    ext a b
    rfl
  map_smul' r h := by
    ext a b
    rfl

theorem finrank_sliceIntersection
    (A B : Type) [Finite B]
    (KA : Submodule F2 (A → F2)) [FiniteDimensional F2 KA]
    (KB : Submodule F2 (B → F2)) [FiniteDimensional F2 KB] :
    Module.finrank F2 (sliceIntersection A B KA KB) =
      Module.finrank F2 KA * Module.finrank F2 KB := by
  calc
    Module.finrank F2 (sliceIntersection A B KA KB) =
        Module.finrank F2 (allDualSlicesIn A KB KA) := by
      exact LinearEquiv.finrank_eq
        (sliceIntersectionAllDualEquiv A B KA KB)
    _ = Module.finrank F2 KB * Module.finrank F2 KA := by
      exact finrank_allDualSlicesIn A KB KA
    _ = Module.finrank F2 KA * Module.finrank F2 KB := by
      rw [Nat.mul_comm]

theorem independent_slice_intersection_dim
    (A B : Type) [Finite B]
    (KA : Submodule F2 (A → F2)) [FiniteDimensional F2 KA]
    (KB : Submodule F2 (B → F2)) [FiniteDimensional F2 KB] :
    Module.finrank F2 (sliceIntersection A B KA KB) =
      Module.finrank F2 KA * Module.finrank F2 KB := by
  exact finrank_sliceIntersection A B KA KB

structure SliceFactor where
  C : Type
  finite_C : Finite C
  K : Submodule F2 (C → F2)
  finiteDim_K : FiniteDimensional F2 K

def factorProduct : List SliceFactor → Type
  | [] => PUnit
  | F :: Fs => F.C × factorProduct Fs

noncomputable instance factorProductFintype :
    (Fs : List SliceFactor) → Fintype (factorProduct Fs)
  | [] => by
      change Fintype PUnit
      infer_instance
  | F :: Fs => by
      change Fintype (F.C × factorProduct Fs)
      letI : Finite F.C := F.finite_C
      letI := Fintype.ofFinite F.C
      letI := factorProductFintype Fs
      infer_instance

noncomputable def independentAllowed :
    (Fs : List SliceFactor) → Submodule F2 (factorProduct Fs → F2)
  | [] => ⊤
  | F :: Fs => by
      letI := F.finite_C
      letI := F.finiteDim_K
      letI := factorProductFintype Fs
      exact sliceIntersection F.C (factorProduct Fs) F.K
        (independentAllowed Fs)

noncomputable instance independentAllowedFintype
    (Fs : List SliceFactor) : Fintype (independentAllowed Fs) := by
  classical
  letI := factorProductFintype Fs
  exact Fintype.ofFinite (independentAllowed Fs)

noncomputable def factorDimProduct : List SliceFactor → Nat
  | [] => 1
  | F :: Fs => Module.finrank F2 F.K * factorDimProduct Fs

theorem finrank_independentAllowed :
    ∀ Fs : List SliceFactor,
      Module.finrank F2 (independentAllowed Fs) =
        factorDimProduct Fs
  | [] => by
      classical
      letI := factorProductFintype []
      calc
        Module.finrank F2 (independentAllowed []) =
            Module.finrank F2 (factorProduct [] → F2) := by
          rw [independentAllowed, finrank_top]
        _ = ∑ _ : factorProduct [], Module.finrank F2 F2 := by
          exact
            Module.finrank_pi_fintype
              (R := F2) (M := fun _ : factorProduct [] => F2)
        _ = 1 := by
          simp [factorProduct]
        _ = factorDimProduct [] := rfl
  | F :: Fs => by
      classical
      letI := F.finite_C
      letI := F.finiteDim_K
      letI := factorProductFintype Fs
      haveI : FiniteDimensional F2 (independentAllowed Fs) := inferInstance
      calc
        Module.finrank F2 (independentAllowed (F :: Fs)) =
            Module.finrank F2 F.K *
              Module.finrank F2 (independentAllowed Fs) := by
          change
            Module.finrank F2
              (sliceIntersection F.C (factorProduct Fs) F.K
                (independentAllowed Fs)) =
              Module.finrank F2 F.K *
                Module.finrank F2 (independentAllowed Fs)
          exact finrank_sliceIntersection F.C (factorProduct Fs) F.K
            (independentAllowed Fs)
        _ = Module.finrank F2 F.K * factorDimProduct Fs := by
          rw [finrank_independentAllowed Fs]
        _ = factorDimProduct (F :: Fs) := rfl

theorem card_independentAllowed (Fs : List SliceFactor) :
    Fintype.card (independentAllowed Fs) =
      2 ^ factorDimProduct Fs := by
  classical
  rw [submodule_card_eq_pow_finrank]
  rw [finrank_independentAllowed]

theorem final_root_allowed_dim (Fs : List SliceFactor) :
    Module.finrank F2 (independentAllowed Fs) =
      factorDimProduct Fs := by
  exact finrank_independentAllowed Fs

end Imbalance
end TreeGraph
