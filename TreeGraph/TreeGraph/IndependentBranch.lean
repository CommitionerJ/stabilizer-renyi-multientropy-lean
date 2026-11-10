import TreeGraph.MessageDimension

namespace TreeGraph

namespace RawPrimitive

noncomputable def branchFactor (n : Nat) (C : RTree) : Nat :=
  branchConstraintExponent n (n ^ RTree.totalWeight C) (Ydim n C)

theorem card_ker_branchConstraintMap_eq_two_pow_branchFactor
    {n : Nat} [NeZero n] {C : RTree} {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (hP : Module.finrank F2 P = n ^ RTree.totalWeight C)
    (hM : Module.finrank F2 M = Ydim n C) :
    Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) =
      2 ^ branchFactor n C := by
  simpa [branchFactor] using
    (card_ker_branchConstraintMap_eq_branchConstraintExponent
      (n := n)
      (N := n ^ RTree.totalWeight C)
      (Y := Ydim n C)
      (P := P)
      (M := M)
      (π := π)
      (hπ := hπ)
      (hP := hP)
      (hM := hM))

theorem card_branchConstraintFiber_eq_two_pow_branchFactor
    {n : Nat} [NeZero n] {C : RTree} {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (g : ZMod n → M) (hg : BranchMessageCompatible M g)
    (hP : Module.finrank F2 P = n ^ RTree.totalWeight C)
    (hM : Module.finrank F2 M = Ydim n C) :
    Nat.card { p : P // branchConstraintMap P M π p = g } =
      2 ^ branchFactor n C := by
  simpa [branchFactor] using
    (card_branchConstraintFiber_eq_branchConstraintExponent
      (n := n)
      (N := n ^ RTree.totalWeight C)
      (Y := Ydim n C)
      (P := P)
      (M := M)
      (π := π)
      (hπ := hπ)
      (g := g)
      (hg := hg)
      (hP := hP)
      (hM := hM))

noncomputable def independentBranchDimension
    (n : Nat) (cs : List RTree) : Nat :=
  (cs.map (branchFactor n)).prod

@[simp] theorem independentBranchDimension_nil (n : Nat) :
    independentBranchDimension n [] = 1 := by
  simp [independentBranchDimension]

@[simp] theorem independentBranchDimension_cons
    (n : Nat) (C : RTree) (cs : List RTree) :
    independentBranchDimension n (C :: cs) =
      branchFactor n C * independentBranchDimension n cs := by
  simp [independentBranchDimension]

@[simp] theorem independentBranchDimension_append
    (n : Nat) (left right : List RTree) :
    independentBranchDimension n (left ++ right) =
      independentBranchDimension n left * independentBranchDimension n right := by
  simp [independentBranchDimension]

theorem Ydim_node_eq_independentBranchDimension
    (n a : Nat) (cs : List RTree) :
    Ydim n (RTree.node a cs) = independentBranchDimension n cs := by
  induction cs with
  | nil =>
      simp [independentBranchDimension]
  | cons C rest ih =>
      have htail :
          (List.map (fun D =>
            branchConstraintExponent n (n ^ RTree.totalWeight D) (Ydim n D))
              rest).prod =
            independentBranchDimension n rest := by
        rw [← ih]
        rw [Ydim]
      simp [Ydim, independentBranchDimension, branchFactor, htail]

noncomputable def BranchIndex (n : Nat) : List RTree → Type
  | [] => PUnit
  | C :: rest => Fin (branchFactor n C) × BranchIndex n rest

noncomputable instance branchIndexFintype (n : Nat) :
    (cs : List RTree) → Fintype (BranchIndex n cs)
  | [] => by
      change Fintype PUnit
      infer_instance
  | C :: rest => by
      change Fintype (Fin (branchFactor n C) × BranchIndex n rest)
      haveI := branchIndexFintype n rest
      infer_instance

noncomputable instance branchIndexDecidableEq (n : Nat) :
    (cs : List RTree) → DecidableEq (BranchIndex n cs)
  | [] => by
      change DecidableEq PUnit
      infer_instance
  | C :: rest => by
      change DecidableEq (Fin (branchFactor n C) × BranchIndex n rest)
      haveI := branchIndexDecidableEq n rest
      infer_instance

noncomputable def branchIndexAppendEquiv (n : Nat) :
    (left right : List RTree) →
      BranchIndex n (left ++ right) ≃
        BranchIndex n left × BranchIndex n right
  | [], right =>
      { toFun := fun j => ⟨PUnit.unit, j⟩
        invFun := fun p => p.2
        left_inv := by
          intro j
          rfl
        right_inv := by
          intro p
          cases p.1
          rfl }
  | C :: left, right =>
      let e := branchIndexAppendEquiv n left right
      { toFun := fun p =>
          ⟨⟨p.1, (e p.2).1⟩, (e p.2).2⟩
        invFun := fun p =>
          ⟨p.1.1, e.symm ⟨p.1.2, p.2⟩⟩
        left_inv := by
          intro p
          simp
        right_inv := by
          intro p
          simp }

@[simp] theorem branchIndexAppendEquiv_nil_apply
    (n : Nat) (right : List RTree) (j : BranchIndex n right) :
    branchIndexAppendEquiv n [] right j = ⟨PUnit.unit, j⟩ := rfl

@[simp] theorem branchIndexAppendEquiv_nil_symm_apply
    (n : Nat) (right : List RTree)
    (p : BranchIndex n [] × BranchIndex n right) :
    (branchIndexAppendEquiv n [] right).symm p = p.2 := rfl

@[simp] theorem branchIndexAppendEquiv_cons_apply
    (n : Nat) (C : RTree) (left right : List RTree)
    (p : BranchIndex n ((C :: left) ++ right)) :
    branchIndexAppendEquiv n (C :: left) right p =
      ⟨⟨p.1, ((branchIndexAppendEquiv n left right) p.2).1⟩,
        ((branchIndexAppendEquiv n left right) p.2).2⟩ := rfl

@[simp] theorem branchIndexAppendEquiv_cons_symm_apply
    (n : Nat) (C : RTree) (left right : List RTree)
    (p : BranchIndex n (C :: left) × BranchIndex n right) :
    (branchIndexAppendEquiv n (C :: left) right).symm p =
      ⟨p.1.1,
        (branchIndexAppendEquiv n left right).symm ⟨p.1.2, p.2⟩⟩ := rfl

noncomputable def branchIndexChildExternalEquiv
    (n : Nat) (left : List RTree) (C : RTree) (right : List RTree) :
    BranchIndex n (left ++ C :: right) ≃
      Fin (branchFactor n C) × BranchIndex n (left ++ right) :=
  let eHead := branchIndexAppendEquiv n left (C :: right)
  let eExternal := branchIndexAppendEquiv n left right
  { toFun := fun k =>
      let p := eHead k
      ⟨p.2.1, eExternal.symm ⟨p.1, p.2.2⟩⟩
    invFun := fun p =>
      let q := eExternal p.2
      eHead.symm ⟨q.1, ⟨p.1, q.2⟩⟩
    left_inv := by
      intro k
      simp
    right_inv := by
      intro p
      simp }

@[simp] theorem branchIndexChildExternalEquiv_apply
    (n : Nat) (left : List RTree) (C : RTree) (right : List RTree)
    (k : BranchIndex n (left ++ C :: right)) :
    branchIndexChildExternalEquiv n left C right k =
      let p := branchIndexAppendEquiv n left (C :: right) k
      ⟨p.2.1,
        (branchIndexAppendEquiv n left right).symm ⟨p.1, p.2.2⟩⟩ := rfl

@[simp] theorem branchIndexChildExternalEquiv_symm_apply
    (n : Nat) (left : List RTree) (C : RTree) (right : List RTree)
    (p : Fin (branchFactor n C) × BranchIndex n (left ++ right)) :
    (branchIndexChildExternalEquiv n left C right).symm p =
      let q := branchIndexAppendEquiv n left right p.2
      (branchIndexAppendEquiv n left (C :: right)).symm
        ⟨q.1, ⟨p.1, q.2⟩⟩ := rfl

theorem card_branchIndex (n : Nat) :
    ∀ cs : List RTree,
      Fintype.card (BranchIndex n cs) = independentBranchDimension n cs
  | [] => by
      calc
        Fintype.card (BranchIndex n []) = Fintype.card PUnit := by
          exact Fintype.card_congr (Equiv.refl PUnit)
        _ = independentBranchDimension n [] := by
          simp [independentBranchDimension]
  | C :: rest => by
      have hrest := card_branchIndex n rest
      calc
        Fintype.card (BranchIndex n (C :: rest)) =
            Fintype.card (Fin (branchFactor n C) × BranchIndex n rest) := by
          exact Fintype.card_congr
            (Equiv.refl (Fin (branchFactor n C) × BranchIndex n rest))
        _ = branchFactor n C * Fintype.card (BranchIndex n rest) := by
          rw [Fintype.card_prod, Fintype.card_fin]
        _ = branchFactor n C * independentBranchDimension n rest := by
          rw [hrest]
        _ = independentBranchDimension n (C :: rest) := by
          rw [independentBranchDimension_cons]

abbrev OpenRootMessageSpace (n : Nat) (cs : List RTree) :=
  BranchIndex n cs → F2

noncomputable def openRootMessageSpaceAppendLinearEquiv
    (n : Nat) (left right : List RTree) :
    OpenRootMessageSpace n (left ++ right) ≃ₗ[F2]
      (BranchIndex n left → OpenRootMessageSpace n right) where
  toFun f := fun i j =>
    f ((branchIndexAppendEquiv n left right).symm ⟨i, j⟩)
  invFun g := fun k =>
    let p := branchIndexAppendEquiv n left right k
    g p.1 p.2
  left_inv f := by
    ext k
    simp
  right_inv g := by
    ext i j
    simp
  map_add' f g := by
    ext i j
    rfl
  map_smul' r f := by
    ext i j
    rfl

@[simp] theorem openRootMessageSpaceAppendLinearEquiv_apply
    (n : Nat) (left right : List RTree)
    (f : OpenRootMessageSpace n (left ++ right))
    (i : BranchIndex n left) (j : BranchIndex n right) :
    openRootMessageSpaceAppendLinearEquiv n left right f i j =
      f ((branchIndexAppendEquiv n left right).symm ⟨i, j⟩) := rfl

@[simp] theorem openRootMessageSpaceAppendLinearEquiv_symm_apply
    (n : Nat) (left right : List RTree)
    (f : BranchIndex n left → OpenRootMessageSpace n right)
    (k : BranchIndex n (left ++ right)) :
    (openRootMessageSpaceAppendLinearEquiv n left right).symm f k =
      f ((branchIndexAppendEquiv n left right) k).1
        ((branchIndexAppendEquiv n left right) k).2 := rfl

noncomputable def openRootMessageSpaceChildExternalLinearEquiv
    (n : Nat) (left : List RTree) (C : RTree) (right : List RTree) :
    OpenRootMessageSpace n (left ++ C :: right) ≃ₗ[F2]
      (Fin (branchFactor n C) →
        OpenRootMessageSpace n (left ++ right)) where
  toFun f := fun i j =>
    f ((branchIndexChildExternalEquiv n left C right).symm ⟨i, j⟩)
  invFun g := fun k =>
    let p := branchIndexChildExternalEquiv n left C right k
    g p.1 p.2
  left_inv f := by
    ext k
    simp
  right_inv g := by
    ext i j
    simp
  map_add' f g := by
    ext i j
    rfl
  map_smul' r f := by
    ext i j
    rfl

@[simp] theorem openRootMessageSpaceChildExternalLinearEquiv_apply
    (n : Nat) (left : List RTree) (C : RTree) (right : List RTree)
    (f : OpenRootMessageSpace n (left ++ C :: right))
    (i : Fin (branchFactor n C)) (j : BranchIndex n (left ++ right)) :
    openRootMessageSpaceChildExternalLinearEquiv n left C right f i j =
      f ((branchIndexChildExternalEquiv n left C right).symm ⟨i, j⟩) := rfl

@[simp] theorem openRootMessageSpaceChildExternalLinearEquiv_symm_apply
    (n : Nat) (left : List RTree) (C : RTree) (right : List RTree)
    (f : Fin (branchFactor n C) →
      OpenRootMessageSpace n (left ++ right))
    (k : BranchIndex n (left ++ C :: right)) :
    (openRootMessageSpaceChildExternalLinearEquiv n left C right).symm f k =
      f ((branchIndexChildExternalEquiv n left C right) k).1
        ((branchIndexChildExternalEquiv n left C right) k).2 := rfl

noncomputable def openRootMessageSpaceConsLinearEquiv
    (n : Nat) (C : RTree) (cs : List RTree) :
    OpenRootMessageSpace n (C :: cs) ≃ₗ[F2]
      (Fin (branchFactor n C) → OpenRootMessageSpace n cs) where
  toFun f := fun i j => f (i, j)
  invFun g := fun p => g p.1 p.2
  left_inv f := by
    ext p
    rfl
  right_inv g := by
    ext i j
    rfl
  map_add' f g := by
    ext i j
    rfl
  map_smul' r f := by
    ext i j
    rfl

@[simp] theorem openRootMessageSpaceConsLinearEquiv_apply
    (n : Nat) (C : RTree) (cs : List RTree)
    (f : OpenRootMessageSpace n (C :: cs))
    (i : Fin (branchFactor n C)) (j : BranchIndex n cs) :
    openRootMessageSpaceConsLinearEquiv n C cs f i j = f (i, j) := rfl

@[simp] theorem openRootMessageSpaceConsLinearEquiv_symm_apply
    (n : Nat) (C : RTree) (cs : List RTree)
    (f : Fin (branchFactor n C) → OpenRootMessageSpace n cs)
    (p : BranchIndex n (C :: cs)) :
    (openRootMessageSpaceConsLinearEquiv n C cs).symm f p =
      f p.1 p.2 := rfl

noncomputable instance openRootMessageSpaceFintype
    (n : Nat) (cs : List RTree) :
    Fintype (OpenRootMessageSpace n cs) := by
  change Fintype (BranchIndex n cs → F2)
  haveI := branchIndexDecidableEq n cs
  haveI := branchIndexFintype n cs
  infer_instance

theorem finrank_openRootMessageSpace
    (n : Nat) (cs : List RTree) :
    Module.finrank F2 (OpenRootMessageSpace n cs) =
      independentBranchDimension n cs := by
  classical
  calc
    Module.finrank F2 (OpenRootMessageSpace n cs) =
        ∑ _ : BranchIndex n cs, Module.finrank F2 F2 := by
          simp [OpenRootMessageSpace]
    _ = Fintype.card (BranchIndex n cs) := by
          simp [F2]
    _ = independentBranchDimension n cs := card_branchIndex n cs

@[simp] theorem finrank_openRootMessageSpace_nil (n : Nat) :
    Module.finrank F2 (OpenRootMessageSpace n []) = 1 := by
  rw [finrank_openRootMessageSpace]
  simp [independentBranchDimension]

theorem finrank_openRootMessageSpace_cons
    (n : Nat) (C : RTree) (cs : List RTree) :
    Module.finrank F2 (OpenRootMessageSpace n (C :: cs)) =
      branchFactor n C *
        Module.finrank F2 (OpenRootMessageSpace n cs) := by
  rw [finrank_openRootMessageSpace, independentBranchDimension_cons,
    finrank_openRootMessageSpace]

theorem finrank_openRootMessageSpace_append
    (n : Nat) (left right : List RTree) :
    Module.finrank F2 (OpenRootMessageSpace n (left ++ right)) =
      independentBranchDimension n left *
        Module.finrank F2 (OpenRootMessageSpace n right) := by
  rw [finrank_openRootMessageSpace, independentBranchDimension_append,
    finrank_openRootMessageSpace]

theorem natCard_openRootMessageSpace
    (n : Nat) (cs : List RTree) :
    Nat.card (OpenRootMessageSpace n cs) =
      2 ^ independentBranchDimension n cs := by
  classical
  haveI := branchIndexFintype n cs
  calc
    Nat.card (OpenRootMessageSpace n cs) =
        Nat.card F2 ^ Module.finrank F2 (OpenRootMessageSpace n cs) := by
      exact Module.natCard_eq_pow_finrank
        (K := F2) (V := OpenRootMessageSpace n cs)
    _ = 2 ^ independentBranchDimension n cs := by
      rw [finrank_openRootMessageSpace]
      simp [F2]

theorem card_openRootMessageSpace
    (n : Nat) (cs : List RTree) :
    Fintype.card (OpenRootMessageSpace n cs) =
      2 ^ independentBranchDimension n cs := by
  classical
  haveI := branchIndexDecidableEq n cs
  haveI := branchIndexFintype n cs
  simpa [Nat.card_eq_fintype_card] using
    natCard_openRootMessageSpace n cs

@[simp] theorem card_openRootMessageSpace_nil (n : Nat) :
    Fintype.card (OpenRootMessageSpace n []) = 2 := by
  rw [card_openRootMessageSpace]
  norm_num

theorem card_openRootMessageSpace_cons
    (n : Nat) (C : RTree) (cs : List RTree) :
    Fintype.card (OpenRootMessageSpace n (C :: cs)) =
      2 ^ (branchFactor n C *
        Module.finrank F2 (OpenRootMessageSpace n cs)) := by
  rw [card_openRootMessageSpace, independentBranchDimension_cons,
    finrank_openRootMessageSpace]

theorem card_openRootMessageSpace_cons_factorized
    (n : Nat) (C : RTree) (cs : List RTree) :
    Fintype.card (OpenRootMessageSpace n (C :: cs)) =
      (Fintype.card (OpenRootMessageSpace n cs)) ^ branchFactor n C := by
  calc
    Fintype.card (OpenRootMessageSpace n (C :: cs)) =
        2 ^ (branchFactor n C * independentBranchDimension n cs) := by
      rw [card_openRootMessageSpace, independentBranchDimension_cons]
    _ = 2 ^ (independentBranchDimension n cs * branchFactor n C) := by
      rw [Nat.mul_comm]
    _ = (2 ^ independentBranchDimension n cs) ^ branchFactor n C := by
      rw [Nat.pow_mul]
    _ = (Fintype.card (OpenRootMessageSpace n cs)) ^ branchFactor n C := by
      rw [card_openRootMessageSpace]

theorem card_openRootMessageSpace_cons_via_function_space
    (n : Nat) (C : RTree) (cs : List RTree) :
    Fintype.card (OpenRootMessageSpace n (C :: cs)) =
      Fintype.card
        (Fin (branchFactor n C) → OpenRootMessageSpace n cs) := by
  exact Fintype.card_congr
    (openRootMessageSpaceConsLinearEquiv n C cs).toEquiv

theorem card_openRootMessageSpace_cons_from_curry
    (n : Nat) (C : RTree) (cs : List RTree) :
    Fintype.card (OpenRootMessageSpace n (C :: cs)) =
      (Fintype.card (OpenRootMessageSpace n cs)) ^ branchFactor n C := by
  rw [card_openRootMessageSpace_cons_via_function_space]
  rw [Fintype.card_fun
    (α := Fin (branchFactor n C))
    (β := OpenRootMessageSpace n cs)]
  rw [Fintype.card_fin]

theorem card_openRootMessageSpace_append_via_function_space
    (n : Nat) (left right : List RTree) :
    Fintype.card (OpenRootMessageSpace n (left ++ right)) =
      Fintype.card
        (BranchIndex n left → OpenRootMessageSpace n right) := by
  exact Fintype.card_congr
    (openRootMessageSpaceAppendLinearEquiv n left right).toEquiv

theorem card_openRootMessageSpace_append_from_curry
    (n : Nat) (left right : List RTree) :
    Fintype.card (OpenRootMessageSpace n (left ++ right)) =
      (Fintype.card (OpenRootMessageSpace n right)) ^
        independentBranchDimension n left := by
  classical
  rw [card_openRootMessageSpace_append_via_function_space]
  rw [Fintype.card_fun
    (α := BranchIndex n left)
    (β := OpenRootMessageSpace n right)]
  rw [card_branchIndex]

theorem card_openRootMessageSpace_child_external_via_function_space
    (n : Nat) (left : List RTree) (C : RTree) (right : List RTree) :
    Fintype.card (OpenRootMessageSpace n (left ++ C :: right)) =
      Fintype.card
        (Fin (branchFactor n C) →
          OpenRootMessageSpace n (left ++ right)) := by
  exact Fintype.card_congr
    (openRootMessageSpaceChildExternalLinearEquiv n left C right).toEquiv

theorem card_openRootMessageSpace_child_external_from_curry
    (n : Nat) (left : List RTree) (C : RTree) (right : List RTree) :
    Fintype.card (OpenRootMessageSpace n (left ++ C :: right)) =
      (Fintype.card (OpenRootMessageSpace n (left ++ right))) ^
        branchFactor n C := by
  rw [card_openRootMessageSpace_child_external_via_function_space]
  rw [Fintype.card_fun
    (α := Fin (branchFactor n C))
    (β := OpenRootMessageSpace n (left ++ right))]
  rw [Fintype.card_fin]

theorem card_openRootMessageSpace_eq_two_pow_Ydim_node
    (n a : Nat) (cs : List RTree) :
    Fintype.card (OpenRootMessageSpace n cs) =
      2 ^ Ydim n (RTree.node a cs) := by
  rw [card_openRootMessageSpace, Ydim_node_eq_independentBranchDimension]

theorem finrank_openRootMessageSpace_eq_Ydim_node
    (n a : Nat) (cs : List RTree) :
    Module.finrank F2 (OpenRootMessageSpace n cs) =
      Ydim n (RTree.node a cs) := by
  rw [finrank_openRootMessageSpace,
    Ydim_node_eq_independentBranchDimension]

theorem branchFactor_cast_eq_Yassign
    {n : Nat} [NeZero n] {C : RTree} (hC : RTree.PositiveWeights C) :
    ((branchFactor n C : Nat) : ℤ) =
      (nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C := by
  simpa [branchFactor] using branchConstraintExponent_cast_Ydim (n := n) hC

theorem branchFactor_toNat_Yassign
    {n : Nat} [NeZero n] {C : RTree} (hC : RTree.PositiveWeights C) :
    Int.toNat ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C) =
      branchFactor n C := by
  simpa [branchFactor] using
    branchConstraintExponent_Ydim_toNat (n := n) hC

theorem card_ker_branchConstraintMap_eq_two_pow_assignmentFactor
    {n : Nat} [NeZero n] {C : RTree} (hC : RTree.PositiveWeights C)
    {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (hP : Module.finrank F2 P = n ^ RTree.totalWeight C)
    (hM : Module.finrank F2 M = Ydim n C) :
    Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) =
      2 ^ Int.toNat
        ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C) := by
  calc
    Nat.card (↥(LinearMap.ker (branchConstraintMap P M π))) =
        2 ^ branchFactor n C :=
      card_ker_branchConstraintMap_eq_two_pow_branchFactor
        (C := C) π hπ hP hM
    _ =
        2 ^ Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C) := by
      rw [branchFactor_toNat_Yassign (n := n) hC]

theorem card_branchConstraintFiber_eq_two_pow_assignmentFactor
    {n : Nat} [NeZero n] {C : RTree} (hC : RTree.PositiveWeights C)
    {P M : Type}
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (π : P →ₗ[F2] (ZMod n → M))
    (hπ : Function.Surjective π)
    (g : ZMod n → M) (hg : BranchMessageCompatible M g)
    (hP : Module.finrank F2 P = n ^ RTree.totalWeight C)
    (hM : Module.finrank F2 M = Ydim n C) :
    Nat.card { p : P // branchConstraintMap P M π p = g } =
      2 ^ Int.toNat
        ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C) := by
  calc
    Nat.card { p : P // branchConstraintMap P M π p = g } =
        2 ^ branchFactor n C :=
      card_branchConstraintFiber_eq_two_pow_branchFactor
        (C := C) π hπ g hg hP hM
    _ =
        2 ^ Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C) := by
      rw [branchFactor_toNat_Yassign (n := n) hC]

theorem independentBranchDimension_eq_assignmentFactorProduct
    {n : Nat} [NeZero n] :
    ∀ {cs : List RTree},
      (∀ C ∈ cs, RTree.PositiveWeights C) →
      independentBranchDimension n cs =
        (cs.map (fun C =>
          Int.toNat
            ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod
  | [], _ => by
      simp [independentBranchDimension]
  | C :: rest, hchildren => by
      have hC : RTree.PositiveWeights C := hchildren C (by simp)
      have hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
        intro D hD
        exact hchildren D (by simp [hD])
      have htail :=
        independentBranchDimension_eq_assignmentFactorProduct
          (n := n) hrest
      rw [independentBranchDimension_cons, htail]
      rw [← branchFactor_toNat_Yassign (n := n) hC]
      simp

theorem finrank_openRootMessageSpace_eq_assignmentFactorProduct
    {n : Nat} [NeZero n] {cs : List RTree}
    (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C) :
    Module.finrank F2 (OpenRootMessageSpace n cs) =
      (cs.map (fun C =>
        Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod := by
  rw [finrank_openRootMessageSpace]
  exact independentBranchDimension_eq_assignmentFactorProduct
    (n := n) hchildren

theorem natCard_openRootMessageSpace_eq_two_pow_assignmentFactorProduct
    {n : Nat} [NeZero n] {cs : List RTree}
    (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C) :
    Nat.card (OpenRootMessageSpace n cs) =
      2 ^ (cs.map (fun C =>
        Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod := by
  rw [natCard_openRootMessageSpace]
  rw [independentBranchDimension_eq_assignmentFactorProduct
    (n := n) hchildren]

theorem card_openRootMessageSpace_eq_two_pow_assignmentFactorProduct
    {n : Nat} [NeZero n] {cs : List RTree}
    (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C) :
    Fintype.card (OpenRootMessageSpace n cs) =
      2 ^ (cs.map (fun C =>
        Int.toNat
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C))).prod := by
  rw [card_openRootMessageSpace]
  rw [independentBranchDimension_eq_assignmentFactorProduct
    (n := n) hchildren]

theorem independentBranchDimension_toNat_Yassign_node
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C) :
    Int.toNat (Yassign n (RTree.node a cs)) =
      independentBranchDimension n cs := by
  have hT : RTree.PositiveWeights (RTree.node a cs) := by
    have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C :=
      ⟨ha, hchildren⟩
    simpa [RTree.PositiveWeights] using hnode
  rw [← Ydim_cast_eq_Yassign (n := n) hT]
  rw [Ydim_node_eq_independentBranchDimension]
  simp

theorem card_openRootMessageSpace_eq_two_pow_Yassign_node
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C) :
    Fintype.card (OpenRootMessageSpace n cs) =
      2 ^ Int.toNat (Yassign n (RTree.node a cs)) := by
  rw [card_openRootMessageSpace]
  rw [independentBranchDimension_toNat_Yassign_node
    (n := n) ha hchildren]

theorem independentBranchDimension_cast_eq_branchProductWith
    {n : Nat} [NeZero n] :
    ∀ {cs : List RTree},
      (∀ C ∈ cs, RTree.PositiveWeights C) →
      ((independentBranchDimension n cs : Nat) : ℤ) =
        branchProductWith (Yassign n) n cs
  | [], _ => by
      simp [independentBranchDimension, branchProductWith]
  | C :: rest, hchildren => by
      have hC : RTree.PositiveWeights C := hchildren C (by simp)
      have hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
        intro D hD
        exact hchildren D (by simp [hD])
      have htail :=
        independentBranchDimension_cast_eq_branchProductWith
          (n := n) hrest
      have hfactor := branchFactor_cast_eq_Yassign (n := n) hC
      change
        ((branchFactor n C * independentBranchDimension n rest : Nat) : ℤ) =
          ((nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C) *
            branchProductWith (Yassign n) n rest
      rw [Nat.cast_mul, hfactor, htail]

theorem independentBranchDimension_cast_eq_Yassign_node
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (_ha : 0 < a) (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C) :
    ((independentBranchDimension n cs : Nat) : ℤ) =
      Yassign n (RTree.node a cs) := by
  rw [independentBranchDimension_cast_eq_branchProductWith
    (n := n) hchildren]
  exact (Yassign_node n a cs).symm

theorem finrank_openRootMessageSpace_cast_eq_Yassign_node
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (ha : 0 < a) (hchildren : ∀ C ∈ cs, RTree.PositiveWeights C) :
    ((Module.finrank F2 (OpenRootMessageSpace n cs) : Nat) : ℤ) =
      Yassign n (RTree.node a cs) := by
  rw [finrank_openRootMessageSpace]
  exact independentBranchDimension_cast_eq_Yassign_node
    (n := n) ha hchildren

theorem openRootMessageSpace_finrank_eq_Yassign_of_positiveWeights
    {n : Nat} [NeZero n] {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    ((Module.finrank F2 (OpenRootMessageSpace n cs) : Nat) : ℤ) =
      Yassign n (RTree.node a cs) := by
  have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
    simpa [RTree.PositiveWeights] using hT
  exact finrank_openRootMessageSpace_cast_eq_Yassign_node
    (n := n) hnode.1 hnode.2

end RawPrimitive

end TreeGraph
