import Core4loop.TriangleLeaf.LeafProfileKernelCoordinates

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable instance instFintypeLeafScalarProfileKernel
    {n a : ℕ} [NeZero n] :
    Fintype (LeafScalarProfileKernel n a) := by
  classical
  letI : Finite (LeafScalarProfileKernel n a) :=
    Finite.of_injective
      (fun x : LeafScalarProfileKernel n a => (x.1 : LeafScalarProfile n a))
      (fun _ _ h => Subtype.ext h)
  exact Fintype.ofFinite (LeafScalarProfileKernel n a)

noncomputable instance instFintypeLeafVisibleProfileKernel
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype (LeafVisibleProfileKernel n a d hd) := by
  classical
  exact Fintype.ofEquiv (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
    (leafVisibleProfileKernelEquivIndex (n := n) (a := a) (d := d) hd).symm

theorem leafScalarProfileSum_single_zeroVec
    {n a : ℕ} [NeZero n] (r : F) :
    leafScalarProfileSum (n := n) (a := a)
        (fun p : PVec n a => if p = (zeroVec : PVec n a) then r else 0)
      =
      r := by
  change
    (∑ p : PVec n a,
      (if p = (zeroVec : PVec n a) then r else 0)) = r
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · simp
  · intro p _ hp
    simp [hp]
  · simp

theorem leafScalarProfileSum_surjective {n a : ℕ} [NeZero n] :
    Function.Surjective (leafScalarProfileSum (n := n) (a := a)) := by
  intro r
  refine ⟨fun p : PVec n a => if p = (zeroVec : PVec n a) then r else 0, ?_⟩
  exact leafScalarProfileSum_single_zeroVec (n := n) (a := a) r

theorem finrank_LeafScalarProfile {n a : ℕ} [NeZero n] :
    Module.finrank F (LeafScalarProfile n a) = n ^ (a - 1) := by
  calc
    Module.finrank F (LeafScalarProfile n a)
        = Fintype.card (PVec n a) := by
            rw [← Module.finrank_fintype_fun_eq_card (R := F) (η := PVec n a)]
    _ = n ^ (a - 1) := card_vec n (a - 1)

theorem finrank_LeafScalarProfileKernel_add_one
    {n a : ℕ} [NeZero n] :
    Module.finrank F (LeafScalarProfileKernel n a) + 1 =
      n ^ (a - 1) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (leafScalarProfileSum (n := n) (a := a))
  have hsurj :
      LinearMap.range (leafScalarProfileSum (n := n) (a := a)) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (leafScalarProfileSum_surjective (n := n) (a := a))
  rw [hsurj, finrank_top, finrank_LeafScalarProfile (n := n) (a := a)] at hnull
  simpa [LeafScalarProfileKernel, Nat.add_comm] using hnull

theorem finrank_LeafScalarProfileKernel
    {n a : ℕ} [NeZero n] :
    Module.finrank F (LeafScalarProfileKernel n a) =
      n ^ (a - 1) - 1 := by
  have h := finrank_LeafScalarProfileKernel_add_one (n := n) (a := a)
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hpow : 0 < n ^ (a - 1) := Nat.pow_pos hnpos
  omega

theorem card_LeafScalarProfileKernel_eq_pow_finrank
    {n a : ℕ} [NeZero n] :
    Fintype.card (LeafScalarProfileKernel n a) =
      2 ^ Module.finrank F (LeafScalarProfileKernel n a) := by
  rw [← Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

theorem card_LeafScalarProfileKernel
    {n a : ℕ} [NeZero n] :
    Fintype.card (LeafScalarProfileKernel n a) =
      2 ^ (n ^ (a - 1) - 1) := by
  rw [card_LeafScalarProfileKernel_eq_pow_finrank,
    finrank_LeafScalarProfileKernel (n := n) (a := a)]

theorem finrank_LeafVisibleProfileKernel
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (LeafVisibleProfileKernel n a d hd) =
      (n ^ d - (n - 1)) * (n ^ (a - 1) - 1) := by
  calc
    Module.finrank F (LeafVisibleProfileKernel n a d hd)
        =
        Module.finrank F (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a) := by
          exact LinearEquiv.finrank_eq
            (leafVisibleProfileKernelEquivIndex (n := n) (a := a) (d := d) hd)
    _ =
        Fintype.card (PassiveVisibleIndex n d hd) *
          Module.finrank F (LeafScalarProfileKernel n a) := by
          simp [Module.finrank_pi_fintype]
    _ =
        (n ^ d - (n - 1)) * (n ^ (a - 1) - 1) := by
          rw [card_PassiveVisibleIndex (n := n) (d := d) hd,
            finrank_LeafScalarProfileKernel (n := n) (a := a)]

theorem card_LeafVisibleProfileKernel
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype.card (LeafVisibleProfileKernel n a d hd) =
      (2 ^ (n ^ (a - 1) - 1)) ^ (n ^ d - (n - 1)) := by
  classical
  rw [Fintype.card_congr
    (leafVisibleProfileKernelEquivIndex (n := n) (a := a) (d := d) hd).toEquiv]
  rw [Fintype.card_fun,
    card_LeafScalarProfileKernel (n := n) (a := a),
    card_PassiveVisibleIndex (n := n) (d := d) hd]

end

end TriangleLeaf
end Core4loop
