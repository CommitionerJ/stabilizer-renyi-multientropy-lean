import Core4loop.Basic

namespace Core4loop

noncomputable section

/-!
Intrinsic quotients of linear-map ranges.

Every denominator below is a submodule of the actual range subtype, rather
than an ambient image that is only informally identified with that subtype.
-/

variable {K C D E V : Type*}
  [DivisionRing K]
  [AddCommGroup C] [Module K C]
  [AddCommGroup D] [Module K D]
  [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]

def restrictedImage (f : C →ₗ[K] E) (L : Submodule K C) :
    Submodule K (LinearMap.range f) :=
  LinearMap.range (f.rangeRestrict.comp L.subtype)

theorem restrictedImage_eq_map
    (f : C →ₗ[K] E) (L : Submodule K C) :
    restrictedImage f L = Submodule.map f.rangeRestrict L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem restrictedImage_mono
    (f : C →ₗ[K] E) {L M : Submodule K C} (hLM : L ≤ M) :
    restrictedImage f L ≤ restrictedImage f M := by
  rw [restrictedImage_eq_map, restrictedImage_eq_map]
  exact Submodule.map_mono hLM

def rangeQuotientMap (f : C →ₗ[K] E) (L : Submodule K C) :
    C →ₗ[K] (LinearMap.range f ⧸ restrictedImage f L) :=
  (Submodule.mkQ (restrictedImage f L)).comp f.rangeRestrict

theorem ker_rangeQuotientMap
    (f : C →ₗ[K] E) (L : Submodule K C) :
    LinearMap.ker (rangeQuotientMap f L) = L ⊔ LinearMap.ker f := by
  ext x
  constructor
  · intro hx
    have hxImage :
        f.rangeRestrict x ∈ restrictedImage f L := by
      exact
        (Submodule.Quotient.mk_eq_zero
          (p := restrictedImage f L)).mp
          (LinearMap.mem_ker.mp hx)
    rcases hxImage with ⟨y, hy⟩
    have hfy : f y.1 = f x := congrArg Subtype.val hy
    have hk : x - y.1 ∈ LinearMap.ker f := by
      apply LinearMap.mem_ker.mpr
      simp [hfy]
    have hsum : y.1 + (x - y.1) ∈ L ⊔ LinearMap.ker f :=
      Submodule.add_mem_sup y.2 hk
    simpa using hsum
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply
      (Submodule.Quotient.mk_eq_zero
        (p := restrictedImage f L)).mpr
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    simp [LinearMap.mem_ker.mp hz]

theorem rangeQuotientMap_surjective
    (f : C →ₗ[K] E) (L : Submodule K C) :
    Function.Surjective (rangeQuotientMap f L) := by
  exact
    (Submodule.mkQ_surjective (restrictedImage f L)).comp
      (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict f))

noncomputable def rangeQuotientSwapEquiv
    (f : C →ₗ[K] E) (g : C →ₗ[K] V) :
    (LinearMap.range f ⧸ restrictedImage f (LinearMap.ker g)) ≃ₗ[K]
      (LinearMap.range g ⧸ restrictedImage g (LinearMap.ker f)) := by
  let qf := rangeQuotientMap f (LinearMap.ker g)
  let qg := rangeQuotientMap g (LinearMap.ker f)
  have hqf : Function.Surjective qf :=
    rangeQuotientMap_surjective f (LinearMap.ker g)
  have hqg : Function.Surjective qg :=
    rangeQuotientMap_surjective g (LinearMap.ker f)
  have hker : LinearMap.ker qf = LinearMap.ker qg := by
    calc
      LinearMap.ker qf =
          LinearMap.ker g ⊔ LinearMap.ker f :=
        ker_rangeQuotientMap f (LinearMap.ker g)
      _ = LinearMap.ker f ⊔ LinearMap.ker g := sup_comm _ _
      _ = LinearMap.ker qg :=
        (ker_rangeQuotientMap g (LinearMap.ker f)).symm
  exact
    ((LinearMap.quotKerEquivOfSurjective qf hqf).symm.trans
      (Submodule.quotEquivOfEq _ _ hker)).trans
        (LinearMap.quotKerEquivOfSurjective qg hqg)

noncomputable def barO
    (alpha : C →ₗ[K] D) (O : C →ₗ[K] E)
    (halpha : Function.Surjective alpha) :
    D →ₗ[K]
      (LinearMap.range O ⧸ restrictedImage O (LinearMap.ker alpha)) := by
  let q := rangeQuotientMap O (LinearMap.ker alpha)
  have hker : LinearMap.ker alpha ≤ LinearMap.ker q := by
    rw [ker_rangeQuotientMap]
    exact le_sup_left
  exact
    ((LinearMap.ker alpha).liftQ q hker).comp
      (LinearMap.quotKerEquivOfSurjective alpha halpha).symm.toLinearMap

theorem barO_apply_alpha
    (alpha : C →ₗ[K] D) (O : C →ₗ[K] E)
    (halpha : Function.Surjective alpha) (c : C) :
    barO alpha O halpha (alpha c) =
      rangeQuotientMap O (LinearMap.ker alpha) c := by
  unfold barO
  dsimp only [LinearMap.comp_apply]
  rw [show
      (LinearMap.quotKerEquivOfSurjective alpha halpha).symm.toLinearMap
          (alpha c) =
        Submodule.Quotient.mk c by
      exact
        LinearMap.quotKerEquivOfSurjective_symm_apply
          alpha halpha c]
  exact Submodule.liftQ_apply _ _ c

theorem barO_surjective
    (alpha : C →ₗ[K] D) (O : C →ₗ[K] E)
    (halpha : Function.Surjective alpha) :
    Function.Surjective (barO alpha O halpha) := by
  intro x
  rcases rangeQuotientMap_surjective O (LinearMap.ker alpha) x with ⟨c, rfl⟩
  exact ⟨alpha c, barO_apply_alpha alpha O halpha c⟩

theorem map_barO_ker_eq_map_mkQ_restrictedImage_ker_comp
    (alpha : C →ₗ[K] D) (rho : D →ₗ[K] V) (O : C →ₗ[K] E)
    (halpha : Function.Surjective alpha) :
    Submodule.map (barO alpha O halpha) (LinearMap.ker rho) =
      Submodule.map
        (Submodule.mkQ (restrictedImage O (LinearMap.ker alpha)))
        (restrictedImage O (LinearMap.ker (rho.comp alpha))) := by
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases halpha d with ⟨c, rfl⟩
    refine ⟨O.rangeRestrict c, ?_, ?_⟩
    · refine ⟨⟨c, ?_⟩, rfl⟩
      apply LinearMap.mem_ker.mpr
      exact LinearMap.mem_ker.mp hd
    · exact (barO_apply_alpha alpha O halpha c).symm
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨c, hc⟩
    rw [← hc]
    refine ⟨alpha c.1, ?_, ?_⟩
    · apply LinearMap.mem_ker.mpr
      exact LinearMap.mem_ker.mp c.2
    · exact barO_apply_alpha alpha O halpha c.1

noncomputable def secondQuotientEquiv
    (alpha : C →ₗ[K] D) (rho : D →ₗ[K] V) (O : C →ₗ[K] E)
    (halpha : Function.Surjective alpha) :
    (LinearMap.range O ⧸
        restrictedImage O (LinearMap.ker (rho.comp alpha))) ≃ₗ[K]
      ((LinearMap.range O ⧸
          restrictedImage O (LinearMap.ker alpha)) ⧸
        Submodule.map (barO alpha O halpha) (LinearMap.ker rho)) := by
  let S := restrictedImage O (LinearMap.ker alpha)
  let T := restrictedImage O (LinearMap.ker (rho.comp alpha))
  have hker :
      LinearMap.ker alpha ≤ LinearMap.ker (rho.comp alpha) := by
    intro c hc
    apply LinearMap.mem_ker.mpr
    simp [LinearMap.mem_ker.mp hc]
  have hST : S ≤ T := restrictedImage_mono O hker
  exact
    (Submodule.quotientQuotientEquivQuotient S T hST).symm.trans
      (Submodule.quotEquivOfEq _ _
        (map_barO_ker_eq_map_mkQ_restrictedImage_ker_comp
          alpha rho O halpha).symm)

end

end Core4loop
