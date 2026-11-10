import Core3loop.ProfileEven

namespace Core3loop

noncomputable def evenVisibleBCoefOfHeadABC {a c n : ℕ} [NeZero n]
    (bhead : ScalarBCoef c n × ScalarBCoef c n) : BCoefABC a c n :=
  fun t z => (evenPlaneCoordInv (a := a) (n := n) (bhead.1 t z, bhead.2 t z)).1

noncomputable def evenVisibleCCoefOfHeadABC {a b n : ℕ} [NeZero n]
    (chead : ScalarCCoef b n × ScalarCCoef b n) : CCoefABC a b n :=
  fun y r => (evenPlaneCoordInv (a := a) (n := n) (chead.1 y r, chead.2 y r)).1

noncomputable def evenTailBCoefOfModelABC {a c n : ℕ} [NeZero n]
    (XB : EvenTailBModelABC a c n) : BCoefABC a c n :=
  ((bUevenBCoefEquivEvenTailBModelABC (a := a) (c := c) (n := n)).symm XB).1

noncomputable def evenTailCCoefOfModelABC {a b n : ℕ} [NeZero n]
    (YC : EvenTailCModelABC a b n) : CCoefABC a b n :=
  ((cUevenCCoefEquivEvenTailCModelABC (a := a) (b := b) (n := n)).symm YC).1

noncomputable def evenBuildBCoefABC {a c n : ℕ} [NeZero n]
    (bhead : ScalarBCoef c n × ScalarBCoef c n) (XB : EvenTailBModelABC a c n) :
    BCoefABC a c n :=
  evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead +
    evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB

noncomputable def evenBuildCCoefABC {a b n : ℕ} [NeZero n]
    (chead : ScalarCCoef b n × ScalarCCoef b n) (YC : EvenTailCModelABC a b n) :
    CCoefABC a b n :=
  evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead +
    evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC

lemma evenHeadBPairABC_evenTailBCoefOfModelABC_eq_zero {a c n : ℕ} [NeZero n]
    (XB : EvenTailBModelABC a c n) :
    evenHeadBPairABC (a := a) (c := c) (n := n)
      (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB) = (0, 0) := by
  apply Prod.ext <;> funext t z
  · have hmem :
        evenPairMap (a := a) (n := n)
          (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB t z) = 0 := by
        simpa [evenTailBCoefOfModelABC] using
          (((bUevenBCoefEquivEvenTailBModelABC (a := a) (c := c) (n := n)).symm XB).2 t z)
    exact congrArg Prod.fst hmem
  · have hmem :
        evenPairMap (a := a) (n := n)
          (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB t z) = 0 := by
        simpa [evenTailBCoefOfModelABC] using
          (((bUevenBCoefEquivEvenTailBModelABC (a := a) (c := c) (n := n)).symm XB).2 t z)
    exact congrArg Prod.snd hmem

lemma evenHeadCPairABC_evenTailCCoefOfModelABC_eq_zero {a b n : ℕ} [NeZero n]
    (YC : EvenTailCModelABC a b n) :
    evenHeadCPairABC (a := a) (b := b) (n := n)
      (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC) = (0, 0) := by
  apply Prod.ext <;> funext y r
  · have hmem :
        evenPairMap (a := a) (n := n)
          (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y r) = 0 := by
        simpa [evenTailCCoefOfModelABC] using
          (((cUevenCCoefEquivEvenTailCModelABC (a := a) (b := b) (n := n)).symm YC).2 y r)
    exact congrArg Prod.fst hmem
  · have hmem :
        evenPairMap (a := a) (n := n)
          (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y r) = 0 := by
        simpa [evenTailCCoefOfModelABC] using
          (((cUevenCCoefEquivEvenTailCModelABC (a := a) (b := b) (n := n)).symm YC).2 y r)
    exact congrArg Prod.snd hmem

lemma evenHeadBPairABC_evenVisibleBCoefOfHeadABC_eq {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (bhead : ScalarBCoef c n × ScalarBCoef c n) :
    evenHeadBPairABC (a := a) (c := c) (n := n)
      (evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead) = bhead := by
  apply Prod.ext <;> funext t z
  · exact congrArg Prod.fst
      (evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2 (bhead.1 t z, bhead.2 t z))
  · exact congrArg Prod.snd
      (evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2 (bhead.1 t z, bhead.2 t z))

lemma evenHeadCPairABC_evenVisibleCCoefOfHeadABC_eq {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (chead : ScalarCCoef b n × ScalarCCoef b n) :
    evenHeadCPairABC (a := a) (b := b) (n := n)
      (evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead) = chead := by
  apply Prod.ext <;> funext y r
  · exact congrArg Prod.fst
      (evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2 (chead.1 y r, chead.2 y r))
  · exact congrArg Prod.snd
      (evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2 (chead.1 y r, chead.2 y r))

lemma evenHeadBPairABC_evenBuildBCoefABC_eq {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (bhead : ScalarBCoef c n × ScalarBCoef c n) (XB : EvenTailBModelABC a c n) :
    evenHeadBPairABC (a := a) (c := c) (n := n)
      (evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB) = bhead := by
  apply Prod.ext <;> funext t z
  · have hmem :
        evenPairMap (a := a) (n := n)
          (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB t z) = 0 := by
        simpa [evenTailBCoefOfModelABC] using
          (((bUevenBCoefEquivEvenTailBModelABC (a := a) (c := c) (n := n)).symm XB).2 t z)
    have hpair :
        evenPairMap (a := a) (n := n)
          (evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB t z) =
            (bhead.1 t z, bhead.2 t z) := by
      rw [show evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB t z =
          evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead t z +
            evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB t z by rfl]
      rw [LinearMap.map_add, hmem, add_zero]
      simpa using evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2 (bhead.1 t z, bhead.2 t z)
    exact congrArg Prod.fst hpair
  · have hmem :
        evenPairMap (a := a) (n := n)
          (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB t z) = 0 := by
        simpa [evenTailBCoefOfModelABC] using
          (((bUevenBCoefEquivEvenTailBModelABC (a := a) (c := c) (n := n)).symm XB).2 t z)
    have hpair :
        evenPairMap (a := a) (n := n)
          (evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB t z) =
            (bhead.1 t z, bhead.2 t z) := by
      rw [show evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB t z =
          evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead t z +
            evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB t z by rfl]
      rw [LinearMap.map_add, hmem, add_zero]
      simpa using evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2 (bhead.1 t z, bhead.2 t z)
    exact congrArg Prod.snd hpair

lemma evenHeadCPairABC_evenBuildCCoefABC_eq {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (chead : ScalarCCoef b n × ScalarCCoef b n) (YC : EvenTailCModelABC a b n) :
    evenHeadCPairABC (a := a) (b := b) (n := n)
      (evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC) = chead := by
  apply Prod.ext <;> funext y r
  · have hmem :
        evenPairMap (a := a) (n := n)
          (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y r) = 0 := by
        simpa [evenTailCCoefOfModelABC] using
          (((cUevenCCoefEquivEvenTailCModelABC (a := a) (b := b) (n := n)).symm YC).2 y r)
    have hpair :
        evenPairMap (a := a) (n := n)
          (evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC y r) =
            (chead.1 y r, chead.2 y r) := by
      rw [show evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC y r =
          evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead y r +
            evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y r by rfl]
      rw [LinearMap.map_add, hmem, add_zero]
      simpa using evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2 (chead.1 y r, chead.2 y r)
    exact congrArg Prod.fst hpair
  · have hmem :
        evenPairMap (a := a) (n := n)
          (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y r) = 0 := by
        simpa [evenTailCCoefOfModelABC] using
          (((cUevenCCoefEquivEvenTailCModelABC (a := a) (b := b) (n := n)).symm YC).2 y r)
    have hpair :
        evenPairMap (a := a) (n := n)
          (evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC y r) =
            (chead.1 y r, chead.2 y r) := by
      rw [show evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC y r =
          evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead y r +
            evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y r by rfl]
      rw [LinearMap.map_add, hmem, add_zero]
      simpa using evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2 (chead.1 y r, chead.2 y r)
    exact congrArg Prod.snd hpair

lemma evenVisibleBCoefABC_evenBuildBCoefABC_eq {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (bhead : ScalarBCoef c n × ScalarBCoef c n) (XB : EvenTailBModelABC a c n) :
    evenVisibleBCoefABC (a := a) (c := c) (n := n)
      (evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB) =
      evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead := by
  funext t z p
  have hfst :
      (evenHeadBPairABC (a := a) (c := c) (n := n)
        (evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB)).1 t z = bhead.1 t z := by
    exact congrFun (congrFun
      (congrArg Prod.fst
        (evenHeadBPairABC_evenBuildBCoefABC_eq (a := a) (c := c) (n := n) hn ha2 bhead XB)) t) z
  have hsnd :
      (evenHeadBPairABC (a := a) (c := c) (n := n)
        (evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB)).2 t z = bhead.2 t z := by
    exact congrFun (congrFun
      (congrArg Prod.snd
        (evenHeadBPairABC_evenBuildBCoefABC_eq (a := a) (c := c) (n := n) hn ha2 bhead XB)) t) z
  simp [evenVisibleBCoefABC, evenVisibleBCoefOfHeadABC, hfst, hsnd]

lemma evenVisibleCCoefABC_evenBuildCCoefABC_eq {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (chead : ScalarCCoef b n × ScalarCCoef b n) (YC : EvenTailCModelABC a b n) :
    evenVisibleCCoefABC (a := a) (b := b) (n := n)
      (evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC) =
      evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead := by
  funext y r p
  have hfst :
      (evenHeadCPairABC (a := a) (b := b) (n := n)
        (evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC)).1 y r = chead.1 y r := by
    exact congrFun (congrFun
      (congrArg Prod.fst
        (evenHeadCPairABC_evenBuildCCoefABC_eq (a := a) (b := b) (n := n) hn ha2 chead YC)) y) r
  have hsnd :
      (evenHeadCPairABC (a := a) (b := b) (n := n)
        (evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC)).2 y r = chead.2 y r := by
    exact congrFun (congrFun
      (congrArg Prod.snd
        (evenHeadCPairABC_evenBuildCCoefABC_eq (a := a) (b := b) (n := n) hn ha2 chead YC)) y) r
  simp [evenVisibleCCoefABC, evenVisibleCCoefOfHeadABC, hfst, hsnd]

lemma evenTailBCoefABC_evenBuildBCoefABC_eq {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (bhead : ScalarBCoef c n × ScalarBCoef c n) (XB : EvenTailBModelABC a c n) :
    evenTailBCoefABC (a := a) (c := c) (n := n)
      (evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB) =
      evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB := by
  funext t z p
  have hvisible :
      evenVisibleBCoefABC (a := a) (c := c) (n := n)
        (evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB) t z p =
      evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead t z p := by
    exact congrFun (congrFun
      (congrFun
        (evenVisibleBCoefABC_evenBuildBCoefABC_eq (a := a) (c := c) (n := n) hn ha2 bhead XB) t) z) p
  have hvisible' :
      evenVisibleBCoefABC (a := a) (c := c) (n := n)
        (evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead +
          evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB) t z p =
      evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead t z p := by
    simpa [evenBuildBCoefABC] using hvisible
  simp only [evenTailBCoefABC, evenBuildBCoefABC, Pi.add_apply]
  rw [hvisible']
  calc
    evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead t z p +
        evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB t z p +
        evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead t z p
      = (evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead t z p +
            evenVisibleBCoefOfHeadABC (a := a) (c := c) (n := n) bhead t z p) +
          evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB t z p := by
            ac_rfl
    _ = evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB t z p := by
          simp [F_add_self]

lemma evenTailCCoefABC_evenBuildCCoefABC_eq {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (chead : ScalarCCoef b n × ScalarCCoef b n) (YC : EvenTailCModelABC a b n) :
    evenTailCCoefABC (a := a) (b := b) (n := n)
      (evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC) =
      evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC := by
  funext y r p
  have hvisible :
      evenVisibleCCoefABC (a := a) (b := b) (n := n)
        (evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC) y r p =
      evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead y r p := by
    exact congrFun (congrFun
      (congrFun
        (evenVisibleCCoefABC_evenBuildCCoefABC_eq (a := a) (b := b) (n := n) hn ha2 chead YC) y) r) p
  have hvisible' :
      evenVisibleCCoefABC (a := a) (b := b) (n := n)
        (evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead +
          evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC) y r p =
      evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead y r p := by
    simpa [evenBuildCCoefABC] using hvisible
  simp only [evenTailCCoefABC, evenBuildCCoefABC, Pi.add_apply]
  rw [hvisible']
  calc
    evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead y r p +
        evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y r p +
        evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead y r p
      = (evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead y r p +
            evenVisibleCCoefOfHeadABC (a := a) (b := b) (n := n) chead y r p) +
          evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y r p := by
            ac_rfl
    _ = evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC y r p := by
          simp [F_add_self]

lemma evenTailBModelOfBCoefABC_evenBuildBCoefABC_eq {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (bhead : ScalarBCoef c n × ScalarBCoef c n) (XB : EvenTailBModelABC a c n) :
    evenTailBModelOfBCoefABC (a := a) (c := c) (n := n) hn ha2
      (evenBuildBCoefABC (a := a) (c := c) (n := n) bhead XB) = XB := by
  funext t z
  apply Subtype.ext
  exact congrFun (congrFun
    (evenTailBCoefABC_evenBuildBCoefABC_eq (a := a) (c := c) (n := n) hn ha2 bhead XB) t) z

lemma evenTailCModelOfCCoefABC_evenBuildCCoefABC_eq {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (chead : ScalarCCoef b n × ScalarCCoef b n) (YC : EvenTailCModelABC a b n) :
    evenTailCModelOfCCoefABC (a := a) (b := b) (n := n) hn ha2
      (evenBuildCCoefABC (a := a) (b := b) (n := n) chead YC) = YC := by
  funext y r
  apply Subtype.ext
  exact congrFun (congrFun
    (evenTailCCoefABC_evenBuildCCoefABC_eq (a := a) (b := b) (n := n) hn ha2 chead YC) y) r

lemma evenBuildBCoefABC_head_tail_eq {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (bcoef : BCoefABC a c n) :
    evenBuildBCoefABC (a := a) (c := c) (n := n)
      (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef)
      (evenTailBModelOfBCoefABC (a := a) (c := c) (n := n) hn ha2 bcoef) = bcoef := by
  simpa [evenBuildBCoefABC, evenVisibleBCoefOfHeadABC, evenTailBCoefOfModelABC,
    evenTailBModelOfBCoefABC] using
    evenVisibleBCoefABC_add_evenTailBCoefABC (a := a) (c := c) (n := n) bcoef

lemma evenBuildCCoefABC_head_tail_eq {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (ccoef : CCoefABC a b n) :
    evenBuildCCoefABC (a := a) (b := b) (n := n)
      (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef)
      (evenTailCModelOfCCoefABC (a := a) (b := b) (n := n) hn ha2 ccoef) = ccoef := by
  simpa [evenBuildCCoefABC, evenVisibleCCoefOfHeadABC, evenTailCCoefOfModelABC,
    evenTailCModelOfCCoefABC] using
    evenVisibleCCoefABC_add_evenTailCCoefABC (a := a) (b := b) (n := n) ccoef

noncomputable def evenDecomposeBCoefABCEquiv {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    BCoefABC a c n ≃ (ScalarBCoef c n × ScalarBCoef c n) × EvenTailBModelABC a c n where
  toFun bcoef := (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef,
    evenTailBModelOfBCoefABC (a := a) (c := c) (n := n) hn ha2 bcoef)
  invFun x := evenBuildBCoefABC (a := a) (c := c) (n := n) x.1 x.2
  left_inv := evenBuildBCoefABC_head_tail_eq (a := a) (c := c) (n := n) hn ha2
  right_inv := by
    intro x
    rcases x with ⟨bhead, XB⟩
    apply Prod.ext
    · exact evenHeadBPairABC_evenBuildBCoefABC_eq (a := a) (c := c) (n := n) hn ha2 bhead XB
    · exact evenTailBModelOfBCoefABC_evenBuildBCoefABC_eq
        (a := a) (c := c) (n := n) hn ha2 bhead XB

noncomputable def evenDecomposeCCoefABCEquiv {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    CCoefABC a b n ≃ (ScalarCCoef b n × ScalarCCoef b n) × EvenTailCModelABC a b n where
  toFun ccoef := (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef,
    evenTailCModelOfCCoefABC (a := a) (b := b) (n := n) hn ha2 ccoef)
  invFun x := evenBuildCCoefABC (a := a) (b := b) (n := n) x.1 x.2
  left_inv := evenBuildCCoefABC_head_tail_eq (a := a) (b := b) (n := n) hn ha2
  right_inv := by
    intro x
    rcases x with ⟨chead, YC⟩
    apply Prod.ext
    · exact evenHeadCPairABC_evenBuildCCoefABC_eq (a := a) (b := b) (n := n) hn ha2 chead YC
    · exact evenTailCModelOfCCoefABC_evenBuildCCoefABC_eq
        (a := a) (b := b) (n := n) hn ha2 chead YC

end Core3loop
