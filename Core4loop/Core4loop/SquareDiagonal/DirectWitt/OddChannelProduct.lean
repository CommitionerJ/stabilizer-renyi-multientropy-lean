import Core4loop.SquareDiagonal.DirectWitt.OddFreeCrossWitt

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

open Core4loop
open Core4loop.SquareDiagonal.EvenP

noncomputable section

/-! ## The seven literal constrained rows -/

abbrev DiamondOddSSSTAmbient
    (n d : Nat) [NeZero n] :=
  DiamondOddAxisTail n d →
    (CyclicCube n × CyclicCube n)

noncomputable def diamondOddSSSTSourceMap
    {n d : Nat} [NeZero n] :
    DiamondOddSSSTAmbient n d →ₗ[F]
      (DiamondOddAxisTail n d → CyclicCube n) where
  toFun x := fun wt =>
    cubeDiffJInv (x wt).1 + cubeDiffP (x wt).2
  map_add' x y := by
    funext wt
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' r x := by
    funext wt
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      map_smul, RingHom.id_apply]
    rw [smul_add]

@[simp] theorem diamondOddSSSTSourceMap_apply
    {n d : Nat} [NeZero n]
    (x : DiamondOddSSSTAmbient n d)
    (wt : DiamondOddAxisTail n d) :
    diamondOddSSSTSourceMap x wt =
      cubeDiffJInv (x wt).1 + cubeDiffP (x wt).2 :=
  rfl

abbrev DiamondOddSSSTSource
    (n d : Nat) [NeZero n] :=
  LinearMap.ker (diamondOddSSSTSourceMap (n := n) (d := d))

abbrev DiamondOddSTSSAmbient
    (n b : Nat) [NeZero n] :=
  DiamondOddAxisTail n b →
    (CyclicCube n × CyclicCube n)

noncomputable def diamondOddSTSSSourceMap
    {n b : Nat} [NeZero n] :
    DiamondOddSTSSAmbient n b →ₗ[F]
      (DiamondOddAxisTail n b → CyclicCube n) where
  toFun x := fun yt =>
    cubeDiffJInv (x yt).1 + cubeDiffR (x yt).2
  map_add' x y := by
    funext yt
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' r x := by
    funext yt
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      map_smul, RingHom.id_apply]
    rw [smul_add]

@[simp] theorem diamondOddSTSSSourceMap_apply
    {n b : Nat} [NeZero n]
    (x : DiamondOddSTSSAmbient n b)
    (yt : DiamondOddAxisTail n b) :
    diamondOddSTSSSourceMap x yt =
      cubeDiffJInv (x yt).1 + cubeDiffR (x yt).2 :=
  rfl

abbrev DiamondOddSTSSSource
    (n b : Nat) [NeZero n] :=
  LinearMap.ker (diamondOddSTSSSourceMap (n := n) (b := b))

abbrev DiamondOddSTSTAmbient
    (n b d : Nat) [NeZero n] :=
  DiamondOddAxisTail n b →
    DiamondOddAxisTail n d → CyclicCube n

noncomputable def diamondOddSTSTSourceMap
    {n b d : Nat} [NeZero n] :
    DiamondOddSTSTAmbient n b d →ₗ[F]
      DiamondOddSTSTAmbient n b d where
  toFun x := fun yt wt => cubeDiffJInv (x yt wt)
  map_add' x y := by
    funext yt wt
    simp only [Pi.add_apply, map_add]
  map_smul' r x := by
    funext yt wt
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem diamondOddSTSTSourceMap_apply
    {n b d : Nat} [NeZero n]
    (x : DiamondOddSTSTAmbient n b d)
    (yt : DiamondOddAxisTail n b)
    (wt : DiamondOddAxisTail n d) :
    diamondOddSTSTSourceMap x yt wt =
      cubeDiffJInv (x yt wt) :=
  rfl

abbrev DiamondOddSTSTSource
    (n b d : Nat) [NeZero n] :=
  LinearMap.ker
    (diamondOddSTSTSourceMap (n := n) (b := b) (d := d))

abbrev DiamondOddTSSSAmbient
    (n a : Nat) [NeZero n] :=
  DiamondOddAxisTail n a →
    (CyclicCube n × CyclicCube n)

noncomputable def diamondOddTSSSSourceMap
    {n a : Nat} [NeZero n] :
    DiamondOddTSSSAmbient n a →ₗ[F]
      (DiamondOddAxisTail n a → CyclicCube n) where
  toFun x := fun pt =>
    cubeDiffP (x pt).1 + cubeDiffR (x pt).2
  map_add' x y := by
    funext pt
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' r x := by
    funext pt
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      map_smul, RingHom.id_apply]
    rw [smul_add]

@[simp] theorem diamondOddTSSSSourceMap_apply
    {n a : Nat} [NeZero n]
    (x : DiamondOddTSSSAmbient n a)
    (pt : DiamondOddAxisTail n a) :
    diamondOddTSSSSourceMap x pt =
      cubeDiffP (x pt).1 + cubeDiffR (x pt).2 :=
  rfl

abbrev DiamondOddTSSSSource
    (n a : Nat) [NeZero n] :=
  LinearMap.ker (diamondOddTSSSSourceMap (n := n) (a := a))

abbrev DiamondOddTSSTAmbient
    (n a d : Nat) [NeZero n] :=
  DiamondOddAxisTail n a →
    DiamondOddAxisTail n d → CyclicCube n

noncomputable def diamondOddTSSTSourceMap
    {n a d : Nat} [NeZero n] :
    DiamondOddTSSTAmbient n a d →ₗ[F]
      DiamondOddTSSTAmbient n a d where
  toFun x := fun pt wt => cubeDiffP (x pt wt)
  map_add' x y := by
    funext pt wt
    simp only [Pi.add_apply, map_add]
  map_smul' r x := by
    funext pt wt
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem diamondOddTSSTSourceMap_apply
    {n a d : Nat} [NeZero n]
    (x : DiamondOddTSSTAmbient n a d)
    (pt : DiamondOddAxisTail n a)
    (wt : DiamondOddAxisTail n d) :
    diamondOddTSSTSourceMap x pt wt =
      cubeDiffP (x pt wt) :=
  rfl

abbrev DiamondOddTSSTSource
    (n a d : Nat) [NeZero n] :=
  LinearMap.ker
    (diamondOddTSSTSourceMap (n := n) (a := a) (d := d))

abbrev DiamondOddTTSSAmbient
    (n a b : Nat) [NeZero n] :=
  DiamondOddAxisTail n a →
    DiamondOddAxisTail n b → CyclicCube n

noncomputable def diamondOddTTSSSourceMap
    {n a b : Nat} [NeZero n] :
    DiamondOddTTSSAmbient n a b →ₗ[F]
      DiamondOddTTSSAmbient n a b where
  toFun x := fun pt yt => cubeDiffR (x pt yt)
  map_add' x y := by
    funext pt yt
    simp only [Pi.add_apply, map_add]
  map_smul' r x := by
    funext pt yt
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem diamondOddTTSSSourceMap_apply
    {n a b : Nat} [NeZero n]
    (x : DiamondOddTTSSAmbient n a b)
    (pt : DiamondOddAxisTail n a)
    (yt : DiamondOddAxisTail n b) :
    diamondOddTTSSSourceMap x pt yt =
      cubeDiffR (x pt yt) :=
  rfl

abbrev DiamondOddTTSSSource
    (n a b : Nat) [NeZero n] :=
  LinearMap.ker
    (diamondOddTTSSSourceMap (n := n) (a := a) (b := b))

/-! ## The complete literal 16-row family -/

inductive DiamondOddChannelRow where
  | ssss | ssst | ssts | sstt
  | stss | stst | stts | sttt
  | tsss | tsst | tsts | tstt
  | ttss | ttst | ttts | tttt
  deriving DecidableEq, Fintype

def DiamondOddChannelRowSpace
    (n a b c d : Nat) [NeZero n] :
    DiamondOddChannelRow → ModuleCat F
  | .ssss => ModuleCat.of F (DiamondOddScalarSource n)
  | .ssst => ModuleCat.of F (DiamondOddSSSTSource n d)
  | .ssts => ModuleCat.of F
      (DiamondOddAxisTail n c → DiamondOddScalarAmbient n)
  | .sstt => ModuleCat.of F
      (DiamondOddAxisTail n c →
        DiamondOddAxisTail n d → (CyclicCube n × CyclicCube n))
  | .stss => ModuleCat.of F (DiamondOddSTSSSource n b)
  | .stst => ModuleCat.of F (DiamondOddSTSTSource n b d)
  | .stts => ModuleCat.of F
      (DiamondOddAxisTail n b →
        DiamondOddAxisTail n c → (CyclicCube n × CyclicCube n))
  | .sttt => ModuleCat.of F
      (DiamondOddAxisTail n b →
        DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n)
  | .tsss => ModuleCat.of F (DiamondOddTSSSSource n a)
  | .tsst => ModuleCat.of F (DiamondOddTSSTSource n a d)
  | .tsts => ModuleCat.of F
      (DiamondOddAxisTail n a →
        DiamondOddAxisTail n c → (CyclicCube n × CyclicCube n))
  | .tstt => ModuleCat.of F
      (DiamondOddAxisTail n a →
        DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n)
  | .ttss => ModuleCat.of F (DiamondOddTTSSSource n a b)
  | .ttst => ModuleCat.of F
      (DiamondOddAxisTail n a →
        DiamondOddAxisTail n b →
          DiamondOddAxisTail n d → (Fin 0 → F))
  | .ttts => ModuleCat.of F
      (DiamondOddAxisTail n a →
        DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → CyclicCube n)
  | .tttt => ModuleCat.of F
      (DiamondOddAxisTail n a →
        DiamondOddAxisTail n b →
          DiamondOddAxisTail n c →
            DiamondOddAxisTail n d → (Fin 0 → F))

abbrev DiamondOddChannelProduct
    (n a b c d : Nat) [NeZero n] :=
  (r : DiamondOddChannelRow) →
    (DiamondOddChannelRowSpace n a b c d r : Type)

private theorem diamondOddPointedSource_coord_zero
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (cp : DiamondOddAxisChannel n a)
    (cy : DiamondOddAxisChannel n b)
    (cw : DiamondOddAxisChannel n d) :
    diamondOddPointedSourceMap hn x.1 cp cy cw = 0 := by
  have h := LinearMap.mem_ker.mp x.2
  exact congrFun (congrFun (congrFun h cp) cy) cw

private noncomputable def diamondOddChannelRead
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddPointedSource n a b c d hn) :
    DiamondOddChannelProduct n a b c d
  | .ssss => diamondOddPointedSSSSExtract hn x
  | .ssst =>
      ⟨fun wt =>
          (x.1.1 diamondOddChannelS diamondOddChannelS
              (diamondOddChannelT wt),
            x.1.2.1 diamondOddChannelS diamondOddChannelS
              (diamondOddChannelT wt)),
        LinearMap.mem_ker.mpr (by
          funext wt
          have h := diamondOddPointedSource_coord_zero x
            diamondOddChannelS diamondOddChannelS
              (diamondOddChannelT wt)
          rw [diamondOddPointedSourceMap_apply_SSST hn x.1 wt] at h
          exact h)⟩
  | .ssts => fun zt =>
      (x.1.1 diamondOddChannelS (diamondOddChannelT zt)
          diamondOddChannelS,
        x.1.2.1 diamondOddChannelS (diamondOddChannelT zt)
            diamondOddChannelS,
          x.1.2.2 diamondOddChannelS diamondOddChannelS
            (diamondOddChannelT zt))
  | .sstt => fun zt wt =>
      (x.1.1 diamondOddChannelS (diamondOddChannelT zt)
          (diamondOddChannelT wt),
        x.1.2.1 diamondOddChannelS (diamondOddChannelT zt)
          (diamondOddChannelT wt))
  | .stss =>
      ⟨fun yt =>
          (x.1.1 (diamondOddChannelT yt) diamondOddChannelS
              diamondOddChannelS,
            x.1.2.2 diamondOddChannelS (diamondOddChannelT yt)
              diamondOddChannelS),
        LinearMap.mem_ker.mpr (by
          funext yt
          have h := diamondOddPointedSource_coord_zero x
            diamondOddChannelS (diamondOddChannelT yt)
              diamondOddChannelS
          rw [diamondOddPointedSourceMap_apply_STSS hn x.1 yt] at h
          exact h)⟩
  | .stst =>
      ⟨fun yt wt =>
          x.1.1 (diamondOddChannelT yt) diamondOddChannelS
            (diamondOddChannelT wt),
        LinearMap.mem_ker.mpr (by
          funext yt wt
          have h := diamondOddPointedSource_coord_zero x
            diamondOddChannelS (diamondOddChannelT yt)
              (diamondOddChannelT wt)
          rw [diamondOddPointedSourceMap_apply_STST hn x.1 yt wt] at h
          exact h)⟩
  | .stts => fun yt zt =>
      (x.1.1 (diamondOddChannelT yt) (diamondOddChannelT zt)
          diamondOddChannelS,
        x.1.2.2 diamondOddChannelS (diamondOddChannelT yt)
          (diamondOddChannelT zt))
  | .sttt => fun yt zt wt =>
      x.1.1 (diamondOddChannelT yt) (diamondOddChannelT zt)
        (diamondOddChannelT wt)
  | .tsss =>
      ⟨fun pt =>
          (x.1.2.1 (diamondOddChannelT pt) diamondOddChannelS
              diamondOddChannelS,
            x.1.2.2 (diamondOddChannelT pt) diamondOddChannelS
              diamondOddChannelS),
        LinearMap.mem_ker.mpr (by
          funext pt
          have h := diamondOddPointedSource_coord_zero x
            (diamondOddChannelT pt) diamondOddChannelS
              diamondOddChannelS
          rw [diamondOddPointedSourceMap_apply_TSSS hn x.1 pt] at h
          exact h)⟩
  | .tsst =>
      ⟨fun pt wt =>
          x.1.2.1 (diamondOddChannelT pt) diamondOddChannelS
            (diamondOddChannelT wt),
        LinearMap.mem_ker.mpr (by
          funext pt wt
          have h := diamondOddPointedSource_coord_zero x
            (diamondOddChannelT pt) diamondOddChannelS
              (diamondOddChannelT wt)
          rw [diamondOddPointedSourceMap_apply_TSST hn x.1 pt wt] at h
          exact h)⟩
  | .tsts => fun pt zt =>
      (x.1.2.1 (diamondOddChannelT pt) (diamondOddChannelT zt)
          diamondOddChannelS,
        x.1.2.2 (diamondOddChannelT pt) diamondOddChannelS
          (diamondOddChannelT zt))
  | .tstt => fun pt zt wt =>
      x.1.2.1 (diamondOddChannelT pt) (diamondOddChannelT zt)
        (diamondOddChannelT wt)
  | .ttss =>
      ⟨fun pt yt =>
          x.1.2.2 (diamondOddChannelT pt) (diamondOddChannelT yt)
            diamondOddChannelS,
        LinearMap.mem_ker.mpr (by
          funext pt yt
          have h := diamondOddPointedSource_coord_zero x
            (diamondOddChannelT pt) (diamondOddChannelT yt)
              diamondOddChannelS
          rw [diamondOddPointedSourceMap_apply_TTSS hn x.1 pt yt] at h
          exact h)⟩
  | .ttst => fun _ _ _ i => Fin.elim0 i
  | .ttts => fun pt yt zt =>
      x.1.2.2 (diamondOddChannelT pt) (diamondOddChannelT yt)
        (diamondOddChannelT zt)
  | .tttt => fun _ _ _ _ i => Fin.elim0 i

private noncomputable def diamondOddChannelBuildAmbient
    {n a b c d : Nat} [NeZero n]
    (rows : DiamondOddChannelProduct n a b c d) :
    DiamondOddPointedAmbient n a b c d :=
  (fun cy cz cw =>
      match cy, cz, cw with
      | none, none, none => (rows .ssss).1.1
      | none, none, some wt => ((rows .ssst).1 wt).1
      | none, some zt, none => ((rows .ssts) zt).1
      | none, some zt, some wt => ((rows .sstt) zt wt).1
      | some yt, none, none => ((rows .stss).1 yt).1
      | some yt, none, some wt => (rows .stst).1 yt wt
      | some yt, some zt, none => ((rows .stts) yt zt).1
      | some yt, some zt, some wt => (rows .sttt) yt zt wt,
    fun cp cz cw =>
      match cp, cz, cw with
      | none, none, none => (rows .ssss).1.2.1
      | none, none, some wt => ((rows .ssst).1 wt).2
      | none, some zt, none => ((rows .ssts) zt).2.1
      | none, some zt, some wt => ((rows .sstt) zt wt).2
      | some pt, none, none => ((rows .tsss).1 pt).1
      | some pt, none, some wt => (rows .tsst).1 pt wt
      | some pt, some zt, none => ((rows .tsts) pt zt).1
      | some pt, some zt, some wt => (rows .tstt) pt zt wt,
    fun cp cy cz =>
      match cp, cy, cz with
      | none, none, none => (rows .ssss).1.2.2
      | none, none, some zt => ((rows .ssts) zt).2.2
      | none, some yt, none => ((rows .stss).1 yt).2
      | none, some yt, some zt => ((rows .stts) yt zt).2
      | some pt, none, none => ((rows .tsss).1 pt).2
      | some pt, none, some zt => ((rows .tsts) pt zt).2
      | some pt, some yt, none => (rows .ttss).1 pt yt
      | some pt, some yt, some zt => (rows .ttts) pt yt zt)

private theorem diamondOddChannelBuildAmbient_mem
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (rows : DiamondOddChannelProduct n a b c d) :
    diamondOddChannelBuildAmbient rows ∈
      DiamondOddPointedSource n a b c d hn := by
  apply LinearMap.mem_ker.mpr
  funext cp cy cw
  simp only [Pi.zero_apply]
  cases cp with
  | none =>
      cases cy with
      | none =>
          cases cw with
          | none =>
              change
                diamondOddPointedSourceMap hn
                  (diamondOddChannelBuildAmbient rows)
                  diamondOddChannelS diamondOddChannelS
                    diamondOddChannelS = 0
              rw [diamondOddPointedSourceMap_apply_SSSS]
              change diamondOddScalarSourceMap (rows .ssss).1 = 0
              exact LinearMap.mem_ker.mp (rows .ssss).2
          | some wt =>
              change
                diamondOddPointedSourceMap hn
                  (diamondOddChannelBuildAmbient rows)
                  diamondOddChannelS diamondOddChannelS
                    (diamondOddChannelT wt) = 0
              rw [diamondOddPointedSourceMap_apply_SSST]
              change diamondOddSSSTSourceMap (rows .ssst).1 wt = 0
              exact congrFun (LinearMap.mem_ker.mp (rows .ssst).2) wt
      | some yt =>
          cases cw with
          | none =>
              change
                diamondOddPointedSourceMap hn
                  (diamondOddChannelBuildAmbient rows)
                  diamondOddChannelS (diamondOddChannelT yt)
                    diamondOddChannelS = 0
              rw [diamondOddPointedSourceMap_apply_STSS]
              change diamondOddSTSSSourceMap (rows .stss).1 yt = 0
              exact congrFun (LinearMap.mem_ker.mp (rows .stss).2) yt
          | some wt =>
              change
                diamondOddPointedSourceMap hn
                  (diamondOddChannelBuildAmbient rows)
                  diamondOddChannelS (diamondOddChannelT yt)
                    (diamondOddChannelT wt) = 0
              rw [diamondOddPointedSourceMap_apply_STST]
              change diamondOddSTSTSourceMap (rows .stst).1 yt wt = 0
              exact congrFun
                (congrFun (LinearMap.mem_ker.mp (rows .stst).2) yt) wt
  | some pt =>
      cases cy with
      | none =>
          cases cw with
          | none =>
              change
                diamondOddPointedSourceMap hn
                  (diamondOddChannelBuildAmbient rows)
                  (diamondOddChannelT pt) diamondOddChannelS
                    diamondOddChannelS = 0
              rw [diamondOddPointedSourceMap_apply_TSSS]
              change diamondOddTSSSSourceMap (rows .tsss).1 pt = 0
              exact congrFun (LinearMap.mem_ker.mp (rows .tsss).2) pt
          | some wt =>
              change
                diamondOddPointedSourceMap hn
                  (diamondOddChannelBuildAmbient rows)
                  (diamondOddChannelT pt) diamondOddChannelS
                    (diamondOddChannelT wt) = 0
              rw [diamondOddPointedSourceMap_apply_TSST]
              change diamondOddTSSTSourceMap (rows .tsst).1 pt wt = 0
              exact congrFun
                (congrFun (LinearMap.mem_ker.mp (rows .tsst).2) pt) wt
      | some yt =>
          cases cw with
          | none =>
              change
                diamondOddPointedSourceMap hn
                  (diamondOddChannelBuildAmbient rows)
                  (diamondOddChannelT pt) (diamondOddChannelT yt)
                    diamondOddChannelS = 0
              rw [diamondOddPointedSourceMap_apply_TTSS]
              change diamondOddTTSSSourceMap (rows .ttss).1 pt yt = 0
              exact congrFun
                (congrFun (LinearMap.mem_ker.mp (rows .ttss).2) pt) yt
          | some wt =>
              change
                diamondOddPointedSourceMap hn
                  (diamondOddChannelBuildAmbient rows)
                  (diamondOddChannelT pt) (diamondOddChannelT yt)
                    (diamondOddChannelT wt) = 0
              rw [diamondOddPointedSourceMap_apply_TTST]

private noncomputable def diamondOddChannelBuild
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (rows : DiamondOddChannelProduct n a b c d) :
    DiamondOddPointedSource n a b c d hn :=
  ⟨diamondOddChannelBuildAmbient rows,
    diamondOddChannelBuildAmbient_mem hn rows⟩

private theorem diamondOddChannelBuild_read
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddPointedSource n a b c d hn) :
    diamondOddChannelBuild hn (diamondOddChannelRead hn x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · funext cy cz cw
    cases cy <;> cases cz <;> cases cw <;> rfl
  · apply Prod.ext
    · funext cp cz cw
      cases cp <;> cases cz <;> cases cw <;> rfl
    · funext cp cy cz
      cases cp <;> cases cy <;> cases cz <;> rfl

private theorem diamondOddChannelRead_build
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (rows : DiamondOddChannelProduct n a b c d) :
    diamondOddChannelRead hn (diamondOddChannelBuild hn rows) = rows := by
  funext r
  cases r with
  | ssss =>
      apply Subtype.ext
      rfl
  | ssst =>
      apply Subtype.ext
      rfl
  | ssts => rfl
  | sstt => rfl
  | stss =>
      apply Subtype.ext
      rfl
  | stst =>
      apply Subtype.ext
      rfl
  | stts => rfl
  | sttt => rfl
  | tsss =>
      apply Subtype.ext
      rfl
  | tsst =>
      apply Subtype.ext
      rfl
  | tsts => rfl
  | tstt => rfl
  | ttss =>
      apply Subtype.ext
      rfl
  | ttst =>
      funext pt yt wt i
      exact Fin.elim0 i
  | ttts => rfl
  | tttt =>
      funext pt yt zt wt i
      exact Fin.elim0 i

private theorem diamondOddChannelBuild_add
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (x y : DiamondOddChannelProduct n a b c d) :
    diamondOddChannelBuild hn (x + y) =
      diamondOddChannelBuild hn x + diamondOddChannelBuild hn y := by
  apply Subtype.ext
  apply Prod.ext
  · funext cy cz cw
    cases cy <;> cases cz <;> cases cw <;> rfl
  · apply Prod.ext
    · funext cp cz cw
      cases cp <;> cases cz <;> cases cw <;> rfl
    · funext cp cy cz
      cases cp <;> cases cy <;> cases cz <;> rfl

private theorem diamondOddChannelBuild_smul
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (s : F) (x : DiamondOddChannelProduct n a b c d) :
    diamondOddChannelBuild hn (s • x) =
      s • diamondOddChannelBuild hn x := by
  apply Subtype.ext
  apply Prod.ext
  · funext cy cz cw
    cases cy <;> cases cz <;> cases cw <;> rfl
  · apply Prod.ext
    · funext cp cz cw
      cases cp <;> cases cz <;> cases cw <;> rfl
    · funext cp cy cz
      cases cp <;> cases cy <;> cases cz <;> rfl

private theorem diamondOddChannelBuild_injective
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    Function.Injective
      (diamondOddChannelBuild
        (n := n) (a := a) (b := b) (c := c) (d := d) hn) := by
  intro x y h
  calc
    x = diamondOddChannelRead hn (diamondOddChannelBuild hn x) :=
      (diamondOddChannelRead_build hn x).symm
    _ = diamondOddChannelRead hn (diamondOddChannelBuild hn y) :=
      congrArg (diamondOddChannelRead hn) h
    _ = y := diamondOddChannelRead_build hn y

noncomputable def diamondOddChannelProductEquiv
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddPointedSource n a b c d hn ≃ₗ[F]
      DiamondOddChannelProduct n a b c d where
  toFun := diamondOddChannelRead hn
  invFun := diamondOddChannelBuild hn
  left_inv := diamondOddChannelBuild_read hn
  right_inv := diamondOddChannelRead_build hn
  map_add' x y := by
    apply diamondOddChannelBuild_injective hn
    rw [diamondOddChannelBuild_read, diamondOddChannelBuild_add,
      diamondOddChannelBuild_read, diamondOddChannelBuild_read]
  map_smul' s x := by
    apply diamondOddChannelBuild_injective hn
    rw [diamondOddChannelBuild_read, diamondOddChannelBuild_smul,
      diamondOddChannelBuild_read]
    simp only [RingHom.id_apply]

/-! ## Exact sixteen forward projection contracts -/

@[simp] theorem diamondOddChannelProductEquiv_apply_SSSS
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn) :
    ((diamondOddChannelProductEquiv hn x) .ssss).1 =
      (x.1.1 diamondOddChannelS diamondOddChannelS
          diamondOddChannelS,
        x.1.2.1 diamondOddChannelS diamondOddChannelS
          diamondOddChannelS,
        x.1.2.2 diamondOddChannelS diamondOddChannelS
          diamondOddChannelS) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_SSST
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (wt : DiamondOddAxisTail n d) :
    ((diamondOddChannelProductEquiv hn x) .ssst).1 wt =
      (x.1.1 diamondOddChannelS diamondOddChannelS
          (diamondOddChannelT wt),
        x.1.2.1 diamondOddChannelS diamondOddChannelS
          (diamondOddChannelT wt)) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_SSTS
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (zt : DiamondOddAxisTail n c) :
    (diamondOddChannelProductEquiv hn x) .ssts zt =
      (x.1.1 diamondOddChannelS (diamondOddChannelT zt)
          diamondOddChannelS,
        x.1.2.1 diamondOddChannelS (diamondOddChannelT zt)
            diamondOddChannelS,
          x.1.2.2 diamondOddChannelS diamondOddChannelS
            (diamondOddChannelT zt)) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_SSTT
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (zt : DiamondOddAxisTail n c)
    (wt : DiamondOddAxisTail n d) :
    (diamondOddChannelProductEquiv hn x) .sstt zt wt =
      (x.1.1 diamondOddChannelS (diamondOddChannelT zt)
          (diamondOddChannelT wt),
        x.1.2.1 diamondOddChannelS (diamondOddChannelT zt)
          (diamondOddChannelT wt)) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_STSS
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (yt : DiamondOddAxisTail n b) :
    ((diamondOddChannelProductEquiv hn x) .stss).1 yt =
      (x.1.1 (diamondOddChannelT yt) diamondOddChannelS
          diamondOddChannelS,
        x.1.2.2 diamondOddChannelS (diamondOddChannelT yt)
          diamondOddChannelS) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_STST
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (yt : DiamondOddAxisTail n b)
    (wt : DiamondOddAxisTail n d) :
    ((diamondOddChannelProductEquiv hn x) .stst).1 yt wt =
      x.1.1 (diamondOddChannelT yt) diamondOddChannelS
        (diamondOddChannelT wt) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_STTS
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (yt : DiamondOddAxisTail n b)
    (zt : DiamondOddAxisTail n c) :
    (diamondOddChannelProductEquiv hn x) .stts yt zt =
      (x.1.1 (diamondOddChannelT yt) (diamondOddChannelT zt)
          diamondOddChannelS,
        x.1.2.2 diamondOddChannelS (diamondOddChannelT yt)
          (diamondOddChannelT zt)) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_STTT
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (yt : DiamondOddAxisTail n b)
    (zt : DiamondOddAxisTail n c)
    (wt : DiamondOddAxisTail n d) :
    (diamondOddChannelProductEquiv hn x) .sttt yt zt wt =
      x.1.1 (diamondOddChannelT yt) (diamondOddChannelT zt)
        (diamondOddChannelT wt) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_TSSS
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (pt : DiamondOddAxisTail n a) :
    ((diamondOddChannelProductEquiv hn x) .tsss).1 pt =
      (x.1.2.1 (diamondOddChannelT pt) diamondOddChannelS
          diamondOddChannelS,
        x.1.2.2 (diamondOddChannelT pt) diamondOddChannelS
          diamondOddChannelS) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_TSST
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (pt : DiamondOddAxisTail n a)
    (wt : DiamondOddAxisTail n d) :
    ((diamondOddChannelProductEquiv hn x) .tsst).1 pt wt =
      x.1.2.1 (diamondOddChannelT pt) diamondOddChannelS
        (diamondOddChannelT wt) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_TSTS
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (pt : DiamondOddAxisTail n a)
    (zt : DiamondOddAxisTail n c) :
    (diamondOddChannelProductEquiv hn x) .tsts pt zt =
      (x.1.2.1 (diamondOddChannelT pt) (diamondOddChannelT zt)
          diamondOddChannelS,
        x.1.2.2 (diamondOddChannelT pt) diamondOddChannelS
          (diamondOddChannelT zt)) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_TSTT
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (pt : DiamondOddAxisTail n a)
    (zt : DiamondOddAxisTail n c)
    (wt : DiamondOddAxisTail n d) :
    (diamondOddChannelProductEquiv hn x) .tstt pt zt wt =
      x.1.2.1 (diamondOddChannelT pt) (diamondOddChannelT zt)
        (diamondOddChannelT wt) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_TTSS
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (pt : DiamondOddAxisTail n a)
    (yt : DiamondOddAxisTail n b) :
    ((diamondOddChannelProductEquiv hn x) .ttss).1 pt yt =
      x.1.2.2 (diamondOddChannelT pt) (diamondOddChannelT yt)
        diamondOddChannelS :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_TTST
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (pt : DiamondOddAxisTail n a)
    (yt : DiamondOddAxisTail n b)
    (wt : DiamondOddAxisTail n d) :
    (diamondOddChannelProductEquiv hn x) .ttst pt yt wt =
      (0 : Fin 0 → F) := by
  funext i
  exact Fin.elim0 i

@[simp] theorem diamondOddChannelProductEquiv_apply_TTTS
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (pt : DiamondOddAxisTail n a)
    (yt : DiamondOddAxisTail n b)
    (zt : DiamondOddAxisTail n c) :
    (diamondOddChannelProductEquiv hn x) .ttts pt yt zt =
      x.1.2.2 (diamondOddChannelT pt) (diamondOddChannelT yt)
        (diamondOddChannelT zt) :=
  rfl

@[simp] theorem diamondOddChannelProductEquiv_apply_TTTT
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn)
    (pt : DiamondOddAxisTail n a)
    (yt : DiamondOddAxisTail n b)
    (zt : DiamondOddAxisTail n c)
    (wt : DiamondOddAxisTail n d) :
    (diamondOddChannelProductEquiv hn x) .tttt pt yt zt wt =
      (0 : Fin 0 → F) := by
  funext i
  exact Fin.elim0 i

/-! ## Six literal active phases on the product -/

noncomputable def diamondOddChannelPhaseSSSS
    {n a b c d : Nat} [NeZero n]
    (rows : DiamondOddChannelProduct n a b c d) : F :=
  diamondOddScalarQ (rows .ssss)

noncomputable def diamondOddChannelPhaseSSST
    {n a b c d : Nat} [NeZero n]
    (rows : DiamondOddChannelProduct n a b c d) : F :=
  ∑ wt : DiamondOddAxisTail n d,
    cubeDot ((rows .ssst).1 wt).1
      (cubeDiffI
        (diamondOddAxisTailJ (CyclicCube n)
          (fun wt' => ((rows .ssst).1 wt').2) wt))

noncomputable def diamondOddChannelPhaseSSTS
    {n a b c d : Nat} [NeZero n]
    (rows : DiamondOddChannelProduct n a b c d) : F :=
  ∑ zt : DiamondOddAxisTail n c,
    cubeDot ((rows .ssts) zt).1
      (cubeDiffI
          (diamondOddAxisTailJ (CyclicCube n)
            (fun zt' => ((rows .ssts) zt').2.1) zt) +
        cubeDiffK
          (diamondOddAxisTailJ (CyclicCube n)
            (fun zt' => ((rows .ssts) zt').2.2) zt))

noncomputable def diamondOddChannelPhaseSSTT
    {n a b c d : Nat} [NeZero n]
    (rows : DiamondOddChannelProduct n a b c d) : F :=
  ∑ zt : DiamondOddAxisTail n c,
    ∑ wt : DiamondOddAxisTail n d,
      cubeDot ((rows .sstt) zt wt).1
        (cubeDiffI
          (diamondOddTensorTailJ
            (zeroVec : PVec n c) (zeroVec : PVec n d)
            (fun zt' wt' => ((rows .sstt) zt' wt').2) zt wt))

noncomputable def diamondOddChannelPhaseSTSS
    {n a b c d : Nat} [NeZero n]
    (rows : DiamondOddChannelProduct n a b c d) : F :=
  ∑ yt : DiamondOddAxisTail n b,
    cubeDot ((rows .stss).1 yt).1
      (cubeDiffK
        (diamondOddAxisTailJ (CyclicCube n)
          (fun yt' => ((rows .stss).1 yt').2) yt))

noncomputable def diamondOddChannelPhaseSTTS
    {n a b c d : Nat} [NeZero n]
    (rows : DiamondOddChannelProduct n a b c d) : F :=
  ∑ yt : DiamondOddAxisTail n b,
    ∑ zt : DiamondOddAxisTail n c,
      cubeDot ((rows .stts) yt zt).1
        (cubeDiffK
          (diamondOddTensorTailJ
            (zeroVec : PVec n b) (zeroVec : PVec n c)
            (fun yt' zt' => ((rows .stts) yt' zt').2) yt zt))

noncomputable def diamondOddChannelProductQ
    {n a b c d : Nat} [NeZero n]
    (rows : DiamondOddChannelProduct n a b c d) : F :=
  diamondOddChannelPhaseSSSS rows +
    diamondOddChannelPhaseSSST rows +
    diamondOddChannelPhaseSSTS rows +
    diamondOddChannelPhaseSSTT rows +
    diamondOddChannelPhaseSTSS rows +
    diamondOddChannelPhaseSTTS rows

theorem diamondOddPointedQ_eq_channelProductQ
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn) :
    diamondOddPointedQ x =
      diamondOddChannelProductQ
        (diamondOddChannelProductEquiv hn x) :=
  rfl

noncomputable def diamondOddChannelReducedQ
    {n a b c d : Nat} [NeZero n]
    (rows : DiamondOddChannelProduct n a b c d) : F :=
  diamondOddChannelPhaseSSSS rows +
    diamondOddChannelPhaseSSTS rows +
    diamondOddChannelPhaseSSTT rows +
    diamondOddChannelPhaseSTTS rows

theorem diamondOddPointedQ_eq_channelReducedQ
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn) :
    diamondOddPointedQ x =
      diamondOddChannelReducedQ
        (diamondOddChannelProductEquiv hn x) := by
  rw [diamondOddPointedQ_apply, diamondOddPointedAmbientQ_apply,
    diamondOddPointedPhaseSSST_eq_zero x,
    diamondOddPointedPhaseSTSS_eq_zero x]
  simp only [add_zero]
  rfl

end

end Core4loop.SquareDiagonal.DirectWitt
