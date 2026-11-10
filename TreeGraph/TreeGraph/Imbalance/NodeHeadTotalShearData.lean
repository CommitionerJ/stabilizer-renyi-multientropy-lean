import TreeGraph.Imbalance.NodeHeadTotalPotential

namespace TreeGraph
namespace Imbalance

noncomputable def rootDomainTotalDiag
    (n : Nat) [NeZero n] (C : RTree)
    (rd : RootFieldDomainClean n C) : Rep n :=
  copenTotalDiag n C ((rootFieldDomainCleanEquivCopen n C) rd)

noncomputable def rootDomainTotalDiagWithBridge
    (n : Nat) [NeZero n] (C : RTree)
    (B : RootFieldCleanCopenBridge n C)
    (rd : RootFieldDomainClean n C) : Rep n :=
  copenTotalDiag n C (B.domEquiv rd)

theorem rootFieldCleanCopenBridge_linearEquiv_apply
    (n : Nat) [NeZero n] (C : RTree)
    (B : RootFieldCleanCopenBridge n C)
    (root : RootFieldAssignmentClean n C)
    (y : Copen n C) :
    B.linearEquiv root y = root (B.domEquiv.symm y) := by
  unfold RootFieldCleanCopenBridge.linearEquiv
    rootFieldCleanLinearEquivBoundaryOfEquiv
  simp [precomposeLinearEquiv]

theorem headChildIndex_root_add_sub
    (n a : Nat) [NeZero n] (rest : List RTree)
    (idx : HeadChildIndex n a rest) (δ : Rep n) :
    ((headChildIndexParentRoot idx, headChildIndexTail idx,
        headChildIndexRootDiag idx + δ - δ) :
        HeadChildIndex n a rest) = idx := by
  rcases idx with ⟨q, tail, s⟩
  simp [headChildIndexParentRoot, headChildIndexTail,
    headChildIndexRootDiag]

theorem headChildIndex_root_sub_add
    (n a : Nat) [NeZero n] (rest : List RTree)
    (idx : HeadChildIndex n a rest) (δ : Rep n) :
    ((headChildIndexParentRoot idx, headChildIndexTail idx,
        headChildIndexRootDiag idx - δ + δ) :
        HeadChildIndex n a rest) = idx := by
  rcases idx with ⟨q, tail, s⟩
  simp [headChildIndexParentRoot, headChildIndexTail,
    headChildIndexRootDiag]

noncomputable def headTotalShearData
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest) :
    HeadChildOpenData n a C rest :=
  fun idx =>
    let q := headChildIndexParentRoot idx
    let tail := headChildIndexTail idx
    let α := headChildIndexRootDiag idx
    ( fun y =>
        (data (q, tail, α - rootDomainTotalDiag n C y)).1 y,
      { nodeField := fun v dom =>
          ((data (q, tail,
            α - nonRootDomainTotalDiag n C v dom)).2).nodeField v dom })

noncomputable def headTotalUnshearData
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest) :
    HeadChildOpenData n a C rest :=
  fun idx =>
    let q := headChildIndexParentRoot idx
    let tail := headChildIndexTail idx
    let α := headChildIndexRootDiag idx
    ( fun y =>
        (data (q, tail, α + rootDomainTotalDiag n C y)).1 y,
      { nodeField := fun v dom =>
          ((data (q, tail,
            α + nonRootDomainTotalDiag n C v dom)).2).nodeField v dom })

@[simp] theorem headTotalShearData_root_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest) (y : RootFieldDomainClean n C) :
    ((headTotalShearData n a C rest data idx).1) y =
      (data (headChildIndexParentRoot idx, headChildIndexTail idx,
        headChildIndexRootDiag idx - rootDomainTotalDiag n C y)).1 y := by
  rfl

@[simp] theorem headTotalShearData_node_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C) (dom : NonRootFieldDomainClean n C v) :
    ((headTotalShearData n a C rest data idx).2).nodeField v dom =
      (data (headChildIndexParentRoot idx, headChildIndexTail idx,
        headChildIndexRootDiag idx -
          nonRootDomainTotalDiag n C v dom)).2.nodeField v dom := by
  rfl

@[simp] theorem headTotalUnshearData_root_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest) (y : RootFieldDomainClean n C) :
    ((headTotalUnshearData n a C rest data idx).1) y =
      (data (headChildIndexParentRoot idx, headChildIndexTail idx,
        headChildIndexRootDiag idx + rootDomainTotalDiag n C y)).1 y := by
  rfl

@[simp] theorem headTotalUnshearData_node_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C) (dom : NonRootFieldDomainClean n C v) :
    ((headTotalUnshearData n a C rest data idx).2).nodeField v dom =
      (data (headChildIndexParentRoot idx, headChildIndexTail idx,
        headChildIndexRootDiag idx +
          nonRootDomainTotalDiag n C v dom)).2.nodeField v dom := by
  rfl

theorem headTotalUnshearData_shear
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest) :
    headTotalUnshearData n a C rest
        (headTotalShearData n a C rest data) = data := by
  funext idx
  apply Prod.ext
  · funext y
    rw [headTotalUnshearData_root_apply, headTotalShearData_root_apply]
    exact congrArg (fun i => (data i).1 y)
      (headChildIndex_root_add_sub n a rest idx
        (rootDomainTotalDiag n C y))
  · change OpenNormalAssignmentClean.mk _ = OpenNormalAssignmentClean.mk _
    congr
    funext v dom
    change
      ((headTotalShearData n a C rest data
        (headChildIndexParentRoot idx, headChildIndexTail idx,
          headChildIndexRootDiag idx +
            nonRootDomainTotalDiag n C v dom)).2).nodeField v dom =
        (data idx).2.nodeField v dom
    rw [headTotalShearData_node_apply]
    exact congrArg (fun i => (data i).2.nodeField v dom)
      (headChildIndex_root_add_sub n a rest idx
        (nonRootDomainTotalDiag n C v dom))

theorem headTotalShearData_unshear
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest) :
    headTotalShearData n a C rest
        (headTotalUnshearData n a C rest data) = data := by
  funext idx
  apply Prod.ext
  · funext y
    rw [headTotalShearData_root_apply, headTotalUnshearData_root_apply]
    exact congrArg (fun i => (data i).1 y)
      (headChildIndex_root_sub_add n a rest idx
        (rootDomainTotalDiag n C y))
  · change OpenNormalAssignmentClean.mk _ = OpenNormalAssignmentClean.mk _
    congr
    funext v dom
    change
      ((headTotalUnshearData n a C rest data
        (headChildIndexParentRoot idx, headChildIndexTail idx,
          headChildIndexRootDiag idx -
            nonRootDomainTotalDiag n C v dom)).2).nodeField v dom =
        (data idx).2.nodeField v dom
    rw [headTotalUnshearData_node_apply]
    exact congrArg (fun i => (data i).2.nodeField v dom)
      (headChildIndex_root_sub_add n a rest idx
        (nonRootDomainTotalDiag n C v dom))

noncomputable def headTotalShearDataEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) :
    HeadChildOpenData n a C rest ≃
      HeadChildOpenData n a C rest where
  toFun := headTotalShearData n a C rest
  invFun := headTotalUnshearData n a C rest
  left_inv := headTotalUnshearData_shear n a C rest
  right_inv := headTotalShearData_unshear n a C rest

@[simp] theorem headTotalShearDataEquiv_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest) :
    headTotalShearDataEquiv n a C rest data =
      headTotalShearData n a C rest data := by
  rfl

@[simp] theorem headTotalShearDataEquiv_symm_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest) :
    (headTotalShearDataEquiv n a C rest).symm data =
      headTotalUnshearData n a C rest data := by
  rfl

noncomputable def headTotalShearDataWithBridge
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest) :
    HeadChildOpenData n a C rest :=
  fun idx =>
    let q := headChildIndexParentRoot idx
    let tail := headChildIndexTail idx
    let α := headChildIndexRootDiag idx
    ( fun y =>
        (data (q, tail, α - rootDomainTotalDiagWithBridge n C B y)).1 y,
      { nodeField := fun v dom =>
          ((data (q, tail,
            α - nonRootDomainTotalDiag n C v dom)).2).nodeField v dom })

noncomputable def headTotalUnshearDataWithBridge
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest) :
    HeadChildOpenData n a C rest :=
  fun idx =>
    let q := headChildIndexParentRoot idx
    let tail := headChildIndexTail idx
    let α := headChildIndexRootDiag idx
    ( fun y =>
        (data (q, tail, α + rootDomainTotalDiagWithBridge n C B y)).1 y,
      { nodeField := fun v dom =>
          ((data (q, tail,
            α + nonRootDomainTotalDiag n C v dom)).2).nodeField v dom })

@[simp] theorem headTotalShearDataWithBridge_root_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest)
    (y : RootFieldDomainClean n C) :
    ((headTotalShearDataWithBridge n a C rest B data) idx).1 y =
      (data
        (headChildIndexParentRoot idx,
          headChildIndexTail idx,
          headChildIndexRootDiag idx -
            rootDomainTotalDiagWithBridge n C B y)).1 y := by
  rfl

@[simp] theorem headTotalShearDataWithBridge_node_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    ((headTotalShearDataWithBridge n a C rest B data) idx).2.nodeField v dom =
      ((data
        (headChildIndexParentRoot idx,
          headChildIndexTail idx,
          headChildIndexRootDiag idx -
            nonRootDomainTotalDiag n C v dom)).2).nodeField v dom := by
  rfl

theorem headTotalShearDataWithBridge_boundary_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest)
    (y : Copen n C) :
    B.linearEquiv
        ((headTotalShearDataWithBridge n a C rest B data) idx).1 y =
      B.linearEquiv
        (data
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx - copenTotalDiag n C y)).1 y := by
  rw [rootFieldCleanCopenBridge_linearEquiv_apply]
  rw [rootFieldCleanCopenBridge_linearEquiv_apply]
  simp [rootDomainTotalDiagWithBridge]

theorem headTotalShearDataWithBridge_boundary_apply_total
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (q : Block n (a - 1)) (tail : CoordsList n rest)
    (s : Rep n) (y : Copen n C) :
    B.linearEquiv
        ((headTotalShearDataWithBridge n a C rest B data)
          (q, tail, s + copenTotalDiag n C y)).1 y =
      B.linearEquiv (data (q, tail, s)).1 y := by
  rw [headTotalShearDataWithBridge_boundary_apply]
  have hidx :
      ((q, tail, s + copenTotalDiag n C y -
          copenTotalDiag n C y) : HeadChildIndex n a rest) =
        (q, tail, s) := by
    simp
  change
    B.linearEquiv
        (data
          (((q, tail, s + copenTotalDiag n C y -
            copenTotalDiag n C y) : HeadChildIndex n a rest))).1 y =
      B.linearEquiv (data (q, tail, s)).1 y
  rw [hidx]

theorem headTotalShearDataWithBridge_node_apply_total
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (q : Block n (a - 1)) (tail : CoordsList n rest)
    (s : Rep n)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    ((headTotalShearDataWithBridge n a C rest B data)
        (q, tail, s + nonRootDomainTotalDiag n C v dom)).2.nodeField v dom =
      (data (q, tail, s)).2.nodeField v dom := by
  rw [headTotalShearDataWithBridge_node_apply]
  have hidx :
      ((q, tail, s + nonRootDomainTotalDiag n C v dom -
          nonRootDomainTotalDiag n C v dom) : HeadChildIndex n a rest) =
        (q, tail, s) := by
    simp
  change
    (data
        (((q, tail, s + nonRootDomainTotalDiag n C v dom -
          nonRootDomainTotalDiag n C v dom) :
          HeadChildIndex n a rest))).2.nodeField v dom =
      (data (q, tail, s)).2.nodeField v dom
  rw [hidx]

@[simp] theorem headTotalUnshearDataWithBridge_root_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest)
    (y : RootFieldDomainClean n C) :
    ((headTotalUnshearDataWithBridge n a C rest B data) idx).1 y =
      (data
        (headChildIndexParentRoot idx,
          headChildIndexTail idx,
          headChildIndexRootDiag idx +
            rootDomainTotalDiagWithBridge n C B y)).1 y := by
  rfl

@[simp] theorem headTotalUnshearDataWithBridge_node_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    ((headTotalUnshearDataWithBridge n a C rest B data) idx).2.nodeField v dom =
      ((data
        (headChildIndexParentRoot idx,
          headChildIndexTail idx,
          headChildIndexRootDiag idx +
            nonRootDomainTotalDiag n C v dom)).2).nodeField v dom := by
  rfl

theorem headTotalUnshearDataWithBridge_boundary_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest)
    (y : Copen n C) :
    B.linearEquiv
        ((headTotalUnshearDataWithBridge n a C rest B data) idx).1 y =
      B.linearEquiv
        (data
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx + copenTotalDiag n C y)).1 y := by
  rw [rootFieldCleanCopenBridge_linearEquiv_apply]
  rw [rootFieldCleanCopenBridge_linearEquiv_apply]
  simp [rootDomainTotalDiagWithBridge]

theorem headTotalUnshearDataWithBridge_shear
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest) :
    headTotalUnshearDataWithBridge n a C rest B
        (headTotalShearDataWithBridge n a C rest B data) =
      data := by
  funext idx
  apply Prod.ext
  · funext y
    change
      (data
        (((headChildIndexParentRoot idx, headChildIndexTail idx,
            headChildIndexRootDiag idx +
              rootDomainTotalDiagWithBridge n C B y -
              rootDomainTotalDiagWithBridge n C B y) :
            HeadChildIndex n a rest))).1 y =
        (data idx).1 y
    rw [headChildIndex_root_add_sub]
  · change OpenNormalAssignmentClean.mk _ = OpenNormalAssignmentClean.mk _
    congr
    funext v dom
    change
      (data
        (((headChildIndexParentRoot idx, headChildIndexTail idx,
            headChildIndexRootDiag idx +
              nonRootDomainTotalDiag n C v dom -
              nonRootDomainTotalDiag n C v dom) :
            HeadChildIndex n a rest))).2.nodeField v dom =
        (data idx).2.nodeField v dom
    rw [headChildIndex_root_add_sub]

theorem headTotalShearDataWithBridge_unshear
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest) :
    headTotalShearDataWithBridge n a C rest B
        (headTotalUnshearDataWithBridge n a C rest B data) =
      data := by
  funext idx
  apply Prod.ext
  · funext y
    change
      (data
        (((headChildIndexParentRoot idx, headChildIndexTail idx,
            headChildIndexRootDiag idx -
              rootDomainTotalDiagWithBridge n C B y +
              rootDomainTotalDiagWithBridge n C B y) :
            HeadChildIndex n a rest))).1 y =
        (data idx).1 y
    rw [headChildIndex_root_sub_add]
  · change OpenNormalAssignmentClean.mk _ = OpenNormalAssignmentClean.mk _
    congr
    funext v dom
    change
      (data
        (((headChildIndexParentRoot idx, headChildIndexTail idx,
            headChildIndexRootDiag idx -
              nonRootDomainTotalDiag n C v dom +
              nonRootDomainTotalDiag n C v dom) :
            HeadChildIndex n a rest))).2.nodeField v dom =
        (data idx).2.nodeField v dom
    rw [headChildIndex_root_sub_add]

noncomputable def headTotalShearDataWithBridgeEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C) :
    HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest where
  toFun := headTotalShearDataWithBridge n a C rest B
  invFun := headTotalUnshearDataWithBridge n a C rest B
  left_inv := headTotalUnshearDataWithBridge_shear n a C rest B
  right_inv := headTotalShearDataWithBridge_unshear n a C rest B

@[simp] theorem headTotalShearDataWithBridgeEquiv_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest) :
    headTotalShearDataWithBridgeEquiv n a C rest B data =
      headTotalShearDataWithBridge n a C rest B data := by
  rfl

@[simp] theorem headTotalShearDataWithBridgeEquiv_symm_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest) :
    (headTotalShearDataWithBridgeEquiv n a C rest B).symm data =
      headTotalUnshearDataWithBridge n a C rest B data := by
  rfl

end Imbalance
end TreeGraph
