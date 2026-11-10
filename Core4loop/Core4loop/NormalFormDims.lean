import Core4loop.Gauss.DeltaAfterA

namespace Core4loop

lemma finrank_AFun4 {n b c d : ℕ} [NeZero n] :
    Module.finrank F (AFun4 n b c d) = n ^ (b + c + d) := by
  calc
    Module.finrank F (AFun4 n b c d)
        = Fintype.card (YVec n b × ZVec n c × WVec n d) := by
            rw [← Module.finrank_fintype_fun_eq_card (R := F)
              (η := YVec n b × ZVec n c × WVec n d)]
            exact LinearEquiv.finrank_eq
              { toFun := fun A u => A u.1 u.2.1 u.2.2
                invFun := fun f y z w => f (y, z, w)
                map_add' := by intro A A'; rfl
                map_smul' := by intro r A; rfl
                left_inv := by intro A; funext y z w; rfl
                right_inv := by intro f; funext u; rcases u with ⟨y, z, w⟩; rfl }
    _ = n ^ (b + c + d) := card_vec3 n b c d

lemma finrank_BFun4 {n a c d : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F (BFun4 n a c d) = n ^ (a + c + d) := by
  calc
    Module.finrank F (BFun4 n a c d)
        = Fintype.card (PVec n a × I n × ZVec n c × WVec n d) := by
            rw [← Module.finrank_fintype_fun_eq_card (R := F)
              (η := PVec n a × I n × ZVec n c × WVec n d)]
            exact LinearEquiv.finrank_eq
              { toFun := fun B u => B u.1 u.2.1 u.2.2.1 u.2.2.2
                invFun := fun f p sy z w => f (p, sy, z, w)
                map_add' := by intro B B'; rfl
                map_smul' := by intro r B; rfl
                left_inv := by intro B; funext p sy z w; rfl
                right_inv := by intro f; funext u; rcases u with ⟨p, sy, z, w⟩; rfl }
    _ = n ^ (a + c + d) := card_BIndex4 ha

lemma finrank_CFun4 {n a b d : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F (CFun4 n a b d) = n ^ (a + b + d) := by
  calc
    Module.finrank F (CFun4 n a b d)
        = Fintype.card (PVec n a × YVec n b × I n × WVec n d) := by
            rw [← Module.finrank_fintype_fun_eq_card (R := F)
              (η := PVec n a × YVec n b × I n × WVec n d)]
            exact LinearEquiv.finrank_eq
              { toFun := fun C u => C u.1 u.2.1 u.2.2.1 u.2.2.2
                invFun := fun f p y sz w => f (p, y, sz, w)
                map_add' := by intro C C'; rfl
                map_smul' := by intro r C; rfl
                left_inv := by intro C; funext p y sz w; rfl
                right_inv := by intro f; funext u; rcases u with ⟨p, y, sz, w⟩; rfl }
    _ = n ^ (a + b + d) := card_CIndex4 ha

lemma finrank_WFun4 {n a b c : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F (WFun4 n a b c) = n ^ (a + b + c) := by
  calc
    Module.finrank F (WFun4 n a b c)
        = Fintype.card (PVec n a × YVec n b × ZVec n c × I n) := by
            rw [← Module.finrank_fintype_fun_eq_card (R := F)
              (η := PVec n a × YVec n b × ZVec n c × I n)]
            exact LinearEquiv.finrank_eq
              { toFun := fun W u => W u.1 u.2.1 u.2.2.1 u.2.2.2
                invFun := fun f p y z sw => f (p, y, z, sw)
                map_add' := by intro W W'; rfl
                map_smul' := by intro r W; rfl
                left_inv := by intro W; funext p y z sw; rfl
                right_inv := by intro f; funext u; rcases u with ⟨p, y, z, sw⟩; rfl }
    _ = n ^ (a + b + c) := card_WIndex4 ha

end Core4loop
