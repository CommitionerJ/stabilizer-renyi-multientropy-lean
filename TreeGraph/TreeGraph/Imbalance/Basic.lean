import TreeGraph.Basic
import TreeGraph.RTree
import TreeGraph.Poly

namespace TreeGraph
namespace Imbalance

abbrev Rep (n : Nat) := ZMod n

abbrev Block (n a : Nat) := Fin a → Rep n

abbrev Field (C : Type) := C → F2

def chi (b : F2) : ℤ :=
  bitSign b

@[simp] theorem chi_zero : chi 0 = 1 := by
  simp [chi]

@[simp] theorem chi_one : chi 1 = -1 := by
  simp [chi]

theorem chi_add (x y : F2) :
    chi (x + y) = chi x * chi y := by
  simpa [chi] using bitSign_add x y

@[simp] theorem chi_add_one (b : F2) :
    chi (b + 1) = -chi b := by
  fin_cases b <;> decide

theorem card_Block (n a : Nat) [NeZero n] :
    Fintype.card (Block n a) = n ^ a := by
  classical
  simp [Block, Rep, ZMod.card]

theorem card_eq_pow_finrank
    (V : Type) [AddCommGroup V] [Module F2 V]
    [Fintype V] [FiniteDimensional F2 V] :
    Fintype.card V = 2 ^ Module.finrank F2 V := by
  calc
    Fintype.card V = Nat.card V := Fintype.card_eq_nat_card
    _ = Nat.card F2 ^ Module.finrank F2 V :=
        Module.natCard_eq_pow_finrank (K := F2) (V := V)
    _ = 2 ^ Module.finrank F2 V := by
        simp [F2]

theorem submodule_card_eq_pow_finrank
    {V : Type} [AddCommGroup V] [Module F2 V]
    (K : Submodule F2 V) [Fintype K] [FiniteDimensional F2 K] :
    Fintype.card K = 2 ^ Module.finrank F2 K :=
  card_eq_pow_finrank K

end Imbalance
end TreeGraph
