import Mathlib.Order.Lattice
import Mathlib.Order.Sublattice
import Mathlib.Data.Fintype.Order
import Mathlib.Combinatorics.Catalan


universe u v

-- Given a lattice (P, ≤),
-- a transfer system on (P,≤) is a sublattice (P,◁) that satisfies
-- 1) refinement: ∀ a, b ∈ P, if a ◁ b, then a ≤ b
-- 2) restrict: ∀ a, b, c ∈ P, if a ◁ b and c ≤ b, then a ∧ c → c
-- Two transfer systems on (P,≤) are equal if they have the same poset structure (I think this is what @[ext] does).
-- QUESTION: are transfer systems sublattices or just sub-posets.
@[ext]
structure TransferSystem (P : Type u) [base_struct: Lattice P] where
  carrier : Set P
  poset_struct : PartialOrder carrier
  refine: ∀ a b : carrier, poset_struct.le a b → base_struct.le a b
  restrict: ∀ a b c: carrier, poset_struct.le a b ∧ base_struct.le c b → base_struct.le (base_struct.inf a c) c
variable (Q : Type u) [Lattice Q]
#check TransferSystem.ext

-- Trivial example showing two tranfer systems are the same when they have the same carrier set and the same poset structure (?)
example (S T: TransferSystem Q) (h₂ : HEq S.poset_struct T.poset_struct): S = T := by
  ext x
  . sorry
  . exact h₂


-- Trivial example of a transfer system (the lattice is itself a transfer system)
def totalOrder : TransferSystem (P:= (Fin 6)) where
  carrier := Set.univ (α := Fin 6)
  poset_struct := inferInstance -- I think this is the poset structure with total complete order
  refine := by
    intro a b h
    exact h
  restrict := by
    intro a b c h
    exact inf_le_right

-- Want to get a transfer system with nontrivial poset strcutre.
def nontrivial : TransferSystem (P:= (Fin 6)) where
  carrier := Set.univ (α := Fin 6)
  poset_struct := sorry
  refine := sorry
  restrict := sorry

-- I think this is the set of all transfer systems on [0,...,n].
def setOfTransferSystems (n:ℕ) := { T:TransferSystem (P:= Fin n) // true}
#check setOfTransferSystems (5:ℕ)

-- Main theorem
-- theorem: cardinality.(setOfTransferSystems n) = catalan 5± 1
