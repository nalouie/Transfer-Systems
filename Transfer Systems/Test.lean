import Mathlib.Order.Lattice
import Mathlib.Order.Sublattice

universe u v

-- Given a lattice (P, ≤),
-- a transfer system on (P,≤) is a partial order (P,◁) that satisfies
-- 1) refinement: ∀ a, b ∈ P, if a ◁ b, then a ≤ b
-- 2) restrict: ∀ a, b, c ∈ P, if a ◁ b and c ≤ b, then a ∧ c → c
structure TransferSystem (P : Type u) [base_struct: Lattice P] where
  carrier : Set P
  poset_struct : PartialOrder carrier
  refine: ∀ a b : carrier, poset_struct.le a b → base_struct.le a b
  restrict: ∀ a b c: carrier, poset_struct.le a b ∧ base_struct.le c b → base_struct.le (base_struct.inf a c) c
