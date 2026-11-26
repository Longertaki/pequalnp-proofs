import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21469 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8858 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
