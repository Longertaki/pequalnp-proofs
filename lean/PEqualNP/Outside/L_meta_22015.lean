import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22015 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18237 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
