import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22181 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17038 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [11, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 16]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
