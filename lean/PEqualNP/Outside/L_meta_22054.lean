import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22054 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33716 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
