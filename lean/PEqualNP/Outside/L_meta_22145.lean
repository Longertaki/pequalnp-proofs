import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22145 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33973 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 10]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
