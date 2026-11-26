import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22144 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33972 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 13]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
