import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21952 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33687 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 13]⟩], 14⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
