import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22012 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18207 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
