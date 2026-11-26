import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22009 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17309 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 8]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
