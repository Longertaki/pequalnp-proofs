import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21581 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13277 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
