import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21480 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (30 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 0]⟩], 8⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp
