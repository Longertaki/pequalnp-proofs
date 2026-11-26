import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23264 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2213807 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 8]⟩], 11⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
