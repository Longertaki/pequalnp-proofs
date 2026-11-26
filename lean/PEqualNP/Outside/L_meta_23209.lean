import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23209 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34074 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩], 11⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
