import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21613 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4187 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [11, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩], 13⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
