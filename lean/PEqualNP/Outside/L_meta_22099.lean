import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22099 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17208 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [14, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
