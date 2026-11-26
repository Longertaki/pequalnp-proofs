import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22180 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17036 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 16]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
